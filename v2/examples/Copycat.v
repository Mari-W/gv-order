(** * A derived forwarder at independent points (design B of 2026-11-22)

      fwd o1 o2 = let (v, o1) = recv o1 in let o2 = send ⟨v, o2⟩ in
                  let (w, o2) = recv o2 in let o1 = send ⟨w, o1⟩ in
                  close o1; close o2

    The forwarder holds o1 : S@x and o2 : S‾@y for S = ?∗.!∗.Close, at
    two independent points. Link fuses at x and x‾ and stays as it is.
    The copycat alternates, and every action asks the acting point below
    the head of the other end, the partner point of that end. The facts
    are those the session type generates.

      recv o1 at x     while o2 sits at y      x ≺ y‾
      send o2 at y     while o1 sits at x⁺     y ≺ (x⁺)‾
      recv o2 at y⁺    while o1 sits at x⁺     y⁺ ≺ (x⁺)‾
      send o1 at x⁺    while o2 sits at y⁺⁺    x⁺ ≺ (y⁺⁺)‾
      close o1 at x⁺⁺  while o2 sits at y⁺⁺    x⁺⁺ ≺ (y⁺⁺)‾

    No rule changes. The results:

    - [fwd_dftyped], [fwd_term]: the copycat types under the five facts,
      and as a thread by P-Term over the world [W_f] that holds them.
    - [fwd_expand]: identity expansion. A process that holds o1‾ at x‾
      types with the forwarder put behind it, then holding o2 at y.
    - [fwd_config_deadlock_free]: partner ∥ fwd ∥ partner is typed and
      deadlock free by the fundamental theorem.
    - [ring_rejected_full], [ring_rejected]: fwd(o1, o2) ∥ fwd(o2‾, o1‾)
      types at no world, no bound and no type, in the full judgment and
      with hiding. The facts give x ≺ y‾ ≺ x.
    - [fwdh_term], [fwdh_config_deadlock_free]: a higher-order payload.
      The forwarder η-expands the received end through a channel created
      at the field y·0.
    - [fb_dftyped], [fwdp_term], [fwdp_expand], [fwdp_sem]: the schema for
      every first-order protocol (data messages and Close), by induction
      on the protocol, with identity expansion and semantic soundness. *)

From GV Require Export examples.SemBranch examples.Tools2.
From GV Require Import static.Inversion cost.Exact.

(** ** The session type and the program *)

Definition S1 : sty := SSeq (SRcv 0 TUnit) (SSeq (SSnd 0 TUnit) SEnd).

Lemma S1_dual : dual S1 = SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) SEnd).
Proof. reflexivity. Qed.

Lemma S1_contr : scontr S1.
Proof. contr_tac. Qed.

Lemma S1_dual_contr : scontr (dual S1).
Proof. contr_tac. Qed.

Definition fwd_t (o1 o2 : cend) : expr :=
  LetP (ERecv (Chan o1))
    (ELet (ESend (Pair (Var 1) (Chan o2)))
      (LetP (ERecv (Var 0))
        (ELet (ESend (Pair (Var 1) (Var 3)))
          (LetU (EClose (Var 0)) (EClose (Var 1)))))).

(** The facts of the alternation at the points x and y. *)
Definition fwd_facts (W : sworld) (Γ : hctx) (x y : point) : Prop :=
  slt W Γ x (y‾) ∧ slt W Γ y (x⁺‾) ∧ slt W Γ (y⁺) (x⁺‾) ∧
  slt W Γ (x⁺) (y⁺⁺‾) ∧ slt W Γ (x⁺⁺) (y⁺⁺‾).

Lemma tenv_heads_one o e : tenv_heads {[o := e]} = {[(te_pt e)‾]}.
Proof. unfold tenv_heads. rewrite map_to_list_singleton. simpl. set_solver. Qed.

Ltac ff_tac := match goal with H : fwd_facts _ _ _ _ |- _ => destruct H as (?&?&?&?&?); assumption end.

Section typing.
  Context (W : sworld) (Γ : hctx) (o1 o2 : cend) (x y : point).
  Context (Ho : o1 ≠ o2) (Hf : fwd_facts W Γ x y).

  Definition Θf : tenv := {[o1 := TE S1 x None None]} ∪ {[o2 := TE (dual S1) y None None]}.

  Lemma Θf_split : tsplit Θf {[o1 := TE S1 x None None]} {[o2 := TE (dual S1) y None None]}.
  Proof. split; [by apply map_disjoint_singleton_l_2; rewrite lookup_singleton_ne|reflexivity]. Qed.

  Lemma fwd_dftyped : dftyped W Θf Γ [] (∅, None) (fwd_t o1 o2) TUnit.
  Proof.
    unfold fwd_t.
    eapply d_letp; [apply Θf_split|apply lsplit_nil| |].
    { eapply d_recv with (S0 := S1) (x := x) (m := 0) (T := TUnit) (S := SSeq (SSnd 0 TUnit) SEnd);
        [reflexivity|exact I| |apply d_chan, spare_unl; spare_tac].
      apply ub_below_nil; [reflexivity|]. intros z Hz.
      rewrite tenv_heads_one in Hz. cbn in Hz. set_unfold in Hz. destruct Hz as [->|Hz]; [ff_tac|set_solver]. }
    eapply d_let with (Θ1 := {[o2 := TE (dual S1) y None None]}) (Θ2 := ∅);
      [split; [apply map_disjoint_empty_r|by rewrite map_union_empty]
      |lsplit_tac (ESend (Pair (Var 1) (Chan o2))) EUnit| |].
    { eapply d_send with (S0 := dual S1) (x := y) (m := 0) (T := TUnit) (S := SSeq (SRcv 0 TUnit) SEnd);
        [reflexivity|exact I|reflexivity|cbn; set_solver| |].
      - apply ub_below_nil; [reflexivity|]. intros z Hz.
        rewrite tenv_heads_empty in Hz. cbn in Hz. set_unfold in Hz.
        destruct Hz as [[]|[->|[]]]. ff_tac.
      - eapply d_pair with (Θ1 := ∅) (Θ2 := {[o2 := TE (dual S1) y None None]});
          [split; [apply map_disjoint_empty_l|by rewrite map_empty_union]
          |lsplit_tac (Var 1) (Chan o2)| |].
        + eapply d_var'; [reflexivity|]. spare_tac.
        + apply d_chan, spare_unl. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 0)) EUnit| |].
    { eapply d_recv with (S0 := SSeq (SRcv 0 TUnit) SEnd) (x := y⁺) (m := 0) (T := TUnit) (S := SEnd);
        [reflexivity|exact I| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [reflexivity|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. set_unfold in Hz.
      destruct Hz as [[]|[->|[]]]. ff_tac. }
    eapply d_let; [apply tsplit_empty|lsplit_tac (ESend (Pair (Var 1) (Var 3))) EUnit| |].
    { eapply d_send with (S0 := SSeq (SSnd 0 TUnit) SEnd) (x := x⁺) (m := 0) (T := TUnit) (S := SEnd);
        [reflexivity|exact I|reflexivity|cbn; set_solver| |].
      - apply ub_below_nil; [reflexivity|]. intros z Hz.
        rewrite tenv_heads_empty in Hz. cbn in Hz. set_unfold in Hz.
        destruct Hz as [[]|[->|[]]]. ff_tac.
      - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 1) (Var 3)| |].
        + eapply d_var'; [reflexivity|]. spare_tac.
        + eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 0)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := x⁺⁺); [reflexivity| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [reflexivity|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. set_unfold in Hz.
      destruct Hz as [[]|[->|[]]]. ff_tac. }
    eapply d_close with (S0 := SEnd) (x := y⁺⁺); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|spare_tac].
    Unshelve. all: exact None.
  Qed.
End typing.

(** ** The partners

    The partner of o1 sends, receives and closes at x‾. The partner of
    o2 receives, sends back and closes at y‾. Each holds one end and
    needs no fact. *)

Definition p1_t (o : cend) : expr :=
  ELet (ESend (Pair EUnit (Chan o))) (LetP (ERecv (Var 0)) (LetU (Var 1) (EClose (Var 0)))).

Definition p2_t (o : cend) : expr :=
  LetP (ERecv (Chan o)) (ELet (ESend (Pair (Var 1) (Var 0))) (EClose (Var 0))).

Lemma p1_dftyped W Γ o z : dftyped W {[o := TE (dual S1) z None None]} Γ [] (∅, None) (p1_t o) TUnit.
Proof.
  unfold p1_t.
  eapply d_let with (Θ1 := {[o := TE (dual S1) z None None]}) (Θ2 := ∅);
    [split; [apply map_disjoint_empty_r|by rewrite map_union_empty]|apply lsplit_nil| |].
  { eapply d_send with (S0 := dual S1) (x := z) (m := 0) (T := TUnit) (S := SSeq (SRcv 0 TUnit) SEnd);
      [reflexivity|exact I|reflexivity|cbn; set_solver| |].
    - apply ub_below_nil; [reflexivity|]. intros u Hu.
      rewrite tenv_heads_empty in Hu. cbn in Hu. set_solver.
    - eapply d_pair with (Θ1 := ∅) (Θ2 := {[o := TE (dual S1) z None None]});
        [split; [apply map_disjoint_empty_l|by rewrite map_empty_union]|apply lsplit_nil| |].
      + apply d_unit'. spare_tac.
      + apply d_chan, spare_unl. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 0)) EUnit| |].
  { eapply d_recv with (S0 := SSeq (SRcv 0 TUnit) SEnd) (x := z⁺) (m := 0) (T := TUnit) (S := SEnd);
      [reflexivity|exact I| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [reflexivity|]. intros u Hu.
    rewrite tenv_heads_empty in Hu. cbn in Hu. set_solver. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
  { eapply d_var'; [reflexivity|spare_tac]. }
  eapply d_close with (S0 := SEnd) (x := z⁺⁺); [reflexivity|apply ub_below_empty|].
  eapply d_var'; [reflexivity|spare_tac].
  Unshelve. all: exact None.
Qed.

Lemma p2_dftyped W Γ o z : dftyped W {[o := TE S1 z None None]} Γ [] (∅, None) (p2_t o) TUnit.
Proof.
  unfold p2_t.
  eapply d_letp with (Θ1 := {[o := TE S1 z None None]}) (Θ2 := ∅);
    [split; [apply map_disjoint_empty_r|by rewrite map_union_empty]|apply lsplit_nil| |].
  { eapply d_recv with (S0 := S1) (x := z) (m := 0) (T := TUnit) (S := SSeq (SSnd 0 TUnit) SEnd);
      [reflexivity|exact I| |apply d_chan, spare_unl; spare_tac].
    apply ub_below_nil; [reflexivity|]. intros u Hu.
    rewrite tenv_heads_empty in Hu. cbn in Hu. set_solver. }
  eapply d_let; [apply tsplit_empty|lsplit_tac (ESend (Pair (Var 1) (Var 0))) EUnit| |].
  { eapply d_send with (S0 := SSeq (SSnd 0 TUnit) SEnd) (x := z⁺) (m := 0) (T := TUnit) (S := SEnd);
      [reflexivity|exact I|reflexivity|cbn; set_solver| |].
    - apply ub_below_nil; [reflexivity|]. intros u Hu.
      rewrite tenv_heads_empty in Hu. cbn in Hu. set_solver.
    - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 1) (Var 0)| |].
      + eapply d_var'; [reflexivity|]. spare_tac.
      + eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_close with (S0 := SEnd) (x := z⁺⁺); [reflexivity|apply ub_below_empty|].
  eapply d_var'; [reflexivity|spare_tac].
  Unshelve. all: exact None.
Qed.

(** ** The forwarder's world

    x and y are the constant roots 0 and 1 of [px] and [py]. The world
    holds exactly the five facts. It is well-founded: the potential
    2·offset + (root + offset mod 2) grows along each fact and along both
    kinds of step, because the side that acts first alternates with the
    offset. *)

Definition fwd_fact (x y : point) (g : fact) : Prop :=
  g = FLt x (y‾) ∨ g = FLt y (x⁺‾) ∨ g = FLt (y⁺) (x⁺‾) ∨
  g = FLt (x⁺) (y⁺⁺‾) ∨ g = FLt (x⁺⁺) (y⁺⁺‾).

Definition W_f : sworld := SWorld ({[0]} ∪ {[1]}) (fwd_fact px py).

Lemma W_f_wf : sworld_wf W_f.
Proof.
  split; simpl. intros u v H.
  destruct H as [H|[H|[H|[H|H]]]]; injection H as Hu Hv; subst;
    split; eexists; (split; [reflexivity|set_solver]).
Qed.

Definition fpot (u : point) : nat := 2 * pt_off u + (rk u + pt_off u) mod 2.

Lemma fpot_off u v : rk u = rk v → pt_off u < pt_off v → fpot u < fpot v.
Proof.
  intros Hr Ho. unfold fpot. rewrite Hr.
  pose proof (Nat.mod_upper_bound (rk v + pt_off u) 2 ltac:(lia)). lia.
Qed.

Lemma W_f_step u v : swstep W_f u v → fpot u < fpot v.
Proof.
  intros Hs. destruct Hs as [u v H|u|u].
  - simpl in H. destruct H as [H|[H|[H|[H|H]]]]; injection H as -> ->;
      vm_compute; lia.
  - apply fpot_off; [by rewrite rk_shift|rewrite off_shift; lia].
  - apply fpot_off; [rewrite rk_shift, rk_dual; done|rewrite off_shift, off_dual; lia].
Qed.

Lemma W_f_lt u v : W_f ⊢ₛ u ≺ v → fpot u < fpot v.
Proof.
  intros H. induction H as [u v H|u v w H _ IH]; [by apply W_f_step|].
  apply W_f_step in H. lia.
Qed.

Lemma W_f_swf : swf W_f.
Proof.
  apply swf_iff.
  assert (∀ m u, fpot u = m → Acc (sw_lt W_f) u) as Hacc.
  { intros m. induction m as [m IH] using lt_wf_ind. intros u <-. constructor.
    intros v Hv. eapply IH; [apply W_f_lt, Hv|done]. }
  intros u. by apply (Hacc (fpot u)).
Qed.

Lemma W_f_ok : sworld_wf W_f ∧ swf W_f.
Proof. split; [apply W_f_wf|apply W_f_swf]. Qed.

Lemma W_f_facts : fwd_facts W_f hc_empty px py.
Proof.
  split_and!; apply sl_w, sw_lt_fact; simpl; unfold fwd_fact; tauto.
Qed.

(** ** The forwarder as a process *)

Definition o1 : cend := EPos "a".
Definition o2 : cend := EPos "b".

Lemma o1_o2 : o1 ≠ o2.
Proof. unfold o1, o2. congruence. Qed.

Definition Σf : senv := {[o1 := (S1, px)]} ∪ {[o2 := (dual S1, py)]}.

Lemma Θf_of : tenv_of None Σf ∪ ∅ = Θf o1 o2 px py.
Proof. rewrite map_union_empty. unfold tenv_of, Σf, Θf. by rewrite map_fmap_union, !map_fmap_singleton. Qed.

Lemma Θf_df : tenv_df (Θf o1 o2 px py) = Θf o1 o2 px py.
Proof. unfold tenv_df, Θf. by rewrite map_fmap_union, !map_fmap_singleton. Qed.

Lemma Σf_pfree : pfree Σf.
Proof.
  intros o Ho Hn. unfold Σf in Ho, Hn. rewrite dom_union_L, !dom_singleton_L in Ho, Hn.
  set_unfold in Ho; set_unfold in Hn. destruct Ho as [->| ->]; simpl in Hn; destruct Hn; discriminate.
Qed.

Lemma fwd_term : fptyped None W_f Σf (∅, {[+ fwd_t o1 o2 +]}) TUnit.
Proof.
  apply (fp_term None W_f Σf ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply Σf_pfree.
  - intros o e He. unfold Σf in He. apply lookup_union_Some_raw in He as [He|[_ He]];
      apply lookup_singleton_Some in He as [_ <-]; [apply S1_contr|apply S1_dual_contr].
  - set_solver.
  - change (fhalf None) with (None : fuel). rewrite Θf_of, <-Θf_df.
    exact (fwd_dftyped W_f hc_empty o1 o2 px py o1_o2 W_f_facts).
  - apply swf_ok_wok, W_f_ok.
Qed.

(** ** Identity expansion

    A process P that holds o1‾ : S‾@x‾ types after the forwarder is put
    between it and its partner. P ∥ fwd holds o2 : S‾@y instead, at the
    same type, and the partner of P now connects to o2‾ at y‾. The only
    condition on P's world W is that it does not know the root of y. The
    forwarder's facts then restrict to program order on the root of x,
    which every world has, so the cut of P-Connect is well-founded
    because W is. *)

Lemma po_name x y : po x y → pt_name x = pt_name y ∧ pt_off x < pt_off y.
Proof.
  induction 1 as [x y [->| ->]|x y z [->| ->] _ [IH1 IH2]];
    cbn [pt_shift pt_dual pt_name pt_off] in *; split; try done; lia.
Qed.

Lemma po_of_off x y : pt_name x = pt_name y → pt_off x < pt_off y → po x y.
Proof.
  destruct x as [n b k], y as [n' b' k']. simpl. intros <- Hk.
  assert (∀ j b0, po (MkPt n b k) (MkPt n b0 (k + S j))) as H.
  { intros j. induction j as [|j IH]; intros b0.
    - apply tc_once. destruct (decide (b0 = b)) as [->|Hne].
      + left. unfold pt_shift. simpl. done.
      + right. unfold pt_shift, pt_dual. simpl. destruct b, b0; done.
    - eapply tc_r; [apply (IH b0)|]. left. unfold pt_shift. simpl. f_equal. lia. }
  replace k' with (k + S (k' - k - 1)) by lia. apply H.
Qed.

Definition nm01 (u : point) : Prop := pt_name u = NConst 0 ∨ pt_name u = NConst 1.

Lemma rk_name u v : pt_name u = pt_name v → rk u = rk v.
Proof. intros H. unfold rk, pt_root. by rewrite H. Qed.

Lemma W_f_lt_inv u v : W_f ⊢ₛ u ≺ v → po u v ∨ (nm01 u ∧ nm01 v ∧ fpot u < fpot v).
Proof.
  assert (∀ u v, swstep W_f u v → po u v ∨ (nm01 u ∧ nm01 v ∧ fpot u < fpot v)) as Hs.
  { intros u' v' H. pose proof (W_f_step _ _ H) as Hp.
    destruct H as [u' v' H|u'|u'].
    - right. simpl in H. unfold nm01.
      destruct H as [H|[H|[H|[H|H]]]]; injection H as -> ->; vm_compute; tauto.
    - left. by apply tc_once; left.
    - left. by apply tc_once; right. }
  induction 1 as [u v H|u v w H _ IH]; [by apply Hs|].
  apply Hs in H. destruct H as [H|(Hu & Hv & H)], IH as [IH|(Hv' & Hw & IH)].
  - left. by eapply po_trans.
  - right. destruct (po_name _ _ H) as [Hn Ho]. split_and!; [unfold nm01; by rewrite Hn|done|].
    pose proof (fpot_off u v (rk_name _ _ Hn) Ho). lia.
  - right. destruct (po_name _ _ IH) as [Hn Ho]. split_and!; [done|unfold nm01; by rewrite <-Hn|].
    pose proof (fpot_off v w (rk_name _ _ Hn) Ho). lia.
  - right. split_and!; [done|done|lia].
Qed.

(** Between two points on the root of x, the forwarder's world holds
    only program order. *)
Lemma W_f_lt_root0 u v : W_f ⊢ₛ u ≺ v → pt_root u = NConst 0 → pt_root v = NConst 0 → po u v.
Proof.
  intros H Hu Hv. destruct (W_f_lt_inv _ _ H) as [Hp|(Hu' & Hv' & Hlt)]; [done|].
  assert (pt_name u = NConst 0) as Hu0.
  { destruct Hu' as [E|E]; [done|]. unfold pt_root in Hu. rewrite E in Hu. discriminate. }
  assert (pt_name v = NConst 0) as Hv0.
  { destruct Hv' as [E|E]; [done|]. unfold pt_root in Hv. rewrite E in Hv. discriminate. }
  apply po_of_off; [by rewrite Hu0, Hv0|].
  unfold fpot, rk, pt_root in Hlt. rewrite Hu0, Hv0 in Hlt. simpl in Hlt.
  destruct (decide (pt_off u < pt_off v)) as [?|Hge]; [done|].
  pose proof (Nat.mod_upper_bound (pt_off u) 2 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (pt_off v) 2 ltac:(lia)). exfalso.
  assert (pt_off u = pt_off v) as E by lia. rewrite E in Hlt. lia.
Qed.

Lemma cut_W_f_wok N W : wok N W → 1 ∉ sw_consts W →
  wok N (swrestrict W (swshared W W_f) ⊔ swrestrict W_f (swshared W W_f)).
Proof.
  intros HW H1. eapply (wok_sub N); [|exact HW].
  assert (∀ u v, swstep (swrestrict W (swshared W W_f) ⊔ swrestrict W_f (swshared W W_f)) u v →
            W ⊢ₛ u ≺ v) as Hs.
  { intros u v Hs. apply swstep_join_inv in Hs as [Hs|Hs].
    - apply (swrestrict_lt W (swshared W W_f)). by apply tc_once.
    - destruct Hs as [u v (Hlt & (a & Ha & Has) & (b & Hb & Hbs))|u|u];
        [|apply sw_lt_po|apply sw_lt_dpo].
      apply po_slt, W_f_lt_root0; [done| |].
      + unfold swshared in Has. simpl in Has. assert (a = 0) as -> by set_solver. done.
      + unfold swshared in Hbs. simpl in Hbs. assert (b = 0) as -> by set_solver. done. }
  intros u v H. induction H as [u v H|u v w H _ IH]; [by apply Hs|].
  eapply sw_lt_trans; [by apply Hs|exact IH].
Qed.

Definition Σx : senv := {[edual o1 := (dual S1, px‾)]}.
Definition Σy : senv := {[o2 := (dual S1, py)]}.

Lemma Σx_dual : senv_dual Σx = {[o1 := (S1, px)]}.
Proof.
  unfold senv_dual, Σx. rewrite map_fmap_singleton, kmap_singleton by apply _. simpl.
  by rewrite ?dual_involutive, ?pt_dual_dual.
Qed.

Lemma chans_Σx : chans_of Σx = {["a"]}.
Proof. unfold chans_of, Σx. by rewrite dom_singleton_L, set_map_singleton_L. Qed.

Lemma chans_Σy : chans_of Σy = {["b"]}.
Proof. unfold chans_of, Σy. by rewrite dom_singleton_L, set_map_singleton_L. Qed.

Lemma Σf_split : Σy ∪ senv_dual Σx = Σf.
Proof.
  rewrite Σx_dual. unfold Σy, Σf. apply map_union_comm.
  apply map_disjoint_singleton_l_2. by rewrite lookup_singleton_ne.
Qed.

Theorem fwd_expand W Σ C E T :
  fptyped None W (Σ ∪ Σx) (C, E) T →
  Σ ##ₘ Σx → "a" ∉ chans_of Σ → "b" ∉ chans_of Σ → "b" ∉ C → 1 ∉ sw_consts W →
  fptyped None (W ⊔ W_f) (Σ ∪ Σy) (C ∪ ∅ ∪ {["a"]}, E ⊎ {[+ fwd_t o1 o2 +]}) T.
Proof.
  intros HP HΣ Ha Hb HbC H1.
  pose proof (fptyped_chans _ _ _ _ _ HP) as HC. simpl in HC.
  rewrite chans_of_union, chans_Σx in HC.
  pose proof (fp_connect None W W_f Σ Σy Σx C ∅ E {[+ fwd_t o1 o2 +]} T) as H.
  rewrite chans_Σx in H. apply H; clear H.
  - exact HP.
  - rewrite Σf_split. apply fwd_term.
  - exact HΣ.
  - rewrite Σx_dual. unfold Σy. apply map_disjoint_singleton_l_2. by rewrite lookup_singleton_ne.
  - intros o. unfold Σx. rewrite dom_singleton_L, !elem_of_singleton. intros ->. discriminate.
  - rewrite ?chans_Σy, ?chans_Σx. set_solver.
  - rewrite ?chans_Σy, ?chans_Σx. set_solver.
  - rewrite ?chans_Σy, ?chans_Σx. set_solver.
  - set_solver.
  - rewrite ?chans_Σy, ?chans_Σx. set_solver.
  - set_solver.
  - apply cut_W_f_wok; [apply (fptyped_wf _ _ _ _ _ HP)|done].
Qed.

(** ** A closed run: partner ∥ fwd ∥ partner, deadlock free

    The partner of o1 is typed alone over the empty world, [fwd_expand]
    puts the forwarder behind it, and P-Connect adds the partner of o2.
    The fundamental theorem gives deadlock freedom ([soundness]). *)

Lemma p1_term : fptyped None sw_empty Σx (∅, {[+ p1_t (edual o1) +]}) TUnit.
Proof.
  apply (fp_term None sw_empty Σx ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_singleton.
  - intros o e He. unfold Σx in He. apply lookup_singleton_Some in He as [_ <-]. apply S1_dual_contr.
  - set_solver.
  - change (fhalf None) with (None : fuel).
    assert (tenv_of None Σx ∪ ∅ = tenv_df {[edual o1 := TE (dual S1) px‾ None None]}) as ->.
    { rewrite map_union_empty. unfold tenv_of, tenv_df, Σx. by rewrite !map_fmap_singleton. }
    apply (p1_dftyped sw_empty hc_empty).
  - apply sw_empty_wok.
Qed.

Lemma p2_term : fptyped None sw_empty (senv_dual Σy) (∅, {[+ p2_t (edual o2) +]}) TUnit.
Proof.
  assert (senv_dual Σy = {[edual o2 := (S1, py‾)]}) as ->.
  { unfold senv_dual, Σy. rewrite map_fmap_singleton, kmap_singleton by apply _. simpl.
    by rewrite ?dual_involutive. }
  apply (fp_term None sw_empty _ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_singleton.
  - intros o e He. apply lookup_singleton_Some in He as [_ <-]. apply S1_contr.
  - set_solver.
  - change (fhalf None) with (None : fuel).
    assert (tenv_of None {[edual o2 := (S1, py‾)]} ∪ ∅ = tenv_df {[edual o2 := TE S1 py‾ None None]}) as ->.
    { rewrite map_union_empty. unfold tenv_of, tenv_df. by rewrite !map_fmap_singleton. }
    apply (p2_dftyped sw_empty hc_empty).
  - apply sw_empty_wok.
Qed.

Definition fwd_config : proc :=
  ({["a"]} ∪ {["b"]}, ({[+ p1_t (edual o1) +]} ⊎ {[+ fwd_t o1 o2 +]}) ⊎ {[+ p2_t (edual o2) +]}).

Definition W_run : sworld := (sw_empty ⊔ W_f) ⊔ sw_empty.

Theorem fwd_config_typed : fptyped None W_run ∅ fwd_config TUnit.
Proof.
  assert (fptyped None (sw_empty ⊔ W_f) (∅ ∪ Σy) (∅ ∪ ∅ ∪ {["a"]}, {[+ p1_t (edual o1) +]} ⊎ {[+ fwd_t o1 o2 +]}) TUnit)
    as H1.
  { apply fwd_expand.
    - rewrite (left_id_L ∅ (∪)). apply p1_term.
    - apply map_disjoint_empty_l.
    - unfold chans_of. rewrite dom_empty_L. set_solver.
    - unfold chans_of. rewrite dom_empty_L. set_solver.
    - set_solver.
    - simpl. set_solver. }
  rewrite (left_id_L ∅ (∪)) in H1.
  pose proof (fp_connect None (sw_empty ⊔ W_f) sw_empty ∅ ∅ Σy (∅ ∪ ∅ ∪ {["a"]}) ∅
    ({[+ p1_t (edual o1) +]} ⊎ {[+ fwd_t o1 o2 +]}) {[+ p2_t (edual o2) +]} TUnit) as H.
  rewrite !(left_id_L ∅ (∪)), chans_Σy in H.
  assert ({["a"]} ∪ ∅ ∪ {["b"]} = ({["a"]} ∪ {["b"]} : gset chan)) as E by set_solver.
  rewrite E in H. apply H; clear H E.
  - exact H1.
  - apply p2_term.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - intros o. unfold Σy. rewrite dom_singleton_L, !elem_of_singleton. intros ->. discriminate.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - apply swf_wok, swf_bare. intros [u v] [Hf|Hf]; simpl in Hf; destruct Hf as (_ & (a & _ & Ha) & _);
      unfold swshared in Ha; simpl in Ha; set_solver.
Qed.

Theorem fwd_config_deadlock_free : deadlock_free fwd_config.
Proof. exact (soundness W_run fwd_config TUnit fwd_config_typed). Qed.

(** ** The forwarder ring is rejected

      fwd(o1, o2) ∥ fwd(o2‾, o1‾),  cut on {a, b}

    Each forwarder waits to receive from the other, so the ring
    deadlocks. Every typing of fwd(a, b) asks the point of a below the
    head of b ([fwd_needs]). The first forwarder holds o1 at x and o2 at
    y, so it asks x ≺ y‾. The second holds o2‾ at y‾ and o1‾ at x‾, so it
    asks y‾ ≺ x. The joined world then has x ≺ y‾ ≺ x, and no world, no
    bound and no type type the ring ([ring_rejected]). *)

Section inv_recv.
  Context (W : sworld) (N : fuel).

  Lemma inv_recv Θ Γ Δ F e T c :
    typed W N Θ Γ Δ F (ERecv e) T c →
    ∃ Θ' Γ' Δ' F' S0 x a mS c0, opened W Θ Γ Δ F Θ' Γ' Δ' F' ∧
      ub_below_s W Γ' (Some x) F' ∧ typed W N Θ' Γ' Δ' F' e (TSess S0 x a mS) c0.
  Proof.
    remember (ERecv e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as ->. eexists _, _, _, _, _, _, _, _, _. split_and!; [constructor|done..].
    - by apply IHtyped.
    - by apply IHtyped.
    - destruct (IHtyped He) as (Θ' & Γ' & Δ' & F' & S0 & x & a & mS & c0 & Ho & Hrest).
      exists Θ', Γ', Δ', F', S0, x, a, mS, c0. split; [|done]. by eapply op_step.
  Qed.
End inv_recv.

Lemma fwd_needs W N Θ Γ Δ F a b T c ea eb :
  a ≠ b → typed W N Θ Γ Δ F (fwd_t a b) T c →
  Θ !! a = Some ea → Θ !! b = Some eb → slt W Γ (te_pt ea) (te_pt eb)‾.
Proof.
  intros Hab H Ha Hb. unfold fwd_t in H.
  apply inv_letp in H as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & T' & c1 & c2
    & Ho & Hs & _ & H1 & _ & _ & _).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Ho) as (σ & Hσl & _ & Hσs).
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ H1) as [Hd1 _]. simpl in Hd1.
  assert (Θ1 !! a = Some (tentry_pinst σ ea)) as Ha1.
  { eapply tsplit_lookup_l; [done| |by apply Hσl].
    intros Hin. destruct Hs as [Hdisj _]. assert (a ∈ dom Θ1) as Hin1 by (rewrite <-Hd1; set_solver).
    apply elem_of_dom in Hin as [? Hx2]. apply elem_of_dom in Hin1 as [? Hx1].
    exact (proj1 (map_disjoint_spec Θ1 Θ2) Hdisj a _ _ Hx1 Hx2). }
  assert (Θ2 !! b = Some (tentry_pinst σ eb)) as Hb2.
  { eapply tsplit_lookup_r; [done| |by apply Hσl]. rewrite <-Hd1. set_solver. }
  apply inv_recv in H1 as (Θ'' & Γ'' & Δ'' & F'' & S0 & x & a0 & mS & c0 & Ho2 & Hub & Hch).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Ho2) as (σ2 & Hl2 & Hf2 & Hs2).
  destruct (inv_chan _ _ _ _ _ _ _ _ _ Hch _ _ _ _ eq_refl) as (e & He & Hx).
  rewrite (Hl2 _ _ Ha1) in He. injection He as <-.
  destruct Hub as [Hub _].
  assert (pt_inst σ2 (te_pt (tentry_pinst σ eb))‾ ∈ F''.1) as Hy.
  { apply Hf2. rewrite sf_unionb_fst. apply elem_of_union_r, elem_of_union_l.
    apply elem_of_tenv_heads. eauto. }
  apply Hub in Hy. rewrite <-Hx, !te_pt_pinst in Hy.
  apply Hσs. rewrite pt_inst_dual. apply Hs2. exact Hy.
Qed.

Definition ring_config : proc :=
  ({["a"]} ∪ {["b"]}, {[+ fwd_t o1 o2 +]} ⊎ {[+ fwd_t (edual o2) (edual o1) +]}).

Lemma ring_threads_ne : fwd_t o1 o2 ≠ fwd_t (edual o2) (edual o1).
Proof. unfold fwd_t, o1, o2. simpl. congruence. Qed.

Lemma o2o1_dual_ne : edual o2 ≠ edual o1.
Proof. unfold o1, o2. simpl. congruence. Qed.

Ltac rfends_tac := unfold fwd_t, o1, o2; simpl; set_unfold; intuition congruence.

Theorem ring_rejected_full N W T : ¬ fptyped N W ∅ ring_config T.
Proof.
  intros H. pose proof (fptyped_wf _ _ _ _ _ H) as [_ HWf].
  pose proof (λ x, wok_acyc N W HWf x) as Hirr.
  apply fptyped_two in H as (W1 & W2 & Σ1 & Σ2 & ΣC & C1 & C2 & u1 & u2 & -> & HΣ & _ & Hu & H1 & H2 & _).
  symmetry in HΣ. pose proof (map_positive_l _ _ HΣ) as ->. rewrite (left_id_L ∅ (∪)) in HΣ. subst Σ2.
  rewrite !(left_id_L ∅ (∪)) in H1, H2.
  set (t1 := fwd_t o1 o2) in *. set (t2 := fwd_t (edual o2) (edual o1)) in *.
  assert ((u1 = t1 ∧ u2 = t2) ∨ (u1 = t2 ∧ u2 = t1)) as Hcase.
  { pose proof ring_threads_ne as Hne. fold t1 t2 in Hne.
    assert (u1 ∈ ({[+ u1 +]} ⊎ {[+ u2 +]} : gmultiset expr)) as Hu1 by multiset_solver.
    assert (u2 ∈ ({[+ u1 +]} ⊎ {[+ u2 +]} : gmultiset expr)) as Hu2 by multiset_solver.
    rewrite Hu in Hu1, Hu2. apply gmultiset_elem_of_disj_union in Hu1, Hu2.
    rewrite !gmultiset_elem_of_singleton in Hu1, Hu2.
    destruct Hu1 as [->| ->], Hu2 as [->| ->]; auto; exfalso.
    - assert (t2 ∈ ({[+ t1 +]} ⊎ {[+ t1 +]} : gmultiset expr)) as Hp by (rewrite Hu; multiset_solver).
      apply gmultiset_elem_of_disj_union in Hp. rewrite !gmultiset_elem_of_singleton in Hp.
      destruct Hp as [Hp|Hp]; by apply Hne.
    - assert (t1 ∈ ({[+ t2 +]} ⊎ {[+ t2 +]} : gmultiset expr)) as Hp by (rewrite Hu; multiset_solver).
      apply gmultiset_elem_of_disj_union in Hp. rewrite !gmultiset_elem_of_singleton in Hp.
      destruct Hp as [Hp|Hp]; by apply Hne. }
  destruct Hcase as [[-> ->]|[-> ->]]; subst t1 t2.
  - destruct (side_lookup _ _ _ _ _ _ H1) as (Θt & ct & Ht & Hlt).
    destruct (side_lookup _ _ _ _ _ _ H2) as (Θp & cp & Hp & Hlp).
    destruct (Hlt o1) as (S & x & e1 & Hc & He1 & <-); [rfends_tac|rfends_tac|].
    destruct (Hlt o2) as (S' & y & e2 & Hd & He2 & <-); [rfends_tac|rfends_tac|].
    destruct (Hlp (edual o2)) as (S2 & y' & e2' & Hd' & He2' & <-); [rfends_tac|rfends_tac|].
    destruct (Hlp (edual o1)) as (S1' & x' & e1' & Hc' & He1' & <-); [rfends_tac|rfends_tac|].
    rewrite (sdual_lookup _ _ _ _ Hc) in Hc'. rewrite (sdual_lookup _ _ _ _ Hd) in Hd'.
    injection Hc' as _ Hx'. injection Hd' as _ Hy'.
    pose proof (slt_empty_w _ _ _ (fwd_needs _ _ _ _ _ _ _ _ _ _ _ _ o1_o2 Ht He1 He2)) as Ha.
    pose proof (slt_empty_w _ _ _ (fwd_needs _ _ _ _ _ _ _ _ _ _ _ _ o2o1_dual_ne Hp He2' He1')) as Hb.
    rewrite <-Hx', <-Hy', pt_dual_dual in Hb.
    apply (Hirr (te_pt e1)). eapply sw_lt_trans; [eapply sw_lt_mono; [apply swext_join_l|exact Ha]|].
    eapply sw_lt_mono; [apply swext_join_r|exact Hb].
  - destruct (side_lookup _ _ _ _ _ _ H2) as (Θt & ct & Ht & Hlt).
    destruct (side_lookup _ _ _ _ _ _ H1) as (Θp & cp & Hp & Hlp).
    destruct (Hlt o1) as (S & x & e1 & Hc & He1 & <-); [rfends_tac|rfends_tac|].
    destruct (Hlt o2) as (S' & y & e2 & Hd & He2 & <-); [rfends_tac|rfends_tac|].
    destruct (Hlp (edual o2)) as (S2 & p & e2' & Hd' & He2' & <-); [rfends_tac|rfends_tac|].
    destruct (Hlp (edual o1)) as (S1' & q & e1' & Hc' & He1' & <-); [rfends_tac|rfends_tac|].
    pose proof (sdual_lookup _ _ _ _ Hc') as Hc2. pose proof (sdual_lookup _ _ _ _ Hd') as Hd2.
    rewrite edual_edual in Hc2, Hd2. rewrite Hc2 in Hc. rewrite Hd2 in Hd.
    injection Hc as _ Hx. injection Hd as _ Hy.
    pose proof (slt_empty_w _ _ _ (fwd_needs _ _ _ _ _ _ _ _ _ _ _ _ o1_o2 Ht He1 He2)) as Ha.
    pose proof (slt_empty_w _ _ _ (fwd_needs _ _ _ _ _ _ _ _ _ _ _ _ o2o1_dual_ne Hp He2' He1')) as Hb.
    rewrite <-Hx, <-Hy, pt_dual_dual in Ha.
    apply (Hirr (te_pt e2')). eapply sw_lt_trans; [eapply sw_lt_mono; [apply swext_join_l|exact Hb]|].
    eapply sw_lt_mono; [apply swext_join_r|exact Ha].
Qed.

(** The hidden judgment translates to the full one ([ptyped_full]), so
    it rejects the ring as well. *)
Corollary ring_rejected N W T : ¬ ptyped N W ∅ ring_config T.
Proof. intros H. destruct (ptyped_full _ _ _ _ _ H) as (W' & Hf & _). exact (ring_rejected_full N W' T Hf). Qed.

(** ** A higher-order payload

      Sh = ?(Close@ι₀).Close

    A message on x carries an end at the field x·0. The forwarder cannot
    send the received end on, because a payload sent on y must sit at
    y·0 and an end keeps its point. It η-expands the payload instead.
    It creates a channel at the field y·0 (E-New-Field), sends the end at
    y·0 on, and forwards the received end at x·0 to the kept end at
    (y·0)‾. For Close that inner forwarder closes both. The payload ends
    pass on with facts at their fields.

      fwdh o1 o2 = let (e, o1) = recv o1 in let (c', c) = new_{y·0} in
                   let o2 = send ⟨c, o2⟩ in
                   close e; close c'; close o1; close o2

      recv o1 at x       x ≺ y‾
      send o2 at y       y ≺ (y·0)‾ (the payload) and y ≺ y·0, y ≺ (x⁺)‾,
                         y ≺ (x·0)‾ (the ends held)
      close e at x·0     x·0 ≺ y·0, x·0 ≺ (x⁺)‾, x·0 ≺ (y⁺)‾
      close c' at (y·0)‾ (y·0)‾ ≺ (x⁺)‾, (y·0)‾ ≺ (y⁺)‾
      close o1 at x⁺     x⁺ ≺ (y⁺)‾ *)

Definition Th : ty := TSess SEnd (pvar 0) None None.
Definition Sh : sty := SSeq (SRcv 1 Th) SEnd.

Lemma Th_scoped : pscoped 1 Th.
Proof. cbn. split; [exact I|]. intros a Ha. injection Ha as <-. lia. Qed.

Lemma Sh_contr : scontr Sh.
Proof. contr_tac. Qed.

Lemma Sh_dual_contr : scontr (dual Sh).
Proof. contr_tac. Qed.

Definition fwdh_t (o1 o2 : cend) : expr :=
  LetP (ERecv (Chan o1))
    (LetP ENew
      (ELet (ESend (Pair (Var 1) (Chan o2)))
        (LetU (EClose (Var 4))
          (LetU (EClose (Var 1))
            (LetU (EClose (Var 3)) (EClose (Var 0))))))).

Definition fwdh_facts (W : sworld) (Γ : hctx) (x y : point) : Prop :=
  slt W Γ x (y‾) ∧
  slt W Γ y ((y·0)‾) ∧ slt W Γ y (y·0) ∧ slt W Γ y (x⁺‾) ∧ slt W Γ y ((x·0)‾) ∧
  slt W Γ (x·0) (y·0) ∧ slt W Γ (x·0) (x⁺‾) ∧ slt W Γ (x·0) (y⁺‾) ∧
  slt W Γ ((y·0)‾) (x⁺‾) ∧ slt W Γ ((y·0)‾) (y⁺‾) ∧
  slt W Γ (x⁺) (y⁺‾).

Ltac fh_tac := match goal with H : fwdh_facts _ _ _ _ |- _ =>
  destruct H as (?&?&?&?&?&?&?&?&?&?&?); assumption end.

Ltac hz_tac := repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst; try contradiction; fh_tac.

Section typing_h.
  Context (W : sworld) (Γ : hctx) (o1 o2 : cend) (x y : point).
  Context (Ho : o1 ≠ o2) (Hf : fwdh_facts W Γ x y).

  Definition Θh : tenv := {[o1 := TE Sh x None None]} ∪ {[o2 := TE (dual Sh) y None None]}.

  Lemma Θh_split : tsplit Θh {[o1 := TE Sh x None None]} {[o2 := TE (dual Sh) y None None]}.
  Proof. split; [by apply map_disjoint_singleton_l_2; rewrite lookup_singleton_ne|reflexivity]. Qed.

  Lemma fwdh_dftyped : dftyped W Θh Γ [] (∅, None) (fwdh_t o1 o2) TUnit.
  Proof.
    unfold fwdh_t.
    eapply d_letp; [apply Θh_split|apply lsplit_nil| |].
    { eapply d_recv with (S0 := Sh) (x := x) (m := 1) (T := Th) (S := SEnd);
        [reflexivity|exact Th_scoped| |apply d_chan, spare_unl; spare_tac].
      apply ub_below_nil; [reflexivity|]. intros z Hz.
      rewrite tenv_heads_one in Hz. cbn in Hz. set_unfold in Hz. destruct Hz as [->|Hz]; [fh_tac|set_solver]. }
    eapply d_letp with (Θ1 := ∅) (Θ2 := {[o2 := TE (dual Sh) y None None]});
      [split; [apply map_disjoint_empty_l|by rewrite map_empty_union]|lsplit_tac ENew EUnit| |].
    { apply (d_new_fld _ _ _ _ y 0 SEnd); [apply spare_unl; spare_tac|contr_tac]. }
    eapply d_let with (Θ1 := {[o2 := TE (dual Sh) y None None]}) (Θ2 := ∅);
      [split; [apply map_disjoint_empty_r|by rewrite map_union_empty]
      |lsplit_tac (ESend (Pair (Var 1) (Chan o2))) EUnit| |].
    { eapply d_send with (S0 := dual Sh) (x := y) (m := 1) (T := Th) (S := SEnd);
        [reflexivity|exact Th_scoped|reflexivity| | |].
      - intros z Hz. cbn in Hz. set_unfold in Hz. subst z. fh_tac.
      - apply ub_below_nil; [reflexivity|]. intros z Hz.
        rewrite tenv_heads_empty in Hz. cbn in Hz. set_unfold in Hz.
        hz_tac.
      - eapply d_pair with (Θ1 := ∅) (Θ2 := {[o2 := TE (dual Sh) y None None]});
          [split; [apply map_disjoint_empty_l|by rewrite map_empty_union]
          |lsplit_tac (Var 1) (Chan o2)| |].
        + eapply d_var'; [reflexivity|]. spare_tac.
        + apply d_chan, spare_unl. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 4)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := x·0); [reflexivity| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [reflexivity|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. set_unfold in Hz.
      hz_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := (y·0)‾); [reflexivity| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [reflexivity|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. set_unfold in Hz.
      hz_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 3)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := x⁺); [reflexivity| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [reflexivity|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. set_unfold in Hz.
      hz_tac. }
    eapply d_close with (S0 := SEnd) (x := y⁺); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|spare_tac].
    Unshelve. all: exact None.
  Qed.
End typing_h.

(** The higher-order forwarder's world, over the constant roots of [px]
    and [py] and the fields px·0 and py·0. The potential
    4·offset + (0 for x, 1 for y, 2 for x·0, 3 for y·0) grows along every
    fact and every step, so the world is well-founded. *)

Definition fwdh_fact (x y : point) (g : fact) : Prop :=
  g = FLt x (y‾) ∨
  g = FLt y ((y·0)‾) ∨ g = FLt y (y·0) ∨ g = FLt y (x⁺‾) ∨ g = FLt y ((x·0)‾) ∨
  g = FLt (x·0) (y·0) ∨ g = FLt (x·0) (x⁺‾) ∨ g = FLt (x·0) (y⁺‾) ∨
  g = FLt ((y·0)‾) (x⁺‾) ∨ g = FLt ((y·0)‾) (y⁺‾) ∨
  g = FLt (x⁺) (y⁺‾).

Definition W_h : sworld := SWorld ({[0]} ∪ {[1]}) (fwdh_fact px py).

Ltac fh_cases H := repeat match type of H with _ ∨ _ => destruct H as [H|H] end.

Lemma W_h_wf : sworld_wf W_h.
Proof.
  split; simpl. intros u v H. unfold fwdh_fact in H. fh_cases H;
    injection H as Hu Hv; subst; split; eexists; (split; [reflexivity|set_solver]).
Qed.

Definition hcls (n : pname) : nat :=
  match n with
  | NConst 1 => 1
  | NField (NConst 0) 0 0 => 2
  | NField (NConst 1) 0 0 => 3
  | _ => 0
  end.

Lemma hcls_le n : hcls n ≤ 3.
Proof. unfold hcls. repeat case_match; lia. Qed.

Definition hpot (u : point) : nat := 4 * pt_off u + hcls (pt_name u).

Lemma W_h_step u v : swstep W_h u v → hpot u < hpot v.
Proof.
  intros Hs. destruct Hs as [u v H|u|u].
  - simpl in H. unfold fwdh_fact in H. fh_cases H; injection H as -> ->; vm_compute; lia.
  - unfold hpot. cbn [pt_shift pt_name pt_off]. pose proof (hcls_le (pt_name u)). lia.
  - unfold hpot. cbn [pt_shift pt_dual pt_name pt_off]. pose proof (hcls_le (pt_name u)). lia.
Qed.

Lemma W_h_swf : swf W_h.
Proof.
  apply swf_iff.
  assert (∀ u v, W_h ⊢ₛ u ≺ v → hpot u < hpot v) as Hlt.
  { intros u v H. induction H as [u v H|u v w H _ IH]; [by apply W_h_step|].
    apply W_h_step in H. lia. }
  assert (∀ m u, hpot u = m → Acc (sw_lt W_h) u) as Hacc.
  { intros m. induction m as [m IH] using lt_wf_ind. intros u <-. constructor.
    intros v Hv. eapply IH; [apply Hlt, Hv|done]. }
  intros u. by apply (Hacc (hpot u)).
Qed.

Lemma W_h_facts : fwdh_facts W_h hc_empty px py.
Proof. split_and!; apply sl_w, sw_lt_fact; simpl; unfold fwdh_fact; tauto. Qed.

Definition Σh : senv := {[o1 := (Sh, px)]} ∪ {[o2 := (dual Sh, py)]}.

Lemma Σh_pfree : pfree Σh.
Proof.
  intros o Ho Hn. unfold Σh in Ho, Hn. rewrite dom_union_L, !dom_singleton_L in Ho, Hn.
  set_unfold in Ho; set_unfold in Hn. destruct Ho as [->| ->]; simpl in Hn; destruct Hn; discriminate.
Qed.

(** The higher-order forwarder typed by P-Term over its world. *)
Theorem fwdh_term : fptyped None W_h Σh (∅, {[+ fwdh_t o1 o2 +]}) TUnit.
Proof.
  apply (fp_term None W_h Σh ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply Σh_pfree.
  - intros o e He. unfold Σh in He. apply lookup_union_Some_raw in He as [He|[_ He]];
      apply lookup_singleton_Some in He as [_ <-]; [apply Sh_contr|apply Sh_dual_contr].
  - set_solver.
  - change (fhalf None) with (None : fuel).
    assert (tenv_of None Σh ∪ ∅ = tenv_df (Θh o1 o2 px py)) as ->.
    { rewrite map_union_empty. unfold tenv_of, tenv_df, Σh, Θh. by rewrite !map_fmap_union, !map_fmap_singleton. }
    exact (fwdh_dftyped W_h hc_empty o1 o2 px py o1_o2 W_h_facts).
  - split; [apply W_h_wf|apply swf_wok, W_h_swf].
Qed.

(** *** A closed higher-order run, deadlock free

    The partner of o1 creates a channel at the field of its point, sends
    one end and closes the other. The partner of o2 receives an end and
    closes it. Both need facts on their own points only. All three worlds
    raise the potential [hpot], so every cut is well-founded. *)

Definition p1h_t (o : cend) : expr :=
  LetP ENew (ELet (ESend (Pair (Var 1) (Chan o))) (LetU (EClose (Var 1)) (EClose (Var 0)))).

Definition p2h_t (o : cend) : expr :=
  LetP (ERecv (Chan o)) (LetU (EClose (Var 1)) (EClose (Var 0))).

Lemma p1h_dftyped W Γ o z :
  slt W Γ z ((z·0)‾) → slt W Γ z (z·0) → slt W Γ ((z·0)‾) (z⁺‾) →
  dftyped W {[o := TE (dual Sh) z None None]} Γ [] (∅, None) (p1h_t o) TUnit.
Proof.
  intros H1 H2 H3. unfold p1h_t.
  eapply d_letp with (Θ1 := ∅) (Θ2 := {[o := TE (dual Sh) z None None]});
    [split; [apply map_disjoint_empty_l|by rewrite map_empty_union]|apply lsplit_nil| |].
  { apply (d_new_fld _ _ _ _ z 0 SEnd); [apply spare_unl; spare_tac|contr_tac]. }
  eapply d_let with (Θ1 := {[o := TE (dual Sh) z None None]}) (Θ2 := ∅);
    [split; [apply map_disjoint_empty_r|by rewrite map_union_empty]
    |lsplit_tac (ESend (Pair (Var 1) (Chan o))) EUnit| |].
  { eapply d_send with (S0 := dual Sh) (x := z) (m := 1) (T := Th) (S := SEnd);
      [reflexivity|exact Th_scoped|reflexivity| | |].
    - intros u Hu. cbn in Hu. set_unfold in Hu. by subst u.
    - apply ub_below_nil; [reflexivity|]. intros u Hu.
      rewrite tenv_heads_empty in Hu. cbn in Hu. set_unfold in Hu.
      repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst; try contradiction; done.
    - eapply d_pair with (Θ1 := ∅) (Θ2 := {[o := TE (dual Sh) z None None]});
        [split; [apply map_disjoint_empty_l|by rewrite map_empty_union]
        |lsplit_tac (Var 1) (Chan o)| |].
      + eapply d_var'; [reflexivity|]. spare_tac.
      + apply d_chan, spare_unl. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
  { eapply d_close with (S0 := SEnd) (x := (z·0)‾); [reflexivity| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [reflexivity|]. intros u Hu.
    rewrite tenv_heads_empty in Hu. cbn in Hu. set_unfold in Hu.
    repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst; try contradiction; done. }
  eapply d_close with (S0 := SEnd) (x := z⁺); [reflexivity|apply ub_below_empty|].
  eapply d_var'; [reflexivity|spare_tac].
  Unshelve. all: exact None.
Qed.

Lemma p2h_dftyped W Γ o z :
  slt W Γ (z·0) (z⁺‾) →
  dftyped W {[o := TE Sh z None None]} Γ [] (∅, None) (p2h_t o) TUnit.
Proof.
  intros H1. unfold p2h_t.
  eapply d_letp with (Θ1 := {[o := TE Sh z None None]}) (Θ2 := ∅);
    [split; [apply map_disjoint_empty_r|by rewrite map_union_empty]|apply lsplit_nil| |].
  { eapply d_recv with (S0 := Sh) (x := z) (m := 1) (T := Th) (S := SEnd);
      [reflexivity|exact Th_scoped| |apply d_chan, spare_unl; spare_tac].
    apply ub_below_nil; [reflexivity|]. intros u Hu.
    rewrite tenv_heads_empty in Hu. cbn in Hu. set_solver. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
  { eapply d_close with (S0 := SEnd) (x := z·0); [reflexivity| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [reflexivity|]. intros u Hu.
    rewrite tenv_heads_empty in Hu. cbn in Hu. set_unfold in Hu.
    repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst; try contradiction; done. }
  eapply d_close with (S0 := SEnd) (x := z⁺); [reflexivity|apply ub_below_empty|].
  eapply d_var'; [reflexivity|spare_tac].
  Unshelve. all: exact None.
Qed.

Definition W_p1 : sworld :=
  SWorld {[0]} (λ g, g = FLt (px‾) ((px‾·0)‾) ∨ g = FLt (px‾) (px‾·0) ∨ g = FLt ((px‾·0)‾) (px‾⁺‾)).
Definition W_p2 : sworld := SWorld {[1]} (λ g, g = FLt (py‾·0) (py‾⁺‾)).

Lemma W_p1_wf : sworld_wf W_p1.
Proof.
  split; simpl. intros u v H. fh_cases H;
    injection H as Hu Hv; subst; split; eexists; (split; [reflexivity|set_solver]).
Qed.

Lemma W_p2_wf : sworld_wf W_p2.
Proof.
  split; simpl. intros u v H. injection H as Hu Hv; subst; split; eexists; (split; [reflexivity|set_solver]).
Qed.

(** Worlds whose steps raise [hpot]. *)
Definition hmono (W : sworld) : Prop := ∀ u v, swstep W u v → hpot u < hpot v.

Lemma hmono_lt W : hmono W → ∀ u v, W ⊢ₛ u ≺ v → hpot u < hpot v.
Proof.
  intros HW u v H. induction H as [u v H|u v w H _ IH]; [by apply HW|]. apply HW in H. lia.
Qed.

Lemma hmono_swf W : hmono W → swf W.
Proof.
  intros HW. apply swf_iff.
  assert (∀ m u, hpot u = m → Acc (sw_lt W) u) as Hacc.
  { intros m. induction m as [m IH] using lt_wf_ind. intros u <-. constructor.
    intros v Hv. eapply IH; [apply (hmono_lt W HW), Hv|done]. }
  intros u. by apply (Hacc (hpot u)).
Qed.

Lemma hpot_po u : hpot u < hpot u⁺ ∧ hpot u < hpot u‾⁺.
Proof. unfold hpot. cbn [pt_shift pt_dual pt_name pt_off]. pose proof (hcls_le (pt_name u)). lia. Qed.

Lemma hmono_facts W : (∀ u v, sw_facts W (FLt u v) → hpot u < hpot v) → hmono W.
Proof. intros H u v Hs. destruct Hs as [u v Hf|u|u]; [by apply H|apply hpot_po|apply hpot_po]. Qed.

Lemma hmono_join A B : hmono A → hmono B → hmono (A ⊔ B).
Proof. intros HA HB u v Hs. apply swstep_join_inv in Hs as [Hs|Hs]; [by apply HA|by apply HB]. Qed.

Lemma hmono_restrict W S : hmono W → hmono (swrestrict W S).
Proof.
  intros HW. apply hmono_facts. intros u v (Hlt & _ & _). by apply (hmono_lt W HW).
Qed.

Lemma W_h_mono : hmono W_h.
Proof. apply hmono_facts. intros u v H. simpl in H. unfold fwdh_fact in H. fh_cases H; injection H as -> ->; vm_compute; lia. Qed.

Lemma W_p1_mono : hmono W_p1.
Proof. apply hmono_facts. intros u v H. simpl in H. fh_cases H; injection H as -> ->; vm_compute; lia. Qed.

Lemma W_p2_mono : hmono W_p2.
Proof. apply hmono_facts. intros u v H. simpl in H. injection H as -> ->; vm_compute; lia. Qed.

Definition Σhx : senv := {[o1 := (Sh, px)]}.
Definition Σhy : senv := {[o2 := (dual Sh, py)]}.

Lemma Σhx_dual : senv_dual Σhx = {[edual o1 := (dual Sh, px‾)]}.
Proof. unfold senv_dual, Σhx. by rewrite map_fmap_singleton, kmap_singleton by apply _. Qed.

Lemma Σhy_dual : senv_dual Σhy = {[edual o2 := (Sh, py‾)]}.
Proof.
  unfold senv_dual, Σhy. rewrite map_fmap_singleton, kmap_singleton by apply _. simpl.
  by rewrite ?dual_involutive.
Qed.

Lemma p1h_term : fptyped None W_p1 (∅ ∪ senv_dual Σhx) (∅, {[+ p1h_t (edual o1) +]}) TUnit.
Proof.
  rewrite (left_id_L ∅ (∪)), Σhx_dual.
  apply (fp_term None W_p1 _ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_singleton.
  - intros o e He. apply lookup_singleton_Some in He as [_ <-]. apply Sh_dual_contr.
  - set_solver.
  - change (fhalf None) with (None : fuel).
    assert (tenv_of None {[edual o1 := (dual Sh, px‾)]} ∪ ∅ = tenv_df {[edual o1 := TE (dual Sh) px‾ None None]}) as ->.
    { rewrite map_union_empty. unfold tenv_of, tenv_df. by rewrite !map_fmap_singleton. }
    apply p1h_dftyped; apply sl_w, sw_lt_fact; simpl; tauto.
  - split; [apply W_p1_wf|apply swf_wok, hmono_swf, W_p1_mono].
Qed.

Lemma p2h_term : fptyped None W_p2 (∅ ∪ senv_dual Σhy) (∅, {[+ p2h_t (edual o2) +]}) TUnit.
Proof.
  rewrite (left_id_L ∅ (∪)), Σhy_dual.
  apply (fp_term None W_p2 _ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_singleton.
  - intros o e He. apply lookup_singleton_Some in He as [_ <-]. apply Sh_contr.
  - set_solver.
  - change (fhalf None) with (None : fuel).
    assert (tenv_of None {[edual o2 := (Sh, py‾)]} ∪ ∅ = tenv_df {[edual o2 := TE Sh py‾ None None]}) as ->.
    { rewrite map_union_empty. unfold tenv_of, tenv_df. by rewrite !map_fmap_singleton. }
    apply p2h_dftyped; apply sl_w, sw_lt_fact; simpl; done.
  - split; [apply W_p2_wf|apply swf_wok, hmono_swf, W_p2_mono].
Qed.

Definition fwdh_config : proc :=
  ({["a"]} ∪ {["b"]}, ({[+ fwdh_t o1 o2 +]} ⊎ {[+ p1h_t (edual o1) +]}) ⊎ {[+ p2h_t (edual o2) +]}).

Definition W_hrun : sworld := (W_h ⊔ W_p1) ⊔ W_p2.

Lemma chans_single (o : cend) (v : sty * point) : chans_of {[o := v]} = {[ech o]}.
Proof. unfold chans_of. by rewrite dom_singleton_L, set_map_singleton_L. Qed.

Lemma chans_empty : chans_of (∅ : senv) = ∅.
Proof. unfold chans_of. by rewrite dom_empty_L, set_map_empty. Qed.

Lemma chans_hx : chans_of Σhx = {["a"]}.
Proof. unfold Σhx. by rewrite chans_single. Qed.

Lemma chans_hy : chans_of Σhy = {["b"]}.
Proof. unfold Σhy. by rewrite chans_single. Qed.

Theorem fwdh_config_typed : fptyped None W_hrun ∅ fwdh_config TUnit.
Proof.
  assert (fptyped None (W_h ⊔ W_p1) Σhy (∅ ∪ ∅ ∪ {["a"]}, {[+ fwdh_t o1 o2 +]} ⊎ {[+ p1h_t (edual o1) +]}) TUnit)
    as H1.
  { pose proof (fp_connect None W_h W_p1 Σhy ∅ Σhx ∅ ∅
      {[+ fwdh_t o1 o2 +]} {[+ p1h_t (edual o1) +]} TUnit) as H.
    rewrite (right_id_L ∅ (∪)), chans_hx in H.
    apply H; clear H.
    - assert (Σhy ∪ Σhx = Σh) as -> by (unfold Σhy, Σhx, Σh; apply map_union_comm;
        apply map_disjoint_singleton_l_2; by rewrite lookup_singleton_ne).
      apply fwdh_term.
    - apply p1h_term.
    - unfold Σhy, Σhx. apply map_disjoint_singleton_l_2. by rewrite lookup_singleton_ne.
    - apply map_disjoint_empty_l.
    - intros o. unfold Σhx. rewrite dom_singleton_L, !elem_of_singleton. intros ->. discriminate.
    - rewrite ?chans_hy, ?chans_hx, ?chans_empty. set_solver.
    - rewrite ?chans_hy, ?chans_hx, ?chans_empty. set_solver.
    - rewrite ?chans_hy, ?chans_hx, ?chans_empty. set_solver.
    - set_solver.
    - set_solver.
    - set_solver.
    - apply swf_wok, hmono_swf, hmono_join; apply hmono_restrict; [apply W_h_mono|apply W_p1_mono]. }
  pose proof (fp_connect None (W_h ⊔ W_p1) W_p2 ∅ ∅ Σhy (∅ ∪ ∅ ∪ {["a"]}) ∅
    ({[+ fwdh_t o1 o2 +]} ⊎ {[+ p1h_t (edual o1) +]}) {[+ p2h_t (edual o2) +]} TUnit) as H.
  rewrite !(left_id_L ∅ (∪)), chans_hy in H.
  assert ({["a"]} ∪ ∅ ∪ {["b"]} = ({["a"]} ∪ {["b"]} : gset chan)) as E by set_solver.
  rewrite E in H. apply H; clear H E.
  - exact H1.
  - pose proof p2h_term as Hp. rewrite (left_id_L ∅ (∪)) in Hp. exact Hp.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - intros o. unfold Σhy. rewrite dom_singleton_L, !elem_of_singleton. intros ->. discriminate.
  - rewrite chans_empty. set_solver.
  - rewrite chans_empty. set_solver.
  - rewrite chans_empty. set_solver.
  - set_solver.
  - rewrite ?chans_hy, ?chans_empty. set_solver.
  - rewrite chans_empty. set_solver.
  - apply swf_wok, hmono_swf, hmono_join; apply hmono_restrict;
      [apply hmono_join; [apply W_h_mono|apply W_p1_mono]|apply W_p2_mono].
Qed.

Theorem fwdh_config_deadlock_free : deadlock_free fwdh_config.
Proof. exact (soundness W_hrun fwdh_config TUnit fwdh_config_typed). Qed.

(** ** The schema for first-order protocols

    A protocol of data messages and Close, p ::= end | ?p | !p, with
    S(p) its session type at unit payloads. The copycat [fb p] works on
    the two ends in the de Bruijn context [o2; o1] and returns them to
    that shape after each step, so it is defined, and typed, by
    recursion on p. The facts [ffp p x y] are generated by p.

      ffp end x y   = x ≺ y‾
      ffp (?p) x y  = x ≺ y‾, y ≺ (x⁺)‾, ffp p x⁺ y⁺
      ffp (!p) x y  = y ≺ x‾, x ≺ (y⁺)‾, ffp p x⁺ y⁺ *)

Inductive proto := PEnd | PRcv (p : proto) | PSnd (p : proto).

Fixpoint pS (p : proto) : sty :=
  match p with
  | PEnd => SEnd
  | PRcv q => SSeq (SRcv 0 TUnit) (pS q)
  | PSnd q => SSeq (SSnd 0 TUnit) (pS q)
  end.

Fixpoint pdual (p : proto) : proto :=
  match p with PEnd => PEnd | PRcv q => PSnd (pdual q) | PSnd q => PRcv (pdual q) end.

Lemma pS_dual p : dual (pS p) = pS (pdual p).
Proof. induction p as [|p IH|p IH]; simpl; rewrite ?IH; done. Qed.

Lemma pS_contr p : scontr (pS p).
Proof. induction p as [|p IH|p IH]; cbn [pS scontr tcontr]; rewrite ?IH; try done. Qed.

Lemma sty_df_pS p : sty_df (pS p) = pS p.
Proof. induction p as [|p IH|p IH]; simpl; rewrite ?IH; done. Qed.

Fixpoint fb (p : proto) : expr :=
  match p with
  | PEnd => LetU (EClose (Var 1)) (EClose (Var 0))
  | PRcv q => LetP (ERecv (Var 1)) (ELet (ESend (Pair (Var 1) (Var 2))) (fb q))
  | PSnd q => LetP (ERecv (Var 0)) (ELet (ESend (Pair (Var 1) (Var 3))) (LetP (Pair (Var 0) (Var 1)) (fb q)))
  end.

Fixpoint ffp (W : sworld) (Γ : hctx) (p : proto) (x y : point) : Prop :=
  match p with
  | PEnd => slt W Γ x (y‾)
  | PRcv q => slt W Γ x (y‾) ∧ slt W Γ y (x⁺‾) ∧ ffp W Γ q (x⁺) (y⁺)
  | PSnd q => slt W Γ y (x‾) ∧ slt W Γ x (y⁺‾) ∧ ffp W Γ q (x⁺) (y⁺)
  end.

Ltac hz_go := repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst; try contradiction.

Lemma fb_dftyped W Γ p : ∀ n x y, ffp W Γ p x y →
  dftyped W ∅ Γ (Some (TSess (pS (pdual p)) y None None) :: Some (TSess (pS p) x None None) :: nones n)
    (∅, None) (fb p) TUnit.
Proof.
  induction p as [|p IH|p IH]; intros n x y Hf; cbn [fb pS pdual ffp] in *.
  - eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := x); [reflexivity| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done. }
    eapply d_close with (S0 := SEnd) (x := y); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|spare_tac].
  - destruct Hf as (H0 & H1 & Hq).
    eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 1)) EUnit| |].
    { eapply d_recv with (S0 := SSeq (SRcv 0 TUnit) (pS p)) (x := x) (m := 0) (T := TUnit) (S := pS p);
        [reflexivity|exact I| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done. }
    eapply d_let; [apply tsplit_empty|lsplit_tac (ESend (Pair (Var 1) (Var 2))) EUnit| |].
    { eapply d_send with (S0 := SSeq (SSnd 0 TUnit) (pS (pdual p))) (x := y) (m := 0) (T := TUnit) (S := pS (pdual p));
        [reflexivity|exact I|reflexivity|cbn; set_solver| |].
      - apply ub_below_nil; [bot_false|]. intros z Hz.
        rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done.
      - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 1) (Var 2)| |].
        + eapply d_var'; [reflexivity|]. spare_tac.
        + eapply d_var'; [reflexivity|]. spare_tac. }
    exact (IH (3 + n) (x⁺) (y⁺) Hq).
  - destruct Hf as (H0 & H1 & Hq).
    eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 0)) EUnit| |].
    { eapply d_recv with (S0 := SSeq (SRcv 0 TUnit) (pS (pdual p))) (x := y) (m := 0) (T := TUnit) (S := pS (pdual p));
        [reflexivity|exact I| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done. }
    eapply d_let; [apply tsplit_empty|lsplit_tac (ESend (Pair (Var 1) (Var 3))) EUnit| |].
    { eapply d_send with (S0 := SSeq (SSnd 0 TUnit) (pS p)) (x := x) (m := 0) (T := TUnit) (S := pS p);
        [reflexivity|exact I|reflexivity|cbn; set_solver| |].
      - apply ub_below_nil; [bot_false|]. intros z Hz.
        rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done.
      - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 1) (Var 3)| |].
        + eapply d_var'; [reflexivity|]. spare_tac.
        + eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Pair (Var 0) (Var 1)) EUnit| |].
    { eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 0) (Var 1)| |].
      + eapply d_var'; [reflexivity|]. spare_tac.
      + eapply d_var'; [reflexivity|]. spare_tac. }
    exact (IH (5 + n) (x⁺) (y⁺) Hq).
  Unshelve. all: exact None.
Qed.

(** *** The schema as a process

    [fwdp p o1 o2] binds the two ends and runs [fb p]. Its world [W_p p]
    holds exactly the facts p generates at the constant roots of [px] and
    [py]. The world is well-founded: at offset k the end that acts first
    in p gets the lower potential, and every other fact raises the
    offset. *)

Definition fwdp_t (p : proto) (o1 o2 : cend) : expr := LetP (Pair (Chan o1) (Chan o2)) (fb p).

Lemma fwdp_dftyped W Γ p o1 o2 x y : o1 ≠ o2 → ffp W Γ p x y →
  dftyped W ({[o1 := TE (pS p) x None None]} ∪ {[o2 := TE (pS (pdual p)) y None None]}) Γ [] (∅, None)
    (fwdp_t p o1 o2) TUnit.
Proof.
  intros Ho Hf. unfold fwdp_t.
  eapply d_letp with (Θ2 := ∅); [split; [apply map_disjoint_empty_r|by rewrite map_union_empty]|apply lsplit_nil| |].
  { eapply d_pair with (Θ1 := {[o1 := TE (pS p) x None None]}) (Θ2 := {[o2 := TE (pS (pdual p)) y None None]});
      [split; [by apply map_disjoint_singleton_l_2; rewrite lookup_singleton_ne|reflexivity]
                   |apply lsplit_nil| |]; apply d_chan, spare_unl; spare_tac. }
  exact (fb_dftyped W Γ p 0 x y Hf).
  Unshelve. all: exact None.
Qed.

Fixpoint ffacts (p : proto) (x y : point) (g : fact) : Prop :=
  match p with
  | PEnd => g = FLt x (y‾)
  | PRcv q => g = FLt x (y‾) ∨ g = FLt y (x⁺‾) ∨ ffacts q (x⁺) (y⁺) g
  | PSnd q => g = FLt y (x‾) ∨ g = FLt x (y⁺‾) ∨ ffacts q (x⁺) (y⁺) g
  end.

Lemma ffacts_ffp W Γ p : ∀ x y, (∀ g, ffacts p x y g → sw_facts W g) → ffp W Γ p x y.
Proof.
  induction p as [|p IH|p IH]; intros x y H; cbn [ffp ffacts] in *.
  - apply sl_w, sw_lt_fact, H. done.
  - split_and!; [apply sl_w, sw_lt_fact, H; tauto|apply sl_w, sw_lt_fact, H; tauto|].
    apply IH. intros g Hg. apply H. tauto.
  - split_and!; [apply sl_w, sw_lt_fact, H; tauto|apply sl_w, sw_lt_fact, H; tauto|].
    apply IH. intros g Hg. apply H. tauto.
Qed.

Lemma ffacts_roots p : ∀ x y u v, ffacts p x y (FLt u v) →
  (pt_root u = pt_root x ∨ pt_root u = pt_root y) ∧ (pt_root v = pt_root x ∨ pt_root v = pt_root y).
Proof.
  induction p as [|p IH|p IH]; intros x y u v H; cbn [ffacts] in H.
  - injection H as -> ->. unfold pt_root. simpl. tauto.
  - destruct H as [H|[H|H]]; [injection H as -> ->; unfold pt_root; simpl; tauto
      |injection H as -> ->; unfold pt_root; simpl; tauto|].
    apply IH in H. unfold pt_root in *. simpl in *. exact H.
  - destruct H as [H|[H|H]]; [injection H as -> ->; unfold pt_root; simpl; tauto
      |injection H as -> ->; unfold pt_root; simpl; tauto|].
    apply IH in H. unfold pt_root in *. simpl in *. exact H.
Qed.

Definition W_p (p : proto) : sworld := SWorld ({[0]} ∪ {[1]}) (ffacts p px py).

Lemma W_p_wf p : sworld_wf (W_p p).
Proof.
  split; simpl. intros u v H. apply ffacts_roots in H as [Hu Hv].
  unfold croot_in. split.
  - destruct Hu as [Hu|Hu]; [exists 0|exists 1]; rewrite Hu; split; [done|set_solver|done|set_solver].
  - destruct Hv as [Hv|Hv]; [exists 0|exists 1]; rewrite Hv; split; [done|set_solver|done|set_solver].
Qed.

(** Does the end at x act first at offset k? *)
Fixpoint pfirst (p : proto) (k : nat) : bool :=
  match p, k with
  | PEnd, _ => true
  | PRcv _, 0 => true
  | PSnd _, 0 => false
  | PRcv q, S k | PSnd q, S k => pfirst q k
  end.

Definition pbit (f : nat → bool) (u : point) : nat :=
  match pt_name u with
  | NConst 0 => if f (pt_off u) then 0 else 1
  | NConst 1 => if f (pt_off u) then 1 else 0
  | _ => 0
  end.

Definition ppot (f : nat → bool) (u : point) : nat := 2 * pt_off u + pbit f u.

Lemma pbit_le f u : pbit f u ≤ 1.
Proof. unfold pbit. repeat case_match; lia. Qed.

Definition XP (k : nat) : point := MkPt (NConst 0) true k.
Definition YP (k : nat) : point := MkPt (NConst 1) true k.

Lemma ffacts_ppot p : ∀ k f u v, (∀ j, f (k + j) = pfirst p j) →
  ffacts p (XP k) (YP k) (FLt u v) → ppot f u < ppot f v.
Proof.
  induction p as [|p IH|p IH]; intros k f u v Hf H; cbn [ffacts] in H.
  - injection H as -> ->. specialize (Hf 0). rewrite Nat.add_0_r in Hf. simpl in Hf.
    unfold ppot, pbit. simpl. rewrite Hf. lia.
  - destruct H as [H|[H|H]].
    + injection H as -> ->. specialize (Hf 0). rewrite Nat.add_0_r in Hf. simpl in Hf.
      unfold ppot, pbit. simpl. rewrite Hf. lia.
    + injection H as -> ->. unfold ppot. pose proof (pbit_le f (YP k)).
      pose proof (pbit_le f (XP k)⁺‾). simpl. lia.
    + apply (IH (k + 1)); [|exact H]. intros j. rewrite <-Nat.add_assoc. rewrite (Hf (1 + j)). done.
  - destruct H as [H|[H|H]].
    + injection H as -> ->. specialize (Hf 0). rewrite Nat.add_0_r in Hf. simpl in Hf.
      unfold ppot, pbit. simpl. rewrite Hf. lia.
    + injection H as -> ->. unfold ppot. pose proof (pbit_le f (XP k)).
      pose proof (pbit_le f (YP k)⁺‾). simpl. lia.
    + apply (IH (k + 1)); [|exact H]. intros j. rewrite <-Nat.add_assoc. rewrite (Hf (1 + j)). done.
Qed.

Lemma W_p_step p u v : swstep (W_p p) u v → ppot (pfirst p) u < ppot (pfirst p) v.
Proof.
  intros Hs. destruct Hs as [u v H|u|u].
  - simpl in H. apply (ffacts_ppot p 0); [done|exact H].
  - unfold ppot. cbn [pt_shift pt_name pt_off]. pose proof (pbit_le (pfirst p) u).
    pose proof (pbit_le (pfirst p) u⁺). lia.
  - unfold ppot. cbn [pt_shift pt_dual pt_name pt_off]. pose proof (pbit_le (pfirst p) u).
    pose proof (pbit_le (pfirst p) u‾⁺). lia.
Qed.

Lemma W_p_lt p u v : W_p p ⊢ₛ u ≺ v → ppot (pfirst p) u < ppot (pfirst p) v.
Proof.
  intros H. induction H as [u v H|u v w H _ IH]; [by apply W_p_step|]. apply W_p_step in H. lia.
Qed.

Lemma W_p_swf p : swf (W_p p).
Proof.
  apply swf_iff.
  assert (∀ m u, ppot (pfirst p) u = m → Acc (sw_lt (W_p p)) u) as Hacc.
  { intros m. induction m as [m IH] using lt_wf_ind. intros u <-. constructor.
    intros v Hv. eapply IH; [apply W_p_lt, Hv|done]. }
  intros u. by apply (Hacc (ppot (pfirst p) u)).
Qed.

Lemma W_p_facts p : ffp (W_p p) hc_empty p px py.
Proof. apply ffacts_ffp. intros g Hg. exact Hg. Qed.

Definition Σp (p : proto) : senv := {[o1 := (pS p, px)]} ∪ {[o2 := (pS (pdual p), py)]}.

Lemma Σp_pfree p : pfree (Σp p).
Proof.
  intros o Ho Hn. unfold Σp in Ho, Hn. rewrite dom_union_L, !dom_singleton_L in Ho, Hn.
  set_unfold in Ho; set_unfold in Hn. destruct Ho as [->| ->]; simpl in Hn; destruct Hn; discriminate.
Qed.

Theorem fwdp_term p : fptyped None (W_p p) (Σp p) (∅, {[+ fwdp_t p o1 o2 +]}) TUnit.
Proof.
  apply (fp_term None (W_p p) (Σp p) ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply Σp_pfree.
  - intros o e He. unfold Σp in He. apply lookup_union_Some_raw in He as [He|[_ He]];
      apply lookup_singleton_Some in He as [_ <-]; apply pS_contr.
  - set_solver.
  - change (fhalf None) with (None : fuel).
    assert (tenv_of None (Σp p) ∪ ∅ =
      tenv_df ({[o1 := TE (pS p) px None None]} ∪ {[o2 := TE (pS (pdual p)) py None None]})) as ->.
    { rewrite map_union_empty. unfold tenv_of, tenv_df, Σp. rewrite !map_fmap_union, !map_fmap_singleton.
      unfold tentry_df. cbn [te_sty te_pt fst snd]. by rewrite !sty_df_pS. }
    exact (fwdp_dftyped _ _ p o1 o2 px py o1_o2 (W_p_facts p)).
  - split; [apply W_p_wf|apply swf_wok, W_p_swf].
Qed.

(** *** Identity expansion for every first-order protocol

    The argument of [fwd_expand] with the potential [ppot]: between two
    points on the root of x the schema's world holds only program order,
    so P ∥ fwdp types whenever P types and its world does not know the
    root of y. *)

Lemma pdual_pdual p : pdual (pdual p) = p.
Proof. induction p as [|p IH|p IH]; simpl; rewrite ?IH; done. Qed.

Lemma ppot_off f u v : pt_name u = pt_name v → pt_off u < pt_off v → ppot f u < ppot f v.
Proof.
  intros Hn Ho. unfold ppot. pose proof (pbit_le f u). pose proof (pbit_le f v). lia.
Qed.

Lemma ffacts_names p : ∀ x y u v, ffacts p x y (FLt u v) →
  (pt_name u = pt_name x ∨ pt_name u = pt_name y) ∧ (pt_name v = pt_name x ∨ pt_name v = pt_name y).
Proof.
  induction p as [|p IH|p IH]; intros x y u v H; cbn [ffacts] in H.
  - injection H as -> ->. simpl. tauto.
  - destruct H as [H|[H|H]]; [injection H as -> ->; simpl; tauto|injection H as -> ->; simpl; tauto|].
    apply IH in H. simpl in H. exact H.
  - destruct H as [H|[H|H]]; [injection H as -> ->; simpl; tauto|injection H as -> ->; simpl; tauto|].
    apply IH in H. simpl in H. exact H.
Qed.

Lemma W_p_lt_inv p u v : W_p p ⊢ₛ u ≺ v →
  po u v ∨ (nm01 u ∧ nm01 v ∧ ppot (pfirst p) u < ppot (pfirst p) v).
Proof.
  assert (∀ u v, swstep (W_p p) u v → po u v ∨ (nm01 u ∧ nm01 v ∧ ppot (pfirst p) u < ppot (pfirst p) v)) as Hs.
  { intros u' v' H. pose proof (W_p_step _ _ _ H) as Hp.
    destruct H as [u' v' H|u'|u'].
    - right. simpl in H. apply ffacts_names in H as [Hu Hv]. unfold nm01. simpl in Hu, Hv. tauto.
    - left. by apply tc_once; left.
    - left. by apply tc_once; right. }
  induction 1 as [u v H|u v w H _ IH]; [by apply Hs|].
  apply Hs in H. destruct H as [H|(Hu & Hv & H)], IH as [IH|(Hv' & Hw & IH)].
  - left. by eapply po_trans.
  - right. destruct (po_name _ _ H) as [Hn Ho]. split_and!; [unfold nm01; by rewrite Hn|done|].
    pose proof (ppot_off (pfirst p) u v Hn Ho). lia.
  - right. destruct (po_name _ _ IH) as [Hn Ho]. split_and!; [done|unfold nm01; by rewrite <-Hn|].
    pose proof (ppot_off (pfirst p) v w Hn Ho). lia.
  - right. split_and!; [done|done|lia].
Qed.

Lemma W_p_lt_root0 p u v : W_p p ⊢ₛ u ≺ v → pt_root u = NConst 0 → pt_root v = NConst 0 → po u v.
Proof.
  intros H Hu Hv. destruct (W_p_lt_inv _ _ _ H) as [Hp|(Hu' & Hv' & Hlt)]; [done|].
  assert (pt_name u = NConst 0) as Hu0.
  { destruct Hu' as [E|E]; [done|]. unfold pt_root in Hu. rewrite E in Hu. discriminate. }
  assert (pt_name v = NConst 0) as Hv0.
  { destruct Hv' as [E|E]; [done|]. unfold pt_root in Hv. rewrite E in Hv. discriminate. }
  apply po_of_off; [by rewrite Hu0, Hv0|].
  unfold ppot, pbit in Hlt. rewrite Hu0, Hv0 in Hlt.
  destruct (decide (pt_off u < pt_off v)) as [?|Hge]; [done|]. exfalso.
  destruct (decide (pt_off u = pt_off v)) as [E|Hne].
  - rewrite E in Hlt. lia.
  - destruct (pfirst p (pt_off u)), (pfirst p (pt_off v)); lia.
Qed.

Lemma cut_W_p_wok N p W : wok N W → 1 ∉ sw_consts W →
  wok N (swrestrict W (swshared W (W_p p)) ⊔ swrestrict (W_p p) (swshared W (W_p p))).
Proof.
  intros HW H1. eapply (wok_sub N); [|exact HW].
  assert (∀ u v, swstep (swrestrict W (swshared W (W_p p)) ⊔ swrestrict (W_p p) (swshared W (W_p p))) u v →
            W ⊢ₛ u ≺ v) as Hs.
  { intros u v Hs. apply swstep_join_inv in Hs as [Hs|Hs].
    - apply (swrestrict_lt W (swshared W (W_p p))). by apply tc_once.
    - destruct Hs as [u v (Hlt & (a & Ha & Has) & (b & Hb & Hbs))|u|u];
        [|apply sw_lt_po|apply sw_lt_dpo].
      apply po_slt, (W_p_lt_root0 p); [done| |].
      + unfold swshared in Has. simpl in Has. assert (a = 0) as -> by set_solver. done.
      + unfold swshared in Hbs. simpl in Hbs. assert (b = 0) as -> by set_solver. done. }
  intros u v H. induction H as [u v H|u v w H _ IH]; [by apply Hs|].
  eapply sw_lt_trans; [by apply Hs|exact IH].
Qed.

Definition Σxp (p : proto) : senv := {[edual o1 := (pS (pdual p), px‾)]}.
Definition Σyp (p : proto) : senv := {[o2 := (pS (pdual p), py)]}.

Lemma Σxp_dual p : senv_dual (Σxp p) = {[o1 := (pS p, px)]}.
Proof.
  unfold senv_dual, Σxp. rewrite map_fmap_singleton, kmap_singleton by apply _. simpl.
  by rewrite pS_dual, pdual_pdual, ?pt_dual_dual.
Qed.

Theorem fwdp_expand p W Σ C E T :
  fptyped None W (Σ ∪ Σxp p) (C, E) T →
  Σ ##ₘ Σxp p → "a" ∉ chans_of Σ → "b" ∉ chans_of Σ → "b" ∉ C → 1 ∉ sw_consts W →
  fptyped None (W ⊔ W_p p) (Σ ∪ Σyp p) (C ∪ ∅ ∪ {["a"]}, E ⊎ {[+ fwdp_t p o1 o2 +]}) T.
Proof.
  intros HP HΣ Ha Hb HbC H1.
  assert (chans_of (Σxp p) = {["a"]}) as Ex by (unfold Σxp; by rewrite chans_single).
  assert (chans_of (Σyp p) = {["b"]}) as Ey by (unfold Σyp; by rewrite chans_single).
  pose proof (fptyped_chans _ _ _ _ _ HP) as HC. simpl in HC.
  rewrite chans_of_union, Ex in HC.
  pose proof (fp_connect None W (W_p p) Σ (Σyp p) (Σxp p) C ∅ E {[+ fwdp_t p o1 o2 +]} T) as H.
  rewrite Ex in H. apply H; clear H.
  - exact HP.
  - assert (Σyp p ∪ senv_dual (Σxp p) = Σp p) as ->.
    { rewrite Σxp_dual. unfold Σyp, Σp. apply map_union_comm.
      apply map_disjoint_singleton_l_2. by rewrite lookup_singleton_ne. }
    apply fwdp_term.
  - exact HΣ.
  - rewrite Σxp_dual. unfold Σyp. apply map_disjoint_singleton_l_2. by rewrite lookup_singleton_ne.
  - intros o. unfold Σxp. rewrite dom_singleton_L, !elem_of_singleton. intros ->. discriminate.
  - rewrite ?Ey, ?Ex. set_solver.
  - rewrite ?Ey, ?Ex. set_solver.
  - rewrite ?Ey, ?Ex. set_solver.
  - set_solver.
  - rewrite ?Ey, ?Ex. set_solver.
  - set_solver.
  - apply cut_W_p_wok; [apply (fptyped_wf _ _ _ _ _ HP)|done].
Qed.

(** The schema is semantically sound at every protocol: the fundamental
    theorem puts the forwarder process in the relation at every strict
    world that models its static world, and such a world exists. *)
Corollary fwdp_sem p R : wmodels R (W_p p) → wstrict R → Σp p ⊨_R (∅, {[+ fwdp_t p o1 o2 +]}) : TUnit.
Proof. intros HR HS. exact (fundamental_proc (W_p p) R _ _ _ (fwdp_term p) HR HS). Qed.

Lemma W_p_models p : ∃ R, wstrict R ∧ wmodels R (W_p p).
Proof. apply dmodels_exists; [apply W_p_wf|apply swf_sacyc, W_p_swf]. Qed.

(** The concrete forwarder is the schema at ?∗.!∗.Close. *)
Lemma pS_S1 : pS (PRcv (PSnd PEnd)) = S1.
Proof. reflexivity. Qed.

Lemma ffp_S1 W Γ x y : ffp W Γ (PRcv (PSnd PEnd)) x y ↔ fwd_facts W Γ x y.
Proof. unfold fwd_facts. simpl. tauto. Qed.
