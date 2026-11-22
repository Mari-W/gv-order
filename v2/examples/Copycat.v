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

    No rule changes. *)

From GV Require Export examples.SemBranch examples.Tools2.
From GV Require Import static.Inversion.

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

Definition sh := pt_shift.

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

Lemma fwd_term : ptyped None W_f Σf (∅, {[+ fwd_t o1 o2 +]}) TUnit.
Proof.
  apply (p_term None W_f Σf ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply Σf_pfree.
  - intros o e He. unfold Σf in He. apply lookup_union_Some_raw in He as [He|[_ He]];
      apply lookup_singleton_Some in He as [_ <-]; [apply S1_contr|apply S1_dual_contr].
  - set_solver.
  - change (fhalf None) with (None : fuel). rewrite Θf_of, <-Θf_df.
    exact (fwd_dftyped W_f hc_empty o1 o2 px py o1_o2 W_f_facts).
  - apply W_f_ok.
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

Lemma cut_W_f_swf W : swf W → 1 ∉ sw_consts W →
  swf (swrestrict W (swshared W W_f) ⊔ swrestrict W_f (swshared W W_f)).
Proof.
  intros HW H1. apply swf_iff. apply swf_iff in HW. eapply wf_sub; [|exact HW].
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
  ptyped None W (Σ ∪ Σx) (C, E) T →
  Σ ##ₘ Σx → "a" ∉ chans_of Σ → "b" ∉ chans_of Σ → "b" ∉ C → 1 ∉ sw_consts W →
  ptyped None (W ⊔ W_f) (Σ ∪ Σy) (C ∪ ∅ ∪ {["a"]}, E ⊎ {[+ fwd_t o1 o2 +]}) T.
Proof.
  intros HP HΣ Ha Hb HbC H1.
  pose proof (ptyped_chans _ _ _ _ _ HP) as HC. simpl in HC.
  rewrite chans_of_union, chans_Σx in HC.
  pose proof (p_connect None W W_f Σ Σy Σx C ∅ E {[+ fwd_t o1 o2 +]} T) as H.
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
  - apply cut_W_f_swf; [apply (ptyped_wf _ _ _ _ _ HP)|done].
Qed.

(** ** A closed run: partner ∥ fwd ∥ partner, deadlock free

    The partner of o1 is typed alone over the empty world, [fwd_expand]
    puts the forwarder behind it, and P-Connect adds the partner of o2.
    The fundamental theorem gives deadlock freedom ([soundness]). *)

Lemma p1_term : ptyped None sw_empty Σx (∅, {[+ p1_t (edual o1) +]}) TUnit.
Proof.
  apply (p_term None sw_empty Σx ∅ ∅ _ TUnit None).
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
  - apply sw_empty_ok.
Qed.

Lemma p2_term : ptyped None sw_empty (senv_dual Σy) (∅, {[+ p2_t (edual o2) +]}) TUnit.
Proof.
  assert (senv_dual Σy = {[edual o2 := (S1, py‾)]}) as ->.
  { unfold senv_dual, Σy. rewrite map_fmap_singleton, kmap_singleton by apply _. simpl.
    by rewrite ?dual_involutive. }
  apply (p_term None sw_empty _ ∅ ∅ _ TUnit None).
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
  - apply sw_empty_ok.
Qed.

Definition fwd_config : proc :=
  ({["a"]} ∪ {["b"]}, ({[+ p1_t (edual o1) +]} ⊎ {[+ fwd_t o1 o2 +]}) ⊎ {[+ p2_t (edual o2) +]}).

Definition W_run : sworld := (sw_empty ⊔ W_f) ⊔ sw_empty.

Theorem fwd_config_typed : ptyped None W_run ∅ fwd_config TUnit.
Proof.
  assert (ptyped None (sw_empty ⊔ W_f) (∅ ∪ Σy) (∅ ∪ ∅ ∪ {["a"]}, {[+ p1_t (edual o1) +]} ⊎ {[+ fwd_t o1 o2 +]}) TUnit)
    as H1.
  { apply fwd_expand.
    - rewrite (left_id_L ∅ (∪)). apply p1_term.
    - apply map_disjoint_empty_l.
    - unfold chans_of. rewrite dom_empty_L. set_solver.
    - unfold chans_of. rewrite dom_empty_L. set_solver.
    - set_solver.
    - simpl. set_solver. }
  rewrite (left_id_L ∅ (∪)) in H1.
  pose proof (p_connect None (sw_empty ⊔ W_f) sw_empty ∅ ∅ Σy (∅ ∪ ∅ ∪ {["a"]}) ∅
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
  - apply swf_bare. intros [u v] [Hf|Hf]; simpl in Hf; destruct Hf as (_ & (a & _ & Ha) & _);
      unfold swshared in Ha; simpl in Ha; set_solver.
Qed.

Theorem fwd_config_deadlock_free : deadlock_free fwd_config.
Proof. exact (soundness W_run fwd_config TUnit fwd_config_typed). Qed.
