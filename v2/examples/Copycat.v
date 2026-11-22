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
