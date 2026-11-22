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
