(** * cycle (proposal Appendix B.1)

      cycle = let (c, c′) = new_0 in
              let (c, ⟨d, d′⟩) = new_0 c in
              let () = spawn (λu. let () = u in let () = close c′ in close d′) in
              let () = close c in close d

    c, c′ sit at ρ and ρ‾ for a fresh root ρ, and d, d′ at the field ρ·0
    and (ρ·0)‾. Main closes c while it holds d, so it needs ρ ≺ (ρ·0)‾.
    The thunk closes c′ while it holds d′, so it needs ρ‾ ≺ ρ·0. The
    constraint of the first creation states exactly these two facts. *)

From GV Require Export examples.Tools2.

(** The constraint of the first creation over the new root ι₀. *)
Definition cy_L (g : fact) : Prop :=
  g = FLt (pvar 0) ((pvar 0)·0)‾ ∨ g = FLt (pvar 0)‾ ((pvar 0)·0).

Definition W_cy : sworld := sw_empty.

Lemma cy_wf_new : wf_new (bcs_of cy_L).
Proof.
  apply (wf_new_lex3 _ (λ x, (pt_depth x, pt_off x, 0))).
  - intros x y [E|E]; injection E as -> ->; split; reflexivity.
  - intros x. unfold lex3, pt_depth. simpl. lia.
  - intros x y [E|E]; injection E as -> ->; unfold lex3, pt_depth; simpl; lia.
Qed.
#[global] Hint Resolve cy_wf_new : wfnew.

Lemma W_cy_wf : sworld_wf W_cy ∧ swf W_cy.
Proof. apply sw_empty_ok. Qed.

Definition cy_thunk : expr := Lam (LetU (Var 0) (LetU (EClose (Var 5)) (EClose (Var 1)))).

Definition cy_main : expr :=
  let_new (LetP (Pair (Var 1) ENew) (LetP (Var 0)
    (LetU (ESpawn cy_thunk) (LetU (EClose (Var 3)) (EClose (Var 1)))))).

Abbreviation Γc := (Γnew cy_L).

Lemma cy_law1 : slt W_cy Γc (pvar 0) ((pvar 0)·0)‾.
Proof. eapply (law_slt _ _ (FLt (pvar 0) ((pvar 0)·0)‾)); [by left|simpl; lia|fact_eq]. Qed.

Lemma cy_law2 : slt W_cy Γc (pvar 0)‾ ((pvar 0)·0).
Proof. eapply (law_slt _ _ (FLt (pvar 0)‾ ((pvar 0)·0))); [by right|simpl; lia|fact_eq]. Qed.

Theorem cy_dftyped : dftyped W_cy ∅ hc_empty [] (∅, None) cy_main TUnit.
Proof.
  unfold cy_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ SEnd None None); [spare_tac|apply cy_wf_new|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew cy_L).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Pair (Var 1) ENew) EUnit| |].
  { eapply (d_new_at _ _ _ _ _ _ 0 SEnd (pvar 0) SEnd); [done|reflexivity| |contr_tac]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn cy_thunk) EUnit| |].
  - eapply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 5)) EUnit| |].
    + eapply d_close with (S0 := SEnd) (x := (pvar 0)‾); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy.
      rewrite pt_dual_dual. apply cy_law2.
    + eapply d_close with (S0 := SEnd) (x := ((pvar 0)·0)‾); [done|apply ub_below_empty|].
      eapply d_var'; [reflexivity|]. spare_tac.
  - eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 3)) EUnit| |].
    + eapply d_close with (S0 := SEnd) (x := pvar 0); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. apply cy_law1.
    + eapply d_close with (S0 := SEnd) (x := (pvar 0)·0); [done|apply ub_below_empty|].
      eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Theorem cy_typed : typed W_cy None ∅ hc_empty [] (∅, None) cy_main TUnit None.
Proof. apply (dftyped_typed _ _ _ _ _ _ _ cy_dftyped). Qed.
