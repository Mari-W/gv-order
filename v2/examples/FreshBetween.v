(** * A channel created between two box arguments (old FreshBetween.v)

      between : □(∀ι κ. C. ∗ ⊸ Close@ι ⊗ Close@κ ⊸^κ ∗)
      between = !(f = λp. let (c, e) = p in
                          let (c, ⟨d, d′⟩) = new_0 c in
                          let () = spawn (λu. let () = u in close d′) in
                          let () = close c in let () = close d in close e)

    d sits at the field δ = ι·0 of c and d′ at δ‾. close c blocks at ι
    while the thread holds d and e, close d at δ while it holds e, and
    the upper point κ bounds both. The constraint is the old [fbx_C]
    with the field ι·0 for δ:
      C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾, δ ≺ κ, δ ≺ κ‾}.
    main creates c by new_0 at a fresh root ρ, e by new_1 c at ρ·1, and
    forces the box at (ρ, ρ·1). The laws Λ_0(r) are C at (r, r·1). *)

From GV Require Export examples.Tools2.

Abbreviation fbd := ((pvar 0)·0).

Definition fbx_P (g : fact) : Prop :=
  g = FLt (pvar 0) (pvar 1) ∨ g = FLt (pvar 0) (pvar 1)‾ ∨ g = FLt (pvar 0) fbd‾ ∨
  g = FLt fbd (pvar 1) ∨ g = FLt fbd (pvar 1)‾.
Definition fb_C : bcs := BCs [] fbx_P.

Definition fb_T : ty := TProd (TSess SEnd (pvar 0) None None) (TSess SEnd (pvar 1) None None).
Definition fb_ty : ty := box1 2 fb_C (pvar 1) fb_T.

Definition fb_box : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Pair (Var 1) ENew) (LetP (Var 0)
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
    (LetU (EClose (Var 3)) (LetU (EClose (Var 1)) (EClose (Var 4))))))))).

Ltac fb_disj :=
  first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
        | right; right; right; left; reflexivity | right; right; right; right; reflexivity ].

Section body.
  Context (W : sworld) (Γ : hctx) (n : nat).
  Local Abbreviation Γb := (Γbox 2 fb_C (pvar 1) Γ).

  Lemma fb_hyp x y : fbx_P (FLt x y) → fact_scoped 2 (FLt x y) → slt W Γb x y.
  Proof. intros Hf Hs. eapply (hyp_slt_ids _ _ fbx_P 2); [exact (Γbox_in 2 fb_C (pvar 1) Γ)|done|done]. Qed.

  Ltac fbf := apply fb_hyp; [unfold fbx_P; fb_disj|simpl; lia].

  Lemma fb_body :
    dftyped W ∅ Γb (Some fb_T :: Some fb_ty :: nones n) (∅, Some (RAbove (pvar 1)))
      (LetP (Var 0) (LetP (Pair (Var 1) ENew) (LetP (Var 0)
        (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
        (LetU (EClose (Var 3)) (LetU (EClose (Var 1)) (EClose (Var 4))))))))
      TUnit.
  Proof.
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Pair (Var 1) ENew) EUnit| |].
    { eapply (d_new_at _ _ _ _ _ _ 0 SEnd (pvar 0) SEnd); [done|reflexivity| |contr_tac]. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| |].
    { eapply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_close with (S0 := SEnd) (x := fbd‾); [done|apply ub_below_empty|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 3)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := pvar 0); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply (ub_below_varb _ _ _ (pvar 1) _ _); [bot_false| |right; fbf].
      intros y Hy. heads_cases Hy; fbf. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := fbd); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply (ub_below_varb _ _ _ (pvar 1) _ _); [bot_false| |right; fbf].
      intros y Hy. heads_cases Hy; fbf. }
    eapply d_close with (S0 := SEnd) (x := pvar 1); [done| |eapply d_var'; [reflexivity|spare_tac]].
    apply (ub_below_var _ _ _ (pvar 1) _); [set_solver|by left].
    Unshelve. all: exact None.
  Qed.
End body.

Lemma fb_box_typed W Γ n F : dftyped W ∅ Γ (nones n) F fb_box fb_ty.
Proof. apply box1_typed; [contr_tac|reflexivity|apply fb_body]. Qed.

(** ** main *)

Definition fb_xs : list point := pvar 0 :: (pvar 0)·1 :: [].

Definition fb_L (g : fact) : Prop := ∃ f, fbx_P f ∧ g = fact_map (pt_inst (plist fb_xs)) f.

Definition W_fb : sworld := sw_empty.

Lemma fb_wf_new : wf_new (bcs_of fb_L).
Proof.
  apply (wf_new_lex3 _ (λ x, (pt_fsum x, pt_off x, pt_depth x))).
  - intros x y (f & Hf & E).
    destruct Hf as [->|[->|[->|[->| ->]]]]; simpl in E; injection E as -> ->; split; reflexivity.
  - intros x. unfold lex3, pt_fsum, pt_depth. simpl. lia.
  - intros x y (f & Hf & E).
    destruct Hf as [->|[->|[->|[->| ->]]]]; simpl in E; injection E as -> ->; unfold pt_fsum, pt_depth; simpl; lia.
Qed.
#[global] Hint Resolve fb_wf_new : wfnew.

Lemma W_fb_wf : sworld_wf W_fb ∧ swf W_fb.
Proof. apply sw_empty_ok. Qed.


Definition fb_main : expr :=
  let_new (LetP (Pair (Var 1) ENew) (LetP (Var 0)
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 5)))))
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
      (App (EForce fb_box) (Pair (Var 3) (Var 1))))))).

Lemma fb_force n F e :
  dftyped W_fb ∅ (Γnew fb_L) (nones n) F e fb_ty →
  dftyped W_fb ∅ (Γnew fb_L) (nones n) F (EForce e)
    (TLolli (UPt ((pvar 0)·1)) LNone None (TProd (TSess SEnd (pvar 0) None None) (TSess SEnd ((pvar 0)·1) None None)) TUnit None).
Proof.
  intros H.
  assert (sinst_ty (slist []) (ty_inst fb_xs
            (TLolli (UPt (pvar 1)) LNone None fb_T TUnit None)) =
    TLolli (UPt ((pvar 0)·1)) LNone None (TProd (TSess SEnd (pvar 0) None None) (TSess SEnd ((pvar 0)·1) None None)) TUnit None) as <-.
  { rewrite sinst_nil. reflexivity. }
  eapply d_force with (ub := None) (c := None) (C := fb_C);
    [done| |done|split; [split; apply Forall_nil|intros _; apply Forall_nil]|exact I|exact H].
  apply hold_at_nil. intros f Hf _.
  destruct (fact_map (pt_inst (plist fb_xs)) f) as [x y] eqn:E.
  apply law_slt'; [exists f; by rewrite E|].
  destruct Hf as [->|[->|[->|[->| ->]]]]; simpl in E; injection E as <- <-; simpl; lia.
Qed.

Theorem fb_dftyped : dftyped W_fb ∅ hc_empty [] (∅, None) fb_main TUnit.
Proof.
  unfold fb_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ SEnd None None); [spare_tac|apply fb_wf_new|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew fb_L).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Pair (Var 1) ENew) EUnit| |].
  { eapply (d_new_at _ _ _ _ _ _ 1 SEnd (pvar 0) SEnd); [done|reflexivity| |contr_tac]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 5))))) EUnit| |].
  { eapply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := (pvar 0)‾); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| |].
  { eapply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := ((pvar 0)·1)‾); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_app; [apply tsplit_empty|lsplit_tac (EForce fb_box) EUnit|apply ubu_below_empty| |].
  - apply (fb_force 7). by apply fb_box_typed.
  - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 3) EUnit| |].
    + eapply d_var'; [reflexivity|]. spare_tac.
    + eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Theorem fb_typed : typed W_fb None ∅ hc_empty [] (∅, None) fb_main TUnit None.
Proof. apply (dftyped_typed _ _ _ _ _ _ _ fb_dftyped). Qed.
