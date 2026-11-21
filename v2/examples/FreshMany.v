(** * A channel that acts several times between two points (old FreshMany.v)

      many : □(∀ι κ. C. ∗ ⊸ Close@ι ⊗ Close@κ ⊸^κ ∗)
      many = !(f = λp. let (c, e) = p in
                       let (c, ⟨d, d′⟩) = new_0 c in
                       let () = spawn (λu. let () = u in
                                           let (v, d′) = recv d′ in let () = v in
                                           let (w, d′) = recv d′ in let () = w in close d′) in
                       let () = close c in
                       let () = close (send ⟨∗, send ⟨∗, d⟩⟩) in close e)

    d : !∗.!∗.Close sits at δ = ι·0 and acts at δ, δ+1 and δ+2 while the
    thread holds e at κ. The constraint is the old infinite [fmx_C] with
    the field ι·0 for δ:
      C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾} ∪ {δ+k ≺ κ, δ+k ≺ κ‾ | k ∈ ℕ}.
    main is the main of FreshBetween.v, and the laws Λ_0(r) are C at
    (r, r·1). *)

From GV Require Export examples.Tools2.

Abbreviation fmd k := (pt_shift k ((pvar 0)·0)).

Definition fmx_P (g : fact) : Prop :=
  g = FLt (pvar 0) (pvar 1) ∨ g = FLt (pvar 0) (pvar 1)‾ ∨ g = FLt (pvar 0) (fmd 0)‾ ∨
  ∃ k, g = FLt (fmd k) (pvar 1) ∨ g = FLt (fmd k) (pvar 1)‾.
Definition fm_C : bcs := BCs [] fmx_P.

Definition Sd1 : sty := SSeq (SSnd 0 TUnit) SEnd.
Definition Sdd : sty := SSeq (SSnd 0 TUnit) Sd1.

Definition fm_T : ty := TProd (TSess SEnd (pvar 0) None None) (TSess SEnd (pvar 1) None None).
Definition fm_ty : ty := box1 2 fm_C (pvar 1) fm_T.

Definition fm_thunk : expr :=
  Lam (LetU (Var 0) (LetP (ERecv (Var 1)) (LetU (Var 1)
    (LetP (ERecv (Var 0)) (LetU (Var 1) (EClose (Var 0))))))).

Definition fm_e : expr :=
  LetP (Var 0) (LetP (ENewAt 0 (Var 1)) (LetP (Var 0)
    (LetU (ESpawn fm_thunk)
    (LetU (EClose (Var 3))
    (LetU (EClose (ESend (Pair EUnit (ESend (Pair EUnit (Var 1))))))
          (EClose (Var 4))))))).

Definition fm_box : expr := EBox (Lam fm_e).

Ltac fm_disj :=
  first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
        | right; right; right; eexists; left; reflexivity
        | right; right; right; eexists; right; reflexivity ].

Section body.
  Context (W : world) (Γ : hctx) (n : nat).
  Local Abbreviation Γb := (Γbox 2 fm_C (pvar 1) Γ).

  Lemma fm_hyp x y : fmx_P (FLt x y) → fact_scoped 2 (FLt x y) → slt W Γb x y.
  Proof. intros Hf Hs. eapply (hyp_slt_ids _ _ fmx_P 2); [exact (Γbox_in 2 fm_C (pvar 1) Γ)|done|done]. Qed.

  Ltac fmf := apply fm_hyp; [unfold fmx_P; fm_disj|simpl; lia].

  Ltac normF :=
    cbn [lenv_bot hbot orb]; rewrite ?lenv_bot_nones; unfold fm_ty, box1;
    cbn [hbot orb sf_unionb fst snd fs_var fs_bot].

  Ltac fut x :=
    apply (ub_below_gen _ _ x (pvar 1));
      [ let y := fresh "y" in let Hy := fresh "Hy" in
        intros y Hy; revert Hy; normF; intros Hy; heads_cases Hy; fmf
      | normF; reflexivity  | right; fmf | normF; reflexivity ].

  Lemma fm_body :
    dftyped W ∅ Γb (Some fm_T :: Some fm_ty :: nones n) (∅, Some (FRest (RAbove (pvar 1)))) fm_e TUnit.
  Proof.
    unfold fm_e.
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (ENewAt 0 (Var 1)) EUnit| |].
    { eapply (d_new_at _ _ _ _ _ _ 0 SEnd (pvar 0) Sdd). eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn fm_thunk) EUnit| |].
    { (* the thunk receives twice on d′ and closes it *)
      eapply d_spawn_lam. unfold fm_thunk.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 1)) EUnit| |].
      { eapply d_recv with (x := (fmd 0)‾) (m := 0) (T := TUnit) (S0 := dual Sdd);
          [done|exact I| |eapply d_var'; [reflexivity|spare_tac]].
        apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. }
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 0)) EUnit| |].
      { eapply d_recv with (x := pt_shift 1 (fmd 0)‾) (m := 0) (T := TUnit) (S0 := dual Sd1);
          [done|exact I| |eapply d_var'; [reflexivity|spare_tac]].
        apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. }
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_close with (S0 := SEnd) (x := pt_shift 1 (pt_shift 1 (fmd 0)‾)); [done|apply ub_below_empty|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 3)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := pvar 0); [done|fut (pvar 0)|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (ESend (Pair EUnit (ESend (Pair EUnit (Var 1)))))) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := pt_shift 1 (pt_shift 1 (fmd 0))); [done|fut (fmd 2)|].
      eapply d_send with (x := pt_shift 1 (fmd 0)) (m := 0) (T := TUnit) (S0 := Sd1);
        [done|exact I|done|cbn; set_solver|fut (fmd 1)|].
      eapply d_pair; [apply tsplit_empty|lsplit_tac EUnit (ESend (Pair EUnit (Var 1)))| |].
      - apply d_unit'. spare_tac.
      - eapply d_send with (x := fmd 0) (m := 0) (T := TUnit) (S0 := Sdd);
          [done|exact I|done|cbn; set_solver|fut (fmd 0)|].
        eapply d_pair; [apply tsplit_empty|lsplit_tac EUnit (Var 1)| |].
        + apply d_unit'. spare_tac.
        + eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := pvar 1); [done| |eapply d_var'; [reflexivity|spare_tac]].
    apply (ub_below_var _ _ _ (pvar 1) _); [set_solver|by left].
    Unshelve. all: exact None.
  Qed.
End body.

Lemma fm_box_typed W Γ n F : dftyped W ∅ Γ (nones n) F fm_box fm_ty.
Proof. apply box1_typed; [reflexivity|apply fm_body]. Qed.

(** ** main *)

Definition fm_xs : list point := pvar 0 :: (pvar 0)·1 :: [].

Definition fm_L (g : fact) : Prop := ∃ f, fmx_P f ∧ g = fact_map (pt_inst (plist fm_xs)) f.

Definition W_fm : world := World ∅ (λ _, False) {[0]} (λ _ g, fm_L g).

Definition fm_main : expr :=
  let_new 0 (LetP (ENewAt 1 (Var 1)) (LetP (Var 0)
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 5)))))
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
      (App (EForce fm_box) (Pair (Var 3) (Var 1))))))).

Lemma fm_force n F e :
  dftyped W_fm ∅ (Γnew W_fm 0) (nones n) F e fm_ty →
  dftyped W_fm ∅ (Γnew W_fm 0) (nones n) F (EForce e)
    (TLolli (UPt ((pvar 0)·1)) LNone None (TProd (TSess SEnd (pvar 0) None None) (TSess SEnd ((pvar 0)·1) None None)) TUnit None).
Proof.
  intros H.
  assert (sinst_ty (slist []) (ty_inst fm_xs
            (TLolli (UPt (pvar 1)) LNone None fm_T TUnit None)) =
    TLolli (UPt ((pvar 0)·1)) LNone None (TProd (TSess SEnd (pvar 0) None None) (TSess SEnd ((pvar 0)·1) None None)) TUnit None) as <-.
  { rewrite sinst_nil. reflexivity. }
  eapply d_force with (ub := None) (c := None) (C := fm_C);
    [done| |done|split; [apply Forall_nil|intros _; apply Forall_nil]|exact I|exact H].
  apply hold_at_nil. intros f Hf _.
  destruct (fact_map (pt_inst (plist fm_xs)) f) as [x y] eqn:E.
  apply law_slt'; [exists f; by rewrite E|].
  destruct Hf as [->|[->|[->|(k & [->| ->])]]]; simpl in E; injection E as <- <-; simpl; lia.
Qed.

Theorem fm_dftyped : dftyped W_fm ∅ hc_empty [] (∅, None) fm_main TUnit.
Proof.
  unfold fm_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ SEnd None None); [spare_tac|set_solver]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew W_fm 0).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (ENewAt 1 (Var 1)) EUnit| |].
  { eapply (d_new_at _ _ _ _ _ _ 1 SEnd (pvar 0) SEnd). eapply d_var'; [reflexivity|]. spare_tac. }
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
  eapply d_app; [apply tsplit_empty|lsplit_tac (EForce fm_box) EUnit|apply ubu_below_empty| |].
  - apply (fm_force 7). by apply fm_box_typed.
  - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 3) EUnit| |].
    + eapply d_var'; [reflexivity|]. spare_tac.
    + eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Theorem fm_typed : typed W_fm None ∅ hc_empty [] (∅, None) fm_main TUnit None.
Proof. apply (dftyped_typed _ _ _ _ _ _ _ fm_dftyped). Qed.
