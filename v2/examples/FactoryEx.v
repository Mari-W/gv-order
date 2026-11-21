(** * The factory (old FactoryEx.v, proposal Appendix B.1, #51)

      mk₀  = !(f = λu. let () = u in let (c, c′) = new_0 in
                      let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)
      mk₁  = !(f = λp. let (p, ⟨c, c′⟩) = new_0 p in
                      let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in ⟨p, c′⟩)
      main = let p = (force mk₀) ∗ in let ⟨p, q⟩ = (force mk₁) p in
             let () = recvclose p in recvclose q
      Λ_0(r) = {r‾ ≺ r·0, r‾⁺ ≺ r·0}

    mk₀ : □(∗ ⊸ ∃^⊥ ι. Λ_0(ι). (?∗.Close)@ι‾) creates at a fresh root,
    so the first call needs no point. mk₁ : □∀ζ. {ζ ≺ ζ·0, ζ⁺ ≺ ζ·0}.
    (?∗.Close)@ζ ⊸ (?∗.Close)@ζ ⊗ (?∗.Close)@(ζ·0)‾ anchors the new
    channel at the end it receives. main opens p at ι, calls mk₁ at
    ζ = ι‾, and receives and closes p at ι‾ and ι‾⁺ while it holds q at
    (ι·0)‾. The laws at ι give both facts. *)

From GV Require Export examples.Tools2.

Definition Sd : sty := SSeq (SSnd 0 TUnit) SEnd.
Definition Sr : sty := SSeq (SRcv 0 TUnit) SEnd.

Definition fx_L (g : fact) : Prop :=
  g = FLt (pvar 0)‾ ((pvar 0)·0) ∨ g = FLt (pt_shift 1 (pvar 0)‾) ((pvar 0)·0).

Definition W_fx : world := World ∅ (λ _, False) {[0]} (λ _ g, fx_L g).

Lemma W_fx_wf : world_wf W_fx.
Proof. split; simpl; [done|]. intros ℓ x y _ [E|E]; injection E as -> ->; done. Qed.

Definition Tres : ty := TEx LBot 1 (bcs_of (w_laws W_fx 0)) (TSess Sr (pvar 0)‾ None).

Definition C0 : bcs := bcs_of (λ _, False).
Definition mk0_ty : ty := boxg 0 C0 None TUnit Tres.

Definition mk1_P (g : fact) : Prop :=
  g = FLt (pvar 0) ((pvar 0)·0) ∨ g = FLt (pt_shift 1 (pvar 0)) ((pvar 0)·0).
Definition mk1_C : bcs := BCs [] mk1_P.
Definition mk1_res : ty := TProd (TSess Sr (pvar 0) None) (TSess Sr ((pvar 0)·0)‾ None).
Definition mk1_ty : ty := boxg 1 mk1_C None (TSess Sr (pvar 0) None) mk1_res.

(** The worker sends ∗ on c and closes it. *)
Definition worker (i : nat) : expr := Lam (LetU (Var 0) (EClose (ESend (Pair EUnit (Var i))))).

Definition mk0_e : expr :=
  LetU (Var 0) (let_new 0 (LetU (ESpawn (worker 2)) (Var 0))).
Definition mk0 : expr := EBox (Lam mk0_e).

Definition mk1_e : expr :=
  LetP (ENewAt 0 (Var 0)) (LetP (Var 0) (LetU (ESpawn (worker 2)) (Pair (Var 3) (Var 0)))).
Definition mk1 : expr := EBox (Lam mk1_e).

Definition fx_main : expr :=
  ELet (App (EForce mk0) EUnit)
    (LetP (App (EForce mk1) (Var 0))
      (LetU (LetP (ERecv (Var 1)) (LetU (Var 1) (EClose (Var 0))))
            (LetP (ERecv (Var 0)) (LetU (Var 1) (EClose (Var 0)))))).

(** The worker: send at x, close at x⁺, with no future. *)
Ltac worker_tac pp j :=
  eapply d_spawn_lam; unfold worker;
  eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit
                 |eapply d_var'; [reflexivity|spare_tac]|];
  eapply d_close with (S0 := SEnd) (x := pt_shift 1 pp); [done|apply ub_below_empty|];
  eapply d_send with (x := pp) (m := 0) (T := TUnit) (S0 := Sd);
    [done|exact I|done|cbn; set_solver|apply ub_below_empty|];
  eapply d_pair; [apply tsplit_empty|lsplit_tac EUnit (Var j)
                 |apply d_unit'; spare_tac|eapply d_var'; [reflexivity|spare_tac]].

(** ** mk₀ *)

Lemma mk0_body Γ n :
  dftyped W_fx ∅ (hc_fvar 1 None (hc_fvar 0 None (hc_open 0 C0 Γ)))
    (Some TUnit :: Some mk0_ty :: nones n) (∅, Some (FVar 1)) mk0_e Tres.
Proof.
  unfold mk0_e, let_new.
  eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_let; [apply tsplit_empty|lsplit_tac (ENew 0) EUnit| |].
  { eapply (d_new' _ _ _ _ _ Sd None None); [spare_tac|set_solver]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_nil', !lenv_pinst_cons', lenv_pinst_nones.
  cbn [fmap option_fmap option_map insert list_insert].
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (worker 2)) EUnit| |].
  { worker_tac (pvar 0) 2. }
  (* pack c′ at the fresh root *)
  change (pinst_ty (pshift 1) Tres) with Tres. unfold Tres.
  eapply d_pack with (xs := pvar 0 :: []); [done| |exact I|].
  - apply hold_at_nil. intros f Hf _. destruct Hf as [->| ->]; simpl.
    + eapply (hyp_slt_ids _ _ (w_laws W_fx 0) 1);
        [unfold hc_fvar, hc_open; cbn [hc_hyps]; apply elem_of_app; right; apply list_elem_of_here|by left|simpl; lia].
    + eapply (hyp_slt_ids _ _ (w_laws W_fx 0) 1);
        [unfold hc_fvar, hc_open; cbn [hc_hyps]; apply elem_of_app; right; apply list_elem_of_here|by right|simpl; lia].
  - eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Lemma mk0_typed Γ n F : hc_fv Γ = ∅ → dftyped W_fx ∅ Γ (nones n) F mk0 mk0_ty.
Proof. intros HΓ. apply boxg_typed; [done|reflexivity|apply mk0_body]. Qed.

(** ** mk₁ *)

Lemma mk1_body Γ n :
  dftyped W_fx ∅ (hc_fvar 1 None (hc_fvar 0 None (hc_open 1 mk1_C Γ)))
    (Some (TSess Sr (pvar 0) None) :: Some mk1_ty :: nones n) (∅, Some (FVar 1)) mk1_e mk1_res.
Proof.
  unfold mk1_e.
  eapply d_letp; [apply tsplit_empty|lsplit_tac (ENewAt 0 (Var 0)) EUnit| |].
  { eapply (d_new_at _ _ _ _ _ _ 0 Sr (pvar 0) Sd). eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (worker 2)) EUnit| |].
  { worker_tac ((pvar 0)·0) 2. }
  eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 3) (Var 0)| |].
  - eapply d_var'; [reflexivity|]. spare_tac.
  - eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Lemma mk1_typed Γ n F : hc_fv Γ = ∅ → dftyped W_fx ∅ Γ (nones n) F mk1 mk1_ty.
Proof. intros HΓ. apply boxg_typed; [done|reflexivity|apply mk1_body]. Qed.

(** ** main *)

Abbreviation Γx := (Γnew W_fx 0).

Lemma fx_law x y : fx_L (FLt x y) → fact_scoped 1 (FLt x y) → slt W_fx Γx x y.
Proof. intros Hf Hs. by apply law_slt'. Qed.

Theorem fx_dftyped : dftyped W_fx ∅ hc_empty [] (∅, None) fx_main TUnit.
Proof.
  unfold fx_main.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { (* the first call needs no point *)
    eapply d_app; [apply tsplit_empty|apply lsplit_nil|apply ub_below_empty| |apply d_unit'; spare_tac].
    assert (sinst_ty (slist []) (ty_inst [] (TLolli None None None tinf TUnit Tres None)) =
            TLolli None None None tinf TUnit Tres None) as <- by (rewrite sinst_nil; reflexivity).
    eapply d_force with (ub := None) (c := None) (t := tinf) (C := C0) (m := 0);
      [done| |done|split; [apply Forall_nil|intros _; apply Forall_nil]|exact I|].
    - intros x y (g0 & (f & Hf & _) & _). done.
    - by apply (mk0_typed _ 0). }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew W_fx 0).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (App (EForce mk1) (Var 0)) EUnit| |].
  { eapply d_app; [apply tsplit_empty|lsplit_tac (EForce mk1) (Var 0)|apply ub_below_empty| |].
    - assert (sinst_ty (slist []) (ty_inst ((pvar 0)‾ :: [])
                (TLolli None None None tinf (TSess Sr (pvar 0) None) mk1_res None)) =
              TLolli None None None tinf (TSess Sr (pvar 0)‾ None)
                (TProd (TSess Sr (pvar 0)‾ None) (TSess Sr ((pvar 0)·0)‾ None)) None) as <-
        by (rewrite sinst_nil; reflexivity).
      eapply d_force with (ub := None) (c := None) (t := tinf) (C := mk1_C);
        [done| |done|split; [apply Forall_nil|intros _; apply Forall_nil]|exact I|].
      + apply hold_at_nil. intros f Hf _. destruct Hf as [->| ->]; simpl.
        * apply fx_law; [by left|simpl; lia].
        * apply fx_law; [by right|simpl; lia].
      + by apply (mk1_typed _ 1).
    - eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (LetP (ERecv (Var 1)) (LetU (Var 1) (EClose (Var 0)))) EUnit| |].
  { (* recvclose p while q is held *)
    eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 1)) EUnit| |].
    - eapply d_recv with (x := (pvar 0)‾) (m := 0) (T := TUnit) (S0 := Sr);
        [done|exact I| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_novar; [|reflexivity]. intros y Hy.
      cbn [sf_unionb fst snd lenv_bot hbot orb] in Hy. heads_cases Hy.
      apply fx_law; [by left|simpl; lia].
    - eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_close with (S0 := SEnd) (x := pt_shift 1 (pvar 0)‾); [done| |].
      + apply ub_below_novar; [|reflexivity]. intros y Hy.
        cbn [sf_unionb fst snd lenv_bot hbot orb] in Hy. heads_cases Hy.
        apply fx_law; [by right|simpl; lia].
      + eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 0)) EUnit| |].
  - eapply d_recv with (x := ((pvar 0)·0)‾) (m := 0) (T := TUnit) (S0 := Sr);
      [done|exact I| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_novar; [|reflexivity]. intros y Hy.
    cbn [sf_unionb fst snd lenv_bot hbot orb] in Hy. heads_cases Hy.
  - eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := pt_shift 1 ((pvar 0)·0)‾); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Theorem fx_typed : typed W_fx None ∅ hc_empty [] (∅, None) fx_main TUnit None tinf.
Proof. apply (dftyped_typed _ _ _ _ _ _ _ fx_dftyped). Qed.
