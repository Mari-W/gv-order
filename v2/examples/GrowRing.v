(** * The growing ring (old GrowRing.v, Padovani 2014 Ex. III.7, proposal Appendix B.1)

      Sch  = µα. ?(∃κ. α@κ).Close
      ring : □(∀ι₁ ι₂. Cr. ∗ ⊸ (Sch@ι₁ ⊗ S̄ch@ι₂ ⊸^{ι₁+1} ∗))
      ring = !(f = λp. let (x, y) = p in
                 let (y, ⟨a, a′⟩) = new_0 y in
                 let () = spawn (λw. let () = w in close (send ⟨a, y⟩)) in
                 let (x, ⟨b, b′⟩) = new_1 x in
                 let (z, x) = recv x in let () = close x in
                 let () = spawn (λw. let () = w in (force f) ⟨z, b′⟩) in
                 spawn (λw. let () = w in (force f) ⟨b, a′⟩))
      main = let (e, e′) = new_0 in (force ring) ⟨e, e′⟩

    The reordering of Appendix B.1: b is created by new_1 x before the
    receive on x, anchored at the field X·1 of x while x is held. a is
    created by new_0 y at Y·0, where the message on y carries it. The
    node at (X, Y) calls (X·0, (X·1)‾) and (X·1, (Y·0)‾). Cr holds five
    facts at every pair reachable from (ι₁, ι₂):

      Y ≺ (Y·0)‾          the payload a of the send on y
      X+1 ≺ (X·0)‾        close x while z is held
      X+1 ≺ Y·0           recv and close x while a′ is held
      X+1 ≺ X·1, (X·1)‾   recv and close x while b and b′ are held

    The receive on x at X gets its facts through X ≺ X+1. The laws of
    family 0 are Cr at (r, r‾). *)

From GV Require Export examples.Tools2.

Definition Sch : sty := SMu (SSeq (SRcv 1 (TSess (SVar 0) (pvar 0) None)) SEnd).

Lemma unfold_Sch : unfoldS Sch = SSeq (SRcv 1 (TSess Sch (pvar 0) None)) SEnd.
Proof. done. Qed.
Lemma unfold_dSch : unfoldS (dual Sch) = SSeq (SSnd 1 (TSess Sch (pvar 0) None)) SEnd.
Proof. done. Qed.
Lemma pscoped_SchT : pscoped 1 (TSess Sch (pvar 0) None).
Proof. simpl. split_and?; try done; intros a Ha; injection Ha as <-; lia. Qed.

Abbreviation sh := pt_shift.

(** ** The pairs of a ring and their facts *)

Inductive rreach (X0 Y0 : point) : point → point → Prop :=
  | rr_root : rreach X0 Y0 X0 Y0
  | rr_l X Y : rreach X0 Y0 X Y → rreach X0 Y0 (X·0) (X·1)‾
  | rr_r X Y : rreach X0 Y0 X Y → rreach X0 Y0 (X·1) (Y·0)‾.

Definition rg_F (X Y : point) (g : fact) : Prop :=
  g = FLt Y (Y·0)‾ ∨ g = FLt (sh 1 X) (X·0)‾ ∨ g = FLt (sh 1 X) (Y·0) ∨
  g = FLt (sh 1 X) (X·1) ∨ g = FLt (sh 1 X) (X·1)‾.

Lemma rreach_trans X0 Y0 X1 Y1 X Y : rreach X0 Y0 X1 Y1 → rreach X1 Y1 X Y → rreach X0 Y0 X Y.
Proof. intros H1 H2. induction H2 as [|X Y _ IH|X Y _ IH]; [done|exact (rr_l _ _ _ _ IH)|exact (rr_r _ _ _ _ IH)]. Qed.

Lemma rreach_inst σ X0 Y0 X Y :
  rreach X0 Y0 X Y → rreach (pt_inst σ X0) (pt_inst σ Y0) (pt_inst σ X) (pt_inst σ Y).
Proof.
  induction 1 as [|X Y _ IH|X Y _ IH]; [apply rr_root| |];
    rewrite pt_inst_dual, !pt_inst_field; [exact (rr_l _ _ _ _ IH)|exact (rr_r _ _ _ _ IH)].
Qed.

Lemma rg_F_inst σ X Y g : rg_F X Y g → rg_F (pt_inst σ X) (pt_inst σ Y) (fact_map (pt_inst σ) g).
Proof.
  intros H. unfold rg_F in *.
  repeat destruct H as [H|H]; subst g; cbn [fact_map];
    rewrite ?pt_inst_dual, ?pt_inst_field, ?pt_inst_shift;
    repeat (first [left; reflexivity|right]); reflexivity.
Qed.

Lemma pn_vb_inst k k' σ p :
  pn_vb k p → (∀ a, a < k → pn_vb k' (pt_name (σ a))) → pn_vb k' (pt_name (pn_inst σ p)).
Proof. intros Hp Hσ. induction p; simpl in *; auto. Qed.

Lemma pt_vb_inst k k' σ x :
  pn_vb k (pt_name x) → (∀ a, a < k → pn_vb k' (pt_name (σ a))) → pn_vb k' (pt_name (pt_inst σ x)).
Proof. intros Hx Hσ. unfold pt_inst. destruct (pt_pol x); simpl; by eapply pn_vb_inst. Qed.

Lemma rreach_vb k X0 Y0 X Y :
  pn_vb k (pt_name X0) → pn_vb k (pt_name Y0) → rreach X0 Y0 X Y →
  pn_vb k (pt_name X) ∧ pn_vb k (pt_name Y).
Proof. intros H0 H1. induction 1 as [|X Y _ [IH1 IH2]|X Y _ [IH1 IH2]]; simpl; auto. Qed.

Lemma rg_F_scoped k X Y x y :
  pn_vb k (pt_name X) → pn_vb k (pt_name Y) → rg_F X Y (FLt x y) → fact_scoped k (FLt x y).
Proof. intros HX HY H. repeat destruct H as [H|H]; injection H as -> ->; simpl; auto. Qed.

(** ** The box *)

Definition rg_P (g : fact) : Prop := ∃ X Y, rreach (pvar 0) (pvar 1) X Y ∧ rg_F X Y g.
Definition rg_C : bcs := BCs [] rg_P.

Definition rg_T : ty := TProd (TSess Sch (pvar 0) None) (TSess (dual Sch) (pvar 1) None).
Definition rg_ty : ty := box1 2 rg_C (sh 1 (pvar 0)) rg_T.

Definition rg_e : expr :=
  LetP (Var 0) (LetP (ENewAt 0 (Var 0)) (LetP (Var 0)
  (LetU (ESpawn (Lam (LetU (Var 0) (EClose (ESend (Pair (Var 2) (Var 4)))))))
  (LetP (ENewAt 1 (Var 5)) (LetP (Var 0)
  (LetP (ERecv (Var 3)) (LetU (EClose (Var 0))
  (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 14)) (Pair (Var 2) (Var 3))))))
        (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 14)) (Pair (Var 4) (Var 7)))))))))))))).

Definition ring : expr := EBox (Lam rg_e).

(** The facts of Cr at an instance (X1, Y1) reachable from (ι₁, ι₂). *)
Lemma rg_inst X1 Y1 f :
  rreach (pvar 0) (pvar 1) X1 Y1 → rg_P f →
  rg_P (fact_map (pt_inst (plist (X1 :: Y1 :: []))) f).
Proof.
  intros HR (X & Y & HXY & HF).
  exists (pt_inst (plist (X1 :: Y1 :: [])) X), (pt_inst (plist (X1 :: Y1 :: [])) Y). split.
  - eapply rreach_trans; [exact HR|].
    pose proof (rreach_inst (plist (X1 :: Y1 :: [])) _ _ _ _ HXY) as H'.
    rewrite !pt_inst_pvar_at in H'. exact H'.
  - by apply rg_F_inst.
Qed.

Lemma rg_P_scoped x y : rg_P (FLt x y) → fact_scoped 2 (FLt x y).
Proof.
  intros (X & Y & HXY & HF). destruct (rreach_vb 2 (pvar 0) (pvar 1) X Y ltac:(simpl; lia) ltac:(simpl; lia) HXY).
  by apply (rg_F_scoped 2 X Y).
Qed.

Ltac rg_disj :=
  first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
        | right; right; right; left; reflexivity | right; right; right; right; reflexivity ].

Section body.
  Context (W : world) (Γ : hctx) (n : nat).
  Local Abbreviation Γb := (Γbox 2 rg_C (sh 1 (pvar 0)) Γ).

  Lemma rg_hyp x y : rg_P (FLt x y) → slt W Γb x y.
  Proof.
    intros Hf. eapply (hyp_slt_ids _ _ rg_P 2); [exact (Γbox_in 2 rg_C (sh 1 (pvar 0)) Γ)|done|].
    by apply rg_P_scoped.
  Qed.

  Ltac rgf := apply rg_hyp; exists (pvar 0), (pvar 1); split; [apply rr_root|unfold rg_F; rg_disj].

  (** A recursive call at a pair reachable in one step. *)
  Lemma rg_call Δ F e X1 Y1 :
    rreach (pvar 0) (pvar 1) X1 Y1 →
    dftyped W ∅ Γb Δ F e rg_ty →
    dftyped W ∅ Γb Δ F (EForce e)
      (TLolli (Some (sh 1 X1)) None None tinf
         (TProd (TSess Sch X1 None) (TSess (dual Sch) Y1 None)) TUnit None).
  Proof.
    intros HR H.
    assert (sinst_ty (slist []) (ty_inst (X1 :: Y1 :: [])
              (TLolli (Some (sh 1 (pvar 0))) None None tinf rg_T TUnit None)) =
      TLolli (Some (sh 1 X1)) None None tinf
         (TProd (TSess Sch X1 None) (TSess (dual Sch) Y1 None)) TUnit None) as <-.
    { rewrite sinst_nil. unfold ty_inst, rg_T. cbn [pinst_ty fmap option_fmap option_map].
      rewrite pt_inst_shift, !pt_inst_pvar_at. reflexivity. }
    eapply d_force with (ub := None) (c := None) (t := tinf) (C := rg_C);
      [done| |done|split; [apply Forall_nil|intros _; apply Forall_nil]|exact I|exact H].
    apply hold_at_nil. intros f Hf _.
    destruct (fact_map (pt_inst (plist (X1 :: Y1 :: []))) f) as [x y] eqn:E.
    apply rg_hyp. rewrite <-E. by apply rg_inst.
  Qed.

  Ltac normF :=
    cbn [lenv_bot hbot orb]; rewrite ?lenv_bot_nones; unfold rg_ty, box1;
    cbn [hbot orb sf_unionb fst snd fs_var fs_bot].

  Ltac fut x :=
    apply (ub_below_gen _ _ x (sh 1 (pvar 0)) 1);
      [ let y := fresh "y" in let Hy := fresh "Hy" in
        intros y Hy; revert Hy; normF; unfold payload_at, ty_inst; cbn [pinst_ty]; intros Hy; heads_cases Hy;
        first [rgf | eapply sl_trans; [apply sl_po|rgf]]
      | normF; reflexivity | apply Γbox_fv
      | first [by left | right; apply sl_po] | normF; reflexivity ].

  Lemma rg_body :
    dftyped W ∅ Γb (Some rg_T :: Some rg_ty :: nones n) (∅, Some (FVar 1)) rg_e TUnit.
  Proof.
    unfold rg_e.
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    (* a at Y·0 *)
    eapply d_letp; [apply tsplit_empty|lsplit_tac (ENewAt 0 (Var 0)) EUnit| |].
    { eapply (d_new_at _ _ _ _ _ _ 0 (dual Sch) (pvar 1) Sch). eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    (* the y-thread sends a on y *)
    eapply d_letu; [apply tsplit_empty
                   |lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (ESend (Pair (Var 2) (Var 4))))))) EUnit| |].
    { eapply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_close with (S0 := SEnd) (x := sh 1 (pvar 1)); [done|apply ub_below_empty|].
      eapply d_send with (x := pvar 1) (m := 1) (T := TSess Sch (pvar 0) None) (S0 := dual Sch);
        [exact unfold_dSch|exact pscoped_SchT|done| |apply ub_below_empty|].
      { intros y Hy. cbn in Hy. apply elem_of_singleton in Hy as ->. rgf. }
      eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 2) (Var 4)| |].
      - eapply d_var'; [reflexivity|]. spare_tac.
      - eapply d_var'; [reflexivity|]. spare_tac. }
    (* b at X·1, before the receive *)
    eapply d_letp; [apply tsplit_empty|lsplit_tac (ENewAt 1 (Var 5)) EUnit| |].
    { eapply (d_new_at _ _ _ _ _ _ 1 Sch (pvar 0) Sch). eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 3)) EUnit| |].
    { eapply d_recv with (x := pvar 0) (m := 1) (T := TSess Sch (pvar 0) None) (S0 := Sch);
        [exact unfold_Sch|exact pscoped_SchT|fut (pvar 0)|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 0)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := sh 1 (pvar 0)); [done|fut (sh 1 (pvar 0))|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty
                   |lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 14)) (Pair (Var 2) (Var 3)))))) EUnit
                   | |].
    { eapply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_app; [apply tsplit_empty|lsplit_tac (EForce (Var 14)) (Pair (Var 2) (Var 3))|apply ub_below_empty| |].
      - eapply rg_call; [eapply rr_l, rr_root|]. eapply d_var'; [reflexivity|]. spare_tac.
      - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 2) (Var 3)| |].
        + eapply d_var'; [reflexivity|]. spare_tac.
        + eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_app; [apply tsplit_empty|lsplit_tac (EForce (Var 14)) (Pair (Var 4) (Var 7))|apply ub_below_empty| |].
    - eapply rg_call; [eapply rr_r, rr_root|]. eapply d_var'; [reflexivity|]. spare_tac.
    - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 4) (Var 7)| |].
      + eapply d_var'; [reflexivity|]. spare_tac.
      + eapply d_var'; [reflexivity|]. spare_tac.
    Unshelve. all: exact None.
  Qed.
End body.

Lemma ring_typed W Γ n F : hc_fv Γ = ∅ → dftyped W ∅ Γ (nones n) F ring rg_ty.
Proof. intros HΓ. apply box1_typed; [done|reflexivity|apply rg_body]. Qed.

(** ** main *)

Definition rg_xs : list point := pvar 0 :: (pvar 0)‾ :: [].

Definition rg_L (g : fact) : Prop := ∃ f, rg_P f ∧ g = fact_map (pt_inst (plist rg_xs)) f.

Definition W_rg : world := World ∅ (λ _, False) {[0]} (λ _ g, rg_L g).

Definition rg_main : expr := let_new 0 (App (EForce ring) (Pair (Var 1) (Var 0))).

Lemma rg_force n F e :
  dftyped W_rg ∅ (Γnew W_rg 0) (nones n) F e rg_ty →
  dftyped W_rg ∅ (Γnew W_rg 0) (nones n) F (EForce e)
    (TLolli (Some (sh 1 (pvar 0))) None None tinf
       (TProd (TSess Sch (pvar 0) None) (TSess (dual Sch) (pvar 0)‾ None)) TUnit None).
Proof.
  intros H.
  assert (sinst_ty (slist []) (ty_inst rg_xs
            (TLolli (Some (sh 1 (pvar 0))) None None tinf rg_T TUnit None)) =
    TLolli (Some (sh 1 (pvar 0))) None None tinf
       (TProd (TSess Sch (pvar 0) None) (TSess (dual Sch) (pvar 0)‾ None)) TUnit None) as <-.
  { rewrite sinst_nil. reflexivity. }
  eapply d_force with (ub := None) (c := None) (t := tinf) (C := rg_C);
    [done| |done|split; [apply Forall_nil|intros _; apply Forall_nil]|exact I|exact H].
  apply hold_at_nil. intros f Hf Hs.
  destruct (fact_map (pt_inst (plist rg_xs)) f) as [x y] eqn:E.
  apply law_slt'; [exists f; by rewrite E|].
  destruct f as [u v]. destruct Hs as [Hu Hv]. simpl in E. injection E as <- <-. split.
  - eapply pt_vb_inst; [exact Hu|]. intros [|[|a]] Ha; unfold rg_xs, plist in *; simpl in *; lia.
  - eapply pt_vb_inst; [exact Hv|]. intros [|[|a]] Ha; unfold rg_xs, plist in *; simpl in *; lia.
Qed.

Theorem rg_dftyped : dftyped W_rg ∅ hc_empty [] (∅, None) rg_main TUnit.
Proof.
  unfold rg_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ Sch None None); [spare_tac|set_solver]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew W_rg 0).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_app; [apply tsplit_empty|lsplit_tac (EForce ring) EUnit|apply ub_below_empty| |].
  - apply (rg_force 3). by apply ring_typed.
  - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
    + eapply d_var'; [reflexivity|]. spare_tac.
    + eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Theorem rg_typed : typed W_rg None ∅ hc_empty [] (∅, None) rg_main TUnit None tinf.
Proof. apply (dftyped_typed _ _ _ _ _ _ _ rg_dftyped). Qed.
