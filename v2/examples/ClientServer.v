(** * The client and server cycle created by main (proposal §2.5)

      main = let (a, a′) = new_0 in
             let (a, ⟨b, b′⟩) = new_κ a in
             let () = spawn (λu. let () = u in (force srv) ⟨a′, b′⟩) in
             (force cli) ⟨a, b⟩
      cli  = !(f = λp. let (a, b) = p in let a = send ⟨∗, a⟩ in
                      let (u, b) = recv b in let () = u in (force f) ⟨a, b⟩)
      srv  = !(g = λp. let (a, b) = p in let (u, a) = recv a in let () = u in
                      let b = send ⟨∗, b⟩ in (force g) ⟨a, b⟩)

    Option (d) of Q2, family laws. a sits at a fresh root ρ of family 0,
    b at the field ρ·0 (κ = 0), and the ceiling of both loops is ρ·1.
    Both boxes have the one type

      □∀ι κ ζ. C. ∗ ⊸ (S1@ι ⊗ S2@κ ⊸^ζ ∗)
      C = {ι+k ≺ (κ+k)‾, κ+k ≺ (ι+k+1)‾, ι+k ≺ ζ, κ+k ≺ ζ | k}

    the client at S1 = µα.!∗.α, S2 = µα.?∗.α, the server at the duals.
    The self call instantiates C at (ι⁺, κ⁺, ζ), where it holds by the
    facts at k + 1. The laws Λ_0(r) state C at (r, r·0, r·1) and at
    (r‾, (r·0)‾, r·1). The program types, as §2.5 (d) claims. *)

From GV Require Export examples.Tools.

Definition Sa : sty := SMu (SSeq (SSnd 0 TUnit) (SVar 0)).
Definition Sb : sty := SMu (SSeq (SRcv 0 TUnit) (SVar 0)).

Abbreviation sh := pt_shift.

(** The constraint, over ι = 0, κ = 1, ζ = 2. *)
Definition cs_P (g : fact) : Prop :=
  ∃ k, g = FLt (sh k (pvar 0)) (sh k (pvar 1))‾ ∨ g = FLt (sh k (pvar 1)) (sh (S k) (pvar 0))‾ ∨
       g = FLt (sh k (pvar 0)) (pvar 2) ∨ g = FLt (sh k (pvar 1)) (pvar 2).
Definition cs_C : bcs := BCs [] cs_P.

(** The laws of family 0 over the root r = 0. *)
Definition cs_L (g : fact) : Prop :=
  ∃ k (b : bool), let α := pt_polar b (pvar 0) in let β := pt_polar b ((pvar 0)·0) in
    g = FLt (sh k α) (sh k β)‾ ∨ g = FLt (sh k β) (sh (S k) α)‾ ∨
    g = FLt (sh k α) ((pvar 0)·1) ∨ g = FLt (sh k β) ((pvar 0)·1).

Definition W_cs : world := World ∅ (λ _, False) {[0]} (λ _ g, cs_L g).

Definition cs_arr (S1 S2 : sty) : ty :=
  TLolli (UPt (pvar 2)) LNone None (TProd (TSess S1 (pvar 0) None None) (TSess S2 (pvar 1) None None)) TUnit None.

Definition cs_box (S1 S2 : sty) : ty := TBox 3 0 cs_C None None (cs_arr S1 S2).

Definition cli : expr :=
  EBox (Lam (LetP (Var 0) (ELet (ESend (Pair EUnit (Var 1)))
    (LetP (ERecv (Var 1)) (LetU (Var 1) (App (EForce (Var 6)) (Pair (Var 2) (Var 0)))))))).

Definition srv : expr :=
  EBox (Lam (LetP (Var 0) (LetP (ERecv (Var 1)) (LetU (Var 1)
    (ELet (ESend (Pair EUnit (Var 2))) (App (EForce (Var 6)) (Pair (Var 1) (Var 0)))))))).

Definition cs_main : expr :=
  let_new 0 (LetP (ENewAt 0 (Var 1)) (LetP (Var 0)
    (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce srv) (Pair (Var 5) (Var 1))))))
          (App (EForce cli) (Pair (Var 3) (Var 1)))))).

Lemma unfold_Sa : unfoldS Sa = SSeq (SSnd 0 TUnit) Sa.
Proof. done. Qed.
Lemma unfold_Sb : unfoldS Sb = SSeq (SRcv 0 TUnit) Sb.
Proof. done. Qed.

(** The facts of the box constraint inside a box body. *)
Lemma cs_fact W Γ x y :
  (cs_C, ids 3) ∈ hc_hyps Γ →
  (∃ k, FLt x y = FLt (sh k (pvar 0)) (sh k (pvar 1))‾ ∨ FLt x y = FLt (sh k (pvar 1)) (sh (S k) (pvar 0))‾ ∨
       FLt x y = FLt (sh k (pvar 0)) (pvar 2) ∨ FLt x y = FLt (sh k (pvar 1)) (pvar 2)) →
  slt W Γ x y.
Proof.
  intros Hin (k & Hk). eapply (slt_hyp _ _ cs_P (ids 3) (FLt x y)); [done|by exists k| |].
  - destruct Hk as [E|[E|[E|E]]]; injection E as -> ->; simpl; lia.
  - destruct Hk as [E|[E|[E|E]]]; injection E as -> ->; fact_eq.
Qed.

Lemma cs_box_shift S1 S2 Δ :
  lenv_pinst (pshift 3) (Some (TBox 3 0 cs_C None None (cs_arr S1 S2)) :: Δ) =
  Some (cs_box S1 S2) :: lenv_pinst (pshift 3) Δ.
Proof. reflexivity. Qed.

(** One box body typing for both loops. [e] is the body after the let
    pair, which binds the end at ι at 1 and the end at κ at 0. *)
Lemma cs_box_typed W Γ n F (S1 S2 : sty) e :
  dftyped W ∅ (hc_open 3 cs_C Γ)
    (Some (TSess S2 (pvar 1) None None) :: Some (TSess S1 (pvar 0) None None) ::
     None :: Some (cs_box S1 S2) :: nones n)
    (∅, Some (FRest (RAbove (pvar 2)))) e TUnit →
  dftyped W ∅ Γ (nones n) F (EBox (Lam (LetP (Var 0) e))) (cs_box S1 S2).
Proof.
  intros He. eapply d_box.
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil, cs_box_shift, lenv_pinst_nones.
  eapply d_abs.
  { apply lb_below_none. spare_tac. }
  eapply d_letp; [apply tsplit_empty| | |].
  - lsplit_tac (Var 0) e.
  - eapply d_var'; [reflexivity|]. spare_tac.
  - exact He.
Qed.

Section body.
  Context (W : world) (Γ : hctx) (n : nat).
  Local Definition Γb : hctx := hc_open 3 cs_C Γ.

  Lemma cs_in : (cs_C, ids 3) ∈ hc_hyps Γb.
  Proof. unfold Γb, hc_open. simpl. apply elem_of_app. right. by left. Qed.


  Ltac fct k := apply cs_fact; [apply cs_in|exists k;
    first [left; fact_eq | right; left; fact_eq | right; right; left; fact_eq | right; right; right; fact_eq]].

  Ltac fut :=
    lazymatch goal with
    | |- ub_below_s _ _ (Some ?x) ?F =>
        rewrite ?lenv_bot_nones; cbn [lenv_bot hbot orb sf_unionb fst snd];
        apply (ub_below_var _ _ _ (pvar 2) _)
    end.

  (** The force of the self at (ι⁺, κ⁺, ζ). *)
  Lemma cs_self Δ F S1 S2 :
    dftyped W ∅ Γb Δ F (Var 6) (cs_box S1 S2) →
    dftyped W ∅ Γb Δ F (EForce (Var 6))
      (TLolli (UPt (pvar 2)) LNone None (TProd (TSess S1 (sh 1 (pvar 0)) None None) (TSess S2 (sh 1 (pvar 1)) None None)) TUnit None).
  Proof.
    intros H. assert (sinst_ty (slist []) (ty_inst (sh 1 (pvar 0) :: sh 1 (pvar 1) :: pvar 2 :: []) (cs_arr S1 S2)) =
      TLolli (UPt (pvar 2)) LNone None (TProd (TSess S1 (sh 1 (pvar 0)) None None) (TSess S2 (sh 1 (pvar 1)) None None)) TUnit None) as <-.
    { rewrite sinst_nil. reflexivity. }
    eapply d_force with (ub := None) (c := None); [done| |done|split; [apply Forall_nil|intros _; apply Forall_nil]|exact I|exact H].
    apply hold_at_nil. intros f (k & Hf) _.
    destruct Hf as [->|[->|[->| ->]]]; simpl.
    - fct (S k).
    - fct (S k).
    - fct (S k).
    - fct (S k).
  Qed.
  Ltac dfut x :=
    apply (ub_below_varb _ _ x (pvar 2) _ _); [bot_false|
      let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; heads_simpl Hy;
      repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst;
      try contradiction; first [fct 0 | fct 1]
    | right; fct 0 ].

  Definition cli_e : expr :=
    ELet (ESend (Pair EUnit (Var 1)))
      (LetP (ERecv (Var 1)) (LetU (Var 1) (App (EForce (Var 6)) (Pair (Var 2) (Var 0))))).

  Lemma cli_body :
    dftyped W ∅ Γb (Some (TSess Sb (pvar 1) None None) :: Some (TSess Sa (pvar 0) None None) ::
                     None :: Some (cs_box Sa Sb) :: nones n)
      (∅, Some (FRest (RAbove (pvar 2)))) cli_e TUnit.
  Proof.
    unfold cli_e.
    eapply d_let; [apply tsplit_empty|lsplit_tac (ESend (Pair EUnit (Var 1))) EUnit| |].
    { eapply d_send with (x := pvar 0) (m := 0) (T := TUnit) (S0 := Sa);
        [exact unfold_Sa|exact I|done|cbn; set_solver|dfut (pvar 0)|].
      eapply d_pair; [apply tsplit_empty|lsplit_tac EUnit (Var 1)| |].
      - apply d_unit'. spare_tac.
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letp;
      [apply tsplit_empty|lsplit_tac (ERecv (Var 1)) EUnit| |].
    { eapply d_recv with (x := pvar 1) (m := 0) (T := TUnit) (S0 := Sb);
        [exact unfold_Sb|exact I|dfut (pvar 1)|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_app; [apply tsplit_empty|lsplit_tac (EForce (Var 6)) EUnit| | |].
    - apply ubu_pt; eapply (ub_below_var _ _ _ (pvar 2) _); [intros y Hy; exfalso; set_solver|by left].
    - apply cs_self. eapply d_var'; [reflexivity|]. spare_tac.
    - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 2) EUnit| |].
      + eapply d_var'; [reflexivity|]. spare_tac.
      + eapply d_var'; [reflexivity|]. spare_tac.
    Unshelve. all: exact None.
  Qed.

  Definition srv_e : expr :=
    LetP (ERecv (Var 1)) (LetU (Var 1)
      (ELet (ESend (Pair EUnit (Var 2))) (App (EForce (Var 6)) (Pair (Var 1) (Var 0))))).

  Lemma srv_body :
    dftyped W ∅ Γb (Some (TSess Sa (pvar 1) None None) :: Some (TSess Sb (pvar 0) None None) ::
                     None :: Some (cs_box Sb Sa) :: nones n)
      (∅, Some (FRest (RAbove (pvar 2)))) srv_e TUnit.
  Proof.
    unfold srv_e.
    eapply d_letp;
      [apply tsplit_empty|lsplit_tac (ERecv (Var 1)) EUnit| |].
    { eapply d_recv with (x := pvar 0) (m := 0) (T := TUnit) (S0 := Sb);
        [exact unfold_Sb|exact I|dfut (pvar 0)|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_let; [apply tsplit_empty|lsplit_tac (ESend (Pair EUnit (Var 2))) EUnit| |].
    { eapply d_send with (x := pvar 1) (m := 0) (T := TUnit) (S0 := Sa);
        [exact unfold_Sa|exact I|done|cbn; set_solver|dfut (pvar 1)|].
      eapply d_pair; [apply tsplit_empty|lsplit_tac EUnit (Var 2)| |].
      - apply d_unit'. spare_tac.
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_app; [apply tsplit_empty|lsplit_tac (EForce (Var 6)) EUnit| | |].
    - apply ubu_pt; eapply (ub_below_var _ _ _ (pvar 2) _); [intros y Hy; exfalso; set_solver|by left].
    - apply cs_self. eapply d_var'; [reflexivity|]. spare_tac.
    - eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |].
      + eapply d_var'; [reflexivity|]. spare_tac.
      + eapply d_var'; [reflexivity|]. spare_tac.
    Unshelve. all: exact None.
  Qed.
End body.

(** ** main *)

Definition Γm : hctx := hc_open 1 (bcs_of (w_laws W_cs 0)) hc_empty.

Lemma law_fact x y :
  (∃ k (b : bool), let α := pt_polar b (pvar 0) in let β := pt_polar b ((pvar 0)·0) in
    FLt x y = FLt (sh k α) (sh k β)‾ ∨ FLt x y = FLt (sh k β) (sh (S k) α)‾ ∨
    FLt x y = FLt (sh k α) ((pvar 0)·1) ∨ FLt x y = FLt (sh k β) ((pvar 0)·1)) →
  slt W_cs Γm x y.
Proof.
  intros (k & b & Hk). eapply (slt_hyp _ _ cs_L (ids 1) (FLt x y)).
  - unfold Γm, hc_open. simpl. by left.
  - by exists k, b.
  - destruct b; destruct Hk as [E|[E|[E|E]]]; injection E as -> ->; simpl; lia.
  - destruct b; destruct Hk as [E|[E|[E|E]]]; injection E as -> ->; fact_eq.
Qed.

(** The force of a box at (x1, x2, ρ·1) from main. *)
Lemma cs_force n F S1 S2 x1 x2 e (b : bool) :
  x1 = pt_polar b (pvar 0) → x2 = pt_polar b ((pvar 0)·0) →
  dftyped W_cs ∅ Γm (nones n) F e (cs_box S1 S2) →
  dftyped W_cs ∅ Γm (nones n) F (EForce e)
    (TLolli (UPt ((pvar 0)·1)) LNone None (TProd (TSess S1 x1 None None) (TSess S2 x2 None None)) TUnit None).
Proof.
  intros -> -> H.
  assert (sinst_ty (slist []) (ty_inst (pt_polar b (pvar 0) :: pt_polar b ((pvar 0)·0) :: (pvar 0)·1 :: [])
            (cs_arr S1 S2)) =
    TLolli (UPt ((pvar 0)·1)) LNone None (TProd (TSess S1 (pt_polar b (pvar 0)) None None) (TSess S2 (pt_polar b ((pvar 0)·0)) None None)) TUnit None) as <-.
  { rewrite sinst_nil. destruct b; reflexivity. }
  eapply d_force with (ub := None) (c := None);
    [done| |done|split; [apply Forall_nil|intros _; apply Forall_nil]|exact I|exact H].
  apply hold_at_nil. intros f (k & Hf) _.
  destruct Hf as [->|[->|[->| ->]]]; simpl; apply law_fact; exists k, b; destruct b;
    first [left; fact_eq | right; left; fact_eq | right; right; left; fact_eq | right; right; right; fact_eq].
Qed.

Lemma cli_typed n F : dftyped W_cs ∅ Γm (nones n) F cli (cs_box Sa Sb).
Proof. apply cs_box_typed, cli_body. Qed.

Lemma srv_typed n F : dftyped W_cs ∅ Γm (nones n) F srv (cs_box Sb Sa).
Proof. apply cs_box_typed, srv_body. Qed.

Theorem cs_dftyped : dftyped W_cs ∅ hc_empty [] (∅, None) cs_main TUnit.
Proof.
  unfold cs_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ Sa None None); [spare_tac|set_solver]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold Γm.
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (ENewAt 0 (Var 1)) EUnit| |].
  { eapply (d_new_at _ _ _ _ _ _ 0 Sa (pvar 0) Sb). eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty
                 |lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce srv) (Pair (Var 5) (Var 1)))))) EUnit| |].
  - eapply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_app; [apply tsplit_empty|lsplit_tac (EForce srv) EUnit|apply ubu_below_empty| |].
    + eapply (cs_force 8 _ Sb Sa _ _ _ false); [done|done|apply srv_typed].
    + eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 5) EUnit| |].
      * eapply d_var'; [reflexivity|]. spare_tac.
      * eapply d_var'; [reflexivity|]. spare_tac.
  - eapply d_app; [apply tsplit_empty|lsplit_tac (EForce cli) EUnit|apply ubu_below_empty| |].
    + eapply (cs_force 7 _ Sa Sb _ _ _ true); [done|done|apply cli_typed].
    + eapply d_pair; [apply tsplit_empty|lsplit_tac (Var 3) EUnit| |].
      * eapply d_var'; [reflexivity|]. spare_tac.
      * eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

(** The merged judgment at N = ∞ types main, by conservativity. *)
Theorem cs_typed : typed W_cs None ∅ hc_empty [] (∅, None) cs_main TUnit None.
Proof. apply (dftyped_typed _ _ _ _ _ _ _ cs_dftyped). Qed.
