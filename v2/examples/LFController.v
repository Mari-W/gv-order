(** * The controller under ⊩ (stage C, proposal #20, plan §7)

      main = let (a, a′) = new_0 in let (a, ⟨b, b′⟩) = new_0 a in
             let (a, ⟨c, c′⟩) = new_2 a in
             let () = spawn (λu. let () = u in (force srv) ⟨⟨a′, b′⟩, c′⟩) in
             (force cli) ⟨⟨a, b⟩, c⟩
      cli  = !(f = λp. let (q, k) = p in let (a, b) = q in
                      let a = send ⟨∗, a⟩ in let (u, b) = recv b in
                      let () = u in (force f) ⟨⟨a, b⟩, k⟩)

    and srv the dual loop. The control channel c sits at Skip, an idle
    end on each side, and neither loop acts on it. The program is the
    client and server cycle of examples/ClientServer.v with one more
    channel at the field ρ·2 of the root. Its world W_ctl is W_cs with
    laws that put the points of a and b below the dual of c's point.

    The controller types under ⊩ at N = 3 and is lock free
    ([ctl_lock_free]). Both boxes have the type

      □∀ι κ ζ χ. C. ⟨S1@ι^1 ⊗ S2@κ^2⟩^0 ⊗ Skip@χ^0 ⊸^ζ ∗

    with C the constraint of ClientServer and ι+j ≺ χ‾, κ+j ≺ χ‾. The
    loops pass a and b as
    there, and k at credit 0. Every step a loop body takes while it holds
    k ages k by the step's cost. Rule [age_idle] of [tage] ages an idle
    end by truncation, so k stays at 0 and the argument of the self call
    has the parameter type. Without [age_idle] the controller types at no
    finite N (progress.md C.6). Rule [age_credit] would need the cost
    below the credit of k, no rule but an action raises a credit, and
    subtyping never raises a credit ([sess_sub_credit]).

    The kept-credit form of [age_idle] is unsound ([idle_age_cex]). The
    fuel skips only the checks "≥ 1" of F-Tick and the hand-over for an
    idle end. Its counter still ticks, and FV asks credit ≤ counter. *)

From GV Require Export examples.LFTools examples.LFClientServer.

(** ** The program *)

Definition ctl_cli : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Var 1) (ELet (ESend (Pair EUnit (Var 1)))
    (LetP (ERecv (Var 1)) (LetU (Var 1)
      (App (EForce (Var 8)) (Pair (Pair (Var 2) (Var 0)) (Var 5))))))))).

Definition ctl_srv : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Var 1) (LetP (ERecv (Var 1)) (LetU (Var 1)
    (ELet (ESend (Pair EUnit (Var 2)))
      (App (EForce (Var 8)) (Pair (Pair (Var 1) (Var 0)) (Var 5))))))))).

Definition ctl_main : expr :=
  let_new 0 (LetP (ENewAt 0 (Var 1)) (LetP (Var 0)
    (LetP (ENewAt 2 (Var 3)) (LetP (Var 0)
      (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce ctl_srv) (Pair (Pair (Var 9) (Var 5)) (Var 1))))))
            (App (EForce ctl_cli) (Pair (Pair (Var 3) (Var 5)) (Var 1)))))))).

(** ** The world and the boxes

    The end k is held across every action of a loop, so the future of
    each action holds its dual point. The constraint of ClientServer
    gains ι+j ≺ χ‾ and κ+j ≺ χ‾, and the laws of family 0 gain
    α+j ≺ γ‾ and β+j ≺ γ‾ for γ the point of c or c′. They rise in the
    field sum, as the laws that end at ρ·1. *)

Definition ctl_P (g : fact) : Prop :=
  ∃ k, g = FLt (sh k (pvar 0)) (sh k (pvar 1))‾ ∨ g = FLt (sh k (pvar 1)) (sh (S k) (pvar 0))‾ ∨
       g = FLt (sh k (pvar 0)) (pvar 2) ∨ g = FLt (sh k (pvar 1)) (pvar 2) ∨
       g = FLt (sh k (pvar 0)) (pvar 3)‾ ∨ g = FLt (sh k (pvar 1)) (pvar 3)‾.
Definition ctl_C : bcs := BCs [] ctl_P.

Definition ctl_L (g : fact) : Prop :=
  ∃ k (b : bool), let α := pt_polar b (pvar 0) in let β := pt_polar b ((pvar 0)·0) in
    let γ := pt_polar b ((pvar 0)·2) in
    g = FLt (sh k α) (sh k β)‾ ∨ g = FLt (sh k β) (sh (S k) α)‾ ∨
    g = FLt (sh k α) ((pvar 0)·1) ∨ g = FLt (sh k β) ((pvar 0)·1) ∨
    g = FLt (sh k α) γ‾ ∨ g = FLt (sh k β) γ‾.

Definition W_ctl : world := World ∅ (λ _, False) {[0]} (λ _ g, ctl_L g).

Ltac pick6 := first [ left; fact_eq | right; left; fact_eq | right; right; left; fact_eq
                    | right; right; right; left; fact_eq | right; right; right; right; left; fact_eq
                    | right; right; right; right; right; fact_eq ].

Lemma W_ctl_wf : world_wf W_ctl.
Proof.
  split; simpl; [done|]. intros ℓ x y _ (k & b & Hk).
  destruct b; destruct Hk as [E|[E|[E|[E|[E|E]]]]]; injection E as -> ->; done.
Qed.

Lemma W_ctl_wfworld : wfworld W_ctl.
Proof.
  apply (wfworld_lex3 W_ctl (λ x, (pt_fsum x, pt_off x, pt_depth x))); [intros f []| |].
  - intros x. unfold pt_fsum, pt_depth. simpl. lia.
  - intros ℓ g x y _ (k & b & Hk).
    destruct b; destruct Hk as [E|[E|[E|[E|[E|E]]]]]; injection E as -> ->; unfold pt_fsum, pt_depth; simpl; lia.
Qed.

Definition Γmc : hctx := hc_open 1 (bcs_of (w_laws W_ctl 0)) hc_empty.

Lemma ctl_law_fact x y :
  (∃ k (b : bool), let α := pt_polar b (pvar 0) in let β := pt_polar b ((pvar 0)·0) in
    let γ := pt_polar b ((pvar 0)·2) in
    FLt x y = FLt (sh k α) (sh k β)‾ ∨ FLt x y = FLt (sh k β) (sh (S k) α)‾ ∨
    FLt x y = FLt (sh k α) ((pvar 0)·1) ∨ FLt x y = FLt (sh k β) ((pvar 0)·1) ∨
    FLt x y = FLt (sh k α) γ‾ ∨ FLt x y = FLt (sh k β) γ‾) →
  slt W_ctl Γmc x y.
Proof.
  intros (k & b & Hk). eapply (slt_hyp _ _ ctl_L (ids 1) (FLt x y)).
  - unfold Γmc, hc_open. simpl. by left.
  - by exists k, b.
  - destruct b; destruct Hk as [E|[E|[E|[E|[E|E]]]]]; injection E as -> ->; simpl; lia.
  - destruct b; destruct Hk as [E|[E|[E|[E|[E|E]]]]]; injection E as -> ->; fact_eq.
Qed.

(** The boxes, over ι = 0, κ = 1, ζ = 2, χ = 3. *)

Definition ctl_T (S1 S2 : sty) : ty :=
  TProd (TProd (TSess S1 (pvar 0) (Some 1) (Some 3)) (TSess S2 (pvar 1) (Some 2) (Some 3)))
        (TSess SSkip (pvar 3) (Some 0) (Some 3)).
Definition ctl_box (S1 S2 : sty) : ty := lbox 4 ctl_C (Some (pvar 2)) (ctl_T S1 S2) TUnit.

(** A pair of ends beside an end whose credits fall. *)
Lemma e_sub_ctl W N Γ Δ F e S1 x S2 y S3 z a1 a2 a3 b1 b2 b3 c :
  typed W N ∅ Γ Δ F e (TProd (TProd (TSess S1 x a1 (Some 3)) (TSess S2 y a2 (Some 3))) (TSess S3 z a3 (Some 3))) c →
  fle b1 a1 → fle b2 a2 → fle b3 a3 →
  typed W N ∅ Γ Δ F e (TProd (TProd (TSess S1 x b1 (Some 3)) (TSess S2 y b2 (Some 3))) (TSess S3 z b3 (Some 3))) c.
Proof.
  intros He H1 H2 H3. eapply e_sub; [exact He| |apply fle_refl].
  apply sub_prod; [apply sub_prod|]; apply sub_sess; rewrite ?fadd_0_l; auto using sequiv_refl.
Qed.

Lemma ctl_fact W Γ x y :
  (ctl_C, ids 4) ∈ hc_hyps Γ →
  (∃ k, FLt x y = FLt (sh k (pvar 0)) (sh k (pvar 1))‾ ∨ FLt x y = FLt (sh k (pvar 1)) (sh (S k) (pvar 0))‾ ∨
       FLt x y = FLt (sh k (pvar 0)) (pvar 2) ∨ FLt x y = FLt (sh k (pvar 1)) (pvar 2) ∨
       FLt x y = FLt (sh k (pvar 0)) (pvar 3)‾ ∨ FLt x y = FLt (sh k (pvar 1)) (pvar 3)‾) →
  slt W Γ x y.
Proof.
  intros Hin (k & Hk). eapply (slt_hyp _ _ ctl_P (ids 4) (FLt x y)); [done|by exists k| |].
  - destruct Hk as [E|[E|[E|[E|[E|E]]]]]; injection E as -> ->; simpl; lia.
  - destruct Hk as [E|[E|[E|[E|[E|E]]]]]; injection E as -> ->; fact_eq.
Qed.

Section body.
  Context (W : world) (Γ : hctx) (n : nat).
  Local Definition Γc : hctx := hc_open 4 ctl_C Γ.

  Lemma ctl_in : (ctl_C, ids 4) ∈ hc_hyps Γc.
  Proof. unfold Γc, hc_open. simpl. apply elem_of_app. right. by left. Qed.


  Ltac fct k := apply ctl_fact; [apply ctl_in|exists k; pick6].

  Ltac dfut x :=
    apply (ub_below_varb _ _ x (pvar 2) _ _); [bot_false|
      let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; heads_simpl Hy;
      repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst;
      try contradiction; first [fct 0 | fct 1]
    | right; fct 0 ].

  (** The force of the self at (ι⁺, κ⁺, ζ, χ). *)
  Lemma ctl_hold : hold_at W Γc ctl_C (sh 1 (pvar 0) :: sh 1 (pvar 1) :: pvar 2 :: pvar 3 :: []).
  Proof.
    apply hold_at_nil. intros f (k & Hf) _.
    destruct Hf as [->|[->|[->|[->|[->| ->]]]]]; simpl; fct (S k).
  Qed.

  Lemma ctl_self Δ F S1 S2 :
    Δ !! 8 = Some (Some (ctl_box S1 S2)) → (∀ y o, y ≠ 8 → Δ !! y = Some o → spare o) →
    typed W (Some 6) ∅ Γc Δ F (EForce (Var 8)) (TLolli (UPt (pvar 2)) LNone None (TProd (TProd (TSess S1 (sh 1 (pvar 0)) (Some 1) (Some 3)) (TSess S2 (sh 1 (pvar 1)) (Some 2) (Some 3)))
                (TSess SSkip (pvar 3) (Some 0) (Some 3))) TUnit None) (fadd (Some 0) (Some 0)).
  Proof.
    intros H8 Hs. eapply (lbox_force_eq _ _ _ _ _ _ 4 ctl_C (Some (pvar 2)) (ctl_T S1 S2) TUnit
      (sh 1 (pvar 0) :: sh 1 (pvar 1) :: pvar 2 :: pvar 3 :: [])); [done|apply ctl_hold|done|done|done|].
    by apply e_var'.
  Qed.

  Lemma ctl_cli_body : ∃ c,
    typed W (Some 6) ∅ Γc (Some (ctl_T Sa Sb) :: Some (ctl_box Sa Sb) :: nones n) (∅, Some (FRest (RAbove (pvar 2)))) (LetP (Var 0) (LetP (Var 1) (ELet (ESend (Pair EUnit (Var 1)))
        (LetP (ERecv (Var 1)) (LetU (Var 1)
          (App (EForce (Var 8)) (Pair (Pair (Var 2) (Var 0)) (Var 5)))))))) TUnit c.
  Proof.
    eexists _.
    { eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Var 1) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac. 
    eapply e_let_; [lsplit_tac (ESend (Pair EUnit (Var 1))) EUnit| | | ].
    { eapply e_send with (x := pvar 0) (m := 0) (T := TUnit) (Tp := TUnit) (S0 := Sa);
        [exact unfold_Sa|exact I|done|cbn; set_solver|dfut (pvar 0)| |age_tac|shelve].
      eapply e_pair_; [lsplit_tac EUnit (Var 1)| | | | ].
      { apply e_unit'. spare_tac. }
      lage_tac.
      { eapply e_var'; [reflexivity|]. spare_tac. }
      age_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (ERecv (Var 1)) EUnit| | | ].
    { eapply e_recv with (x := pvar 1) (m := 0) (T := TUnit) (S0 := Sb);
        [exact unfold_Sb|exact I|dfut (pvar 1)|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (Var 1) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_app_; [lsplit_tac (EForce (Var 8)) EUnit| | | | |shelve].
    { apply ubu_pt; eapply (ub_below_var _ _ _ (pvar 2) _); [intros y Hy; exfalso; set_solver|by left]. }
    { apply ctl_self; [reflexivity|spare_tac]. }
    lage_tac.
    eapply e_sub_ctl; [|shelve|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Pair (Var 2) (Var 0)) EUnit| | | | ].
    { eapply e_pair_; [lsplit_tac (Var 2) EUnit| | | | ].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      { eapply e_var'; [reflexivity|]. spare_tac. }
      age_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
    Unshelve. all: first [apply tsub_refl | exact None | simpl; lia | simpl; done].
  Qed.

  Lemma ctl_srv_body : ∃ c,
    typed W (Some 6) ∅ Γc (Some (ctl_T Sb Sa) :: Some (ctl_box Sb Sa) :: nones n) (∅, Some (FRest (RAbove (pvar 2)))) (LetP (Var 0) (LetP (Var 1) (LetP (ERecv (Var 1)) (LetU (Var 1)
        (ELet (ESend (Pair EUnit (Var 2)))
          (App (EForce (Var 8)) (Pair (Pair (Var 1) (Var 0)) (Var 5)))))))) TUnit c.
  Proof.
    eexists _.
    { eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (Var 1) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (ERecv (Var 1)) EUnit| | | ].
    { eapply e_recv with (x := pvar 0) (m := 0) (T := TUnit) (S0 := Sb);
        [exact unfold_Sb|exact I|dfut (pvar 0)|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (Var 1) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac. 
    eapply e_let_; [lsplit_tac (ESend (Pair EUnit (Var 2))) EUnit| | | ].
    { eapply e_send with (x := pvar 1) (m := 0) (T := TUnit) (Tp := TUnit) (S0 := Sa);
        [exact unfold_Sa|exact I|done|cbn; set_solver|dfut (pvar 1)| |age_tac|shelve].
      eapply e_pair_; [lsplit_tac EUnit (Var 2)| | | | ].
      { apply e_unit'. spare_tac. }
      lage_tac.
      { eapply e_var'; [reflexivity|]. spare_tac. }
      age_tac. }
    lage_tac.
    eapply e_app_; [lsplit_tac (EForce (Var 8)) EUnit| | | | |shelve].
    { apply ubu_pt; eapply (ub_below_var _ _ _ (pvar 2) _); [intros y Hy; exfalso; set_solver|by left]. }
    { apply ctl_self; [reflexivity|spare_tac]. }
    lage_tac.
    eapply e_sub_ctl; [|shelve|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Pair (Var 1) (Var 0)) EUnit| | | | ].
    { eapply e_pair_; [lsplit_tac (Var 1) EUnit| | | | ].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      { eapply e_var'; [reflexivity|]. spare_tac. }
      age_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
    Unshelve. all: first [apply tsub_refl | exact None | simpl; lia | simpl; done].
  Qed.
End body.

Lemma ctl_cli_typed Γ n F : typed W_ctl (Some 6) ∅ Γ (nones n) F ctl_cli (ctl_box Sa Sb) (Some 0).
Proof.
  destruct (ctl_cli_body W_ctl Γ n) as (c & Hb).
  eapply lbox_typed; [reflexivity|exact Hb].
Qed.

Lemma ctl_srv_typed Γ n F : typed W_ctl (Some 6) ∅ Γ (nones n) F ctl_srv (ctl_box Sb Sa) (Some 0).
Proof.
  destruct (ctl_srv_body W_ctl Γ n) as (c & Hb).
  eapply lbox_typed; [reflexivity|exact Hb].
Qed.

Lemma ctl_hold_main (b : bool) :
  hold_at W_ctl Γmc ctl_C
    (pt_polar b (pvar 0) :: pt_polar b ((pvar 0)·0) :: (pvar 0)·1 :: pt_polar b ((pvar 0)·2) :: []).
Proof.
  apply hold_at_nil. intros f (k & Hf) _.
  destruct Hf as [->|[->|[->|[->|[->| ->]]]]]; simpl; apply ctl_law_fact; exists k, b; destruct b; pick6.
Qed.

(** ** main at N = 3 *)

Lemma ctl_typedN : ∃ c, typed W_ctl (Some 6) ∅ hc_empty [] (∅, None) ctl_main TUnit c.
Proof.
  eexists _.
  { unfold ctl_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | ].
  { apply (e_new' _ _ _ _ _ _ Sa); [spare_tac|set_solver]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold Γmc.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (ENewAt 0 (Var 1)) EUnit| | | ].
  { eapply (e_new_at _ _ _ _ _ _ _ 0 Sa (pvar 0) _ _ Sb); [|shelve]. eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (ENewAt 2 (Var 3)) EUnit| | | ].
  { eapply (e_new_at _ _ _ _ _ _ _ 2 Sa (pvar 0) _ _ SSkip); [|shelve]. eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0)
                     (App (EForce ctl_srv) (Pair (Pair (Var 9) (Var 5)) (Var 1)))))) EUnit
                  | | |].
  { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_app_; [lsplit_tac (EForce ctl_srv) EUnit|apply ubu_below_empty| | | |shelve].
    { eapply (lbox_force_eq _ _ _ _ _ _ 4 ctl_C (Some (pvar 2)) (ctl_T Sb Sa) TUnit (pt_polar false (pvar 0) :: pt_polar false ((pvar 0)·0) :: (pvar 0)·1 :: pt_polar false ((pvar 0)·2) :: []) _ (UPt ((pvar 0)·1)) (TProd (TProd (TSess Sb (pvar 0)‾ (Some 1) (Some 3)) (TSess Sa ((pvar 0)·0)‾ (Some 2) (Some 3)))
               (TSess SSkip ((pvar 0)·2)‾ (Some 0) (Some 3))));
        [done|apply ctl_hold_main|done|done|done|].
      apply (ctl_srv_typed _ 12). }
    lage_tac.
    eapply e_sub_ctl; [|shelve|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Pair (Var 9) (Var 5)) EUnit| | | | ].
    { eapply e_pair_; [lsplit_tac (Var 9) EUnit| | | | ].
      { eapply e_var'; [reflexivity|]. spare_tac. }
      lage_tac.
      { eapply e_var'; [reflexivity|]. spare_tac. }
      age_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
  lage_tac.
  eapply e_app_; [lsplit_tac (EForce ctl_cli) EUnit|apply ubu_below_empty| | | |shelve].
  { eapply (lbox_force_eq _ _ _ _ _ _ 4 ctl_C (Some (pvar 2)) (ctl_T Sa Sb) TUnit (pt_polar true (pvar 0) :: pt_polar true ((pvar 0)·0) :: (pvar 0)·1 :: pt_polar true ((pvar 0)·2) :: []) _ (UPt ((pvar 0)·1)) (TProd (TProd (TSess Sa (pvar 0) (Some 1) (Some 3)) (TSess Sb ((pvar 0)·0) (Some 2) (Some 3)))
             (TSess SSkip ((pvar 0)·2) (Some 0) (Some 3))));
      [done|apply ctl_hold_main|done|done|done|].
    apply (ctl_cli_typed _ 11). }
  lage_tac.
  eapply e_sub_ctl; [|shelve|shelve|shelve].
  eapply e_pair_; [lsplit_tac (Pair (Var 3) (Var 5)) EUnit| | | | ].
  { eapply e_pair_; [lsplit_tac (Var 3) EUnit| | | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
  lage_tac.
  { eapply e_var'; [reflexivity|]. spare_tac. }
  age_tac. }
  Unshelve. all: first [exact None | simpl; lia | simpl; done].
Qed.

Lemma ctl_guarded : ∅ ⊢▷ ctl_main.
Proof. unfold ctl_main, ctl_cli, ctl_srv, let_new. guard_tac. Qed.

Theorem ctl_lftyped : ∃ N, ∅ ⊩^N _ W_ctl (∅, {[+ ctl_main +]}) : TUnit.
Proof.
  destruct ctl_typedN as (c & Ht). exists 6.
  eapply lf_main_typed; [apply strict_wfworld; [apply W_ctl_wf|apply W_ctl_wfworld]|constructor|exact Ht|apply ctl_guarded].
Qed.

Theorem ctl_lock_free : lock_free (∅, {[+ ctl_main +]}).
Proof.
  destruct ctl_typedN as (c & Ht).
  eapply lf_main; [apply (strict_wfworld _ W_ctl_wf W_ctl_wfworld)|apply W_ctl_wfworld|constructor|exact Ht|apply ctl_guarded].
Qed.
