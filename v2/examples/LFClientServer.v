(** * The client and server cycle is lock free (stage S9)

    The program of examples/ClientServer.v types at the bound N = 6, so every end has N/2 = 3 tickets.
    Both loops take ⟨a, b⟩ at credits 1 and 2. A send or receive returns
    its end at credit 3, and the end held across it loses 1, so each
    self call passes credits 2 and 3, which fall to 1 and 2 by
    subtyping. main passes 3 and 3, the server thread 2 and 2 after the
    spawn. Every call is the last step of its thread, so the arrow may
    cost ∞. The world is a lock-free world by the measure (field sum,
    offset, depth): the laws rise in offset or depth, except those that
    end at ρ·1, which rise in the field sum. *)

From GV Require Export examples.LFTools examples.ClientServer.

Definition csl_T (S1 S2 : sty) : ty := TProd (TSess S1 (pvar 0) (Some 1) (Some 3)) (TSess S2 (pvar 1) (Some 2) (Some 3)).
Definition csl_box (S1 S2 : sty) : ty := lbox 3 cs_C (Some (pvar 2)) (csl_T S1 S2) TUnit.

Section body.
  Context (W : sworld) (Γ : hctx) (n : nat).
  Local Definition Γl : hctx := hc_open 3 cs_C Γ.

  Lemma csl_in : (cs_C, ids 3) ∈ hc_hyps Γl.
  Proof. unfold Γl, hc_open. simpl. apply elem_of_app. right. by left. Qed.


  Ltac fct k := apply cs_fact; [apply csl_in|exists k;
    first [left; fact_eq | right; left; fact_eq | right; right; left; fact_eq | right; right; right; fact_eq]].

  Ltac dfut x :=
    apply (ub_below_varb _ _ x (pvar 2) _ _); [bot_false|
      let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; heads_simpl Hy;
      repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst;
      try contradiction; first [fct 0 | fct 1]
    | right; fct 0 ].

  (** The force of the self at (ι⁺, κ⁺, ζ). *)
  Lemma csl_hold : hold_at W Γl cs_C (sh 1 (pvar 0) :: sh 1 (pvar 1) :: pvar 2 :: []).
  Proof.
    apply hold_at_nil. intros f (k & Hf) _.
    destruct Hf as [->|[->|[->| ->]]]; simpl; fct (S k).
  Qed.

  Lemma csl_self Δ F S1 S2 :
    Δ !! 6 = Some (Some (csl_box S1 S2)) → (∀ y o, y ≠ 6 → Δ !! y = Some o → spare o) →
    typed W (Some 6) ∅ Γl Δ F (EForce (Var 6)) (TLolli (UPt (pvar 2)) LNone None (TProd (TSess S1 (sh 1 (pvar 0)) (Some 1) (Some 3)) (TSess S2 (sh 1 (pvar 1)) (Some 2) (Some 3))) TUnit None) (fadd (Some 0) (Some 0)).
  Proof.
    intros H6 Hs. eapply (lbox_force_eq _ _ _ _ _ _ 3 cs_C (Some (pvar 2)) (csl_T S1 S2) TUnit
      (sh 1 (pvar 0) :: sh 1 (pvar 1) :: pvar 2 :: [])); [done|apply csl_hold|done|done|done|].
    by apply e_var'.
  Qed.

  Lemma csl_cli : ∃ c,
    typed W (Some 6) ∅ Γl (Some (csl_T Sa Sb) :: Some (csl_box Sa Sb) :: nones n) (∅, Some (FRest (RAbove (pvar 2)))) (LetP (Var 0) cli_e) TUnit c.
  Proof.
    eexists _.
    { eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac. unfold cli_e.
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
    eapply e_app_; [lsplit_tac (EForce (Var 6)) EUnit| | | | |shelve].
    { apply ubu_pt; eapply (ub_below_var _ _ _ (pvar 2) _); [intros y Hy; exfalso; set_solver|by left]. }
    { apply csl_self; [reflexivity|spare_tac]. }
    lage_tac.
    eapply e_sub_sess2; [|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Var 2) EUnit| | | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
    Unshelve. all: first [apply tsub_refl | exact None | simpl; lia | simpl; done].
  Qed.

  Lemma csl_srv : ∃ c,
    typed W (Some 6) ∅ Γl (Some (csl_T Sb Sa) :: Some (csl_box Sb Sa) :: nones n) (∅, Some (FRest (RAbove (pvar 2)))) (LetP (Var 0) srv_e) TUnit c.
  Proof.
    eexists _.
    { eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac. unfold srv_e.
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
    eapply e_app_; [lsplit_tac (EForce (Var 6)) EUnit| | | | |shelve].
    { apply ubu_pt; eapply (ub_below_var _ _ _ (pvar 2) _); [intros y Hy; exfalso; set_solver|by left]. }
    { apply csl_self; [reflexivity|spare_tac]. }
    lage_tac.
    eapply e_sub_sess2; [|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Var 1) EUnit| | | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
    Unshelve. all: first [apply tsub_refl | exact None | simpl; lia | simpl; done].
  Qed.
End body.

Lemma csl_cli_typed Γ n F : typed W_cs (Some 6) ∅ Γ (nones n) F cli (csl_box Sa Sb) (Some 0).
Proof.
  destruct (csl_cli W_cs Γ n) as (c & Hb).
  eapply lbox_typed; [contr_tac|contr_tac|reflexivity|exact Hb].
Qed.

Lemma csl_srv_typed Γ n F : typed W_cs (Some 6) ∅ Γ (nones n) F srv (csl_box Sb Sa) (Some 0).
Proof.
  destruct (csl_srv W_cs Γ n) as (c & Hb).
  eapply lbox_typed; [contr_tac|contr_tac|reflexivity|exact Hb].
Qed.

Lemma csl_hold_main (b : bool) :
  hold_at W_cs Γm cs_C (pt_polar b (pvar 0) :: pt_polar b ((pvar 0)·0) :: (pvar 0)·1 :: []).
Proof.
  apply hold_at_nil. intros f (k & Hf) _.
  destruct Hf as [->|[->|[->| ->]]]; simpl; apply law_fact; exists k, b; destruct b;
    first [left; fact_eq | right; left; fact_eq | right; right; left; fact_eq | right; right; right; fact_eq].
Qed.

Lemma csl_typedN : ∃ c, typed W_cs (Some 6) ∅ hc_empty [] (∅, None) cs_main TUnit c.
Proof.
  eexists _.
  { unfold cs_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | ].
  { eapply (e_new' _ _ _ _ _ _ Sa); [spare_tac|apply cs_wf_new|contr_tac]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold Γm.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Pair (Var 1) ENew) EUnit| | | ].
  { eapply (e_new_at' _ _ _ _ _ _ _ 0 Sa (pvar 0) _ _ Sb); [done|shelve|reflexivity| |contr_tac]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce srv) (Pair (Var 5) (Var 1)))))) EUnit
                  | | |].
  { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_app_; [lsplit_tac (EForce srv) EUnit|apply ubu_below_empty| | | |shelve].
    { eapply (lbox_force_eq _ _ _ _ _ _ 3 cs_C (Some (pvar 2)) (csl_T Sb Sa) TUnit (pt_polar false (pvar 0) :: pt_polar false ((pvar 0)·0) :: (pvar 0)·1 :: []) _ (UPt ((pvar 0)·1)) (TProd (TSess Sb (pvar 0)‾ (Some 1) (Some 3)) (TSess Sa ((pvar 0)·0)‾ (Some 2) (Some 3))));
        [done|apply csl_hold_main|done|done|done|].
      apply (csl_srv_typed _ 8). }
    lage_tac.
    eapply e_sub_sess2; [|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Var 5) EUnit| | | | ].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
  lage_tac.
  eapply e_app_; [lsplit_tac (EForce cli) EUnit|apply ubu_below_empty| | | |shelve].
  { eapply (lbox_force_eq _ _ _ _ _ _ 3 cs_C (Some (pvar 2)) (csl_T Sa Sb) TUnit (pt_polar true (pvar 0) :: pt_polar true ((pvar 0)·0) :: (pvar 0)·1 :: []) _ (UPt ((pvar 0)·1)) (TProd (TSess Sa (pvar 0) (Some 1) (Some 3)) (TSess Sb ((pvar 0)·0) (Some 2) (Some 3))));
      [done|apply csl_hold_main|done|done|done|].
    apply (csl_cli_typed _ 7). }
  lage_tac.
  eapply e_sub_sess2; [|shelve|shelve].
  eapply e_pair_; [lsplit_tac (Var 3) EUnit| | | | ].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  { eapply e_var'; [reflexivity|]. spare_tac. }
  age_tac. }
  Unshelve. all: first [exact None | simpl; lia | simpl; done].
Qed.

Lemma cs_guarded : ∅ ⊢▷ cs_main.
Proof. unfold cs_main, cli, srv, let_new. guard_tac. Qed.

Theorem cs_lftyped : ∃ N, ∅ ⊩^N _ W_cs (∅, {[+ cs_main +]}) : TUnit.
Proof.
  destruct csl_typedN as (c & Ht). exists 6.
  eapply lf_main_typed; [apply W_cs_wf|constructor|exact Ht|apply cs_guarded].
Qed.

Theorem cs_lock_free : excluded_middle → functional_choice → lock_free (∅, {[+ cs_main +]}).
Proof.
  intros EM FC. destruct csl_typedN as (c & Ht).
  eapply (lf_main EM FC); [apply W_cs_wf|constructor|exact Ht|apply cs_guarded].
Qed.
