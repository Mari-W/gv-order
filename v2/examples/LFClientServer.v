(** * The client and server cycle is lock free (stage S9)

    The program of examples/ClientServer.v types at the refill N = 3.
    Both loops take ⟨a, b⟩ at credits 1 and 2. A send or receive returns
    its end at credit 3, and the end held across it loses 1, so each
    self call passes credits 2 and 3, which fall to 1 and 2 by
    subtyping. main passes 3 and 3, the server thread 2 and 2 after the
    spawn. Every call is the last step of its thread, so the arrow may
    cost ∞. The world is a lock-free world by the measure (field sum,
    offset, depth): the laws rise in offset or depth, except those that
    end at ρ·1, which rise in the field sum. *)

From GV Require Export examples.LFTools examples.ClientServer.

Lemma W_cs_wf : world_wf W_cs.
Proof.
  split; simpl; [done|]. intros ℓ x y _ (k & b & Hk).
  destruct b; destruct Hk as [E|[E|[E|E]]]; injection E as -> ->; done.
Qed.

Lemma W_cs_lfworld : lfworld W_cs.
Proof.
  apply (lfworld_lex3 W_cs (λ x, (pt_fsum x, pt_off x, pt_depth x))); [apply W_cs_wf|intros f []| |].
  - intros x. unfold pt_fsum, pt_depth. simpl. lia.
  - intros ℓ g x y _ (k & b & Hk).
    destruct b; destruct Hk as [E|[E|[E|E]]]; injection E as -> ->; unfold pt_fsum, pt_depth; simpl; lia.
Qed.

Definition csl_T (S1 S2 : sty) : ty := TProd (TSess S1 (pvar 0)) (Some 1) (TSess S2 (pvar 1)) (Some 2).
Definition csl_box (S1 S2 : sty) : ty := lbox 3 cs_C (Some (pvar 2)) (csl_T S1 S2) (Some 0) TUnit None.

(** A pair of ends whose credits fall. *)
Lemma e_sub_sess2 W N Γ Δ F e S1 x S2 y a1 a2 b1 b2 c t :
  typed W N ∅ Γ Δ F e (TProd (TSess S1 x) a1 (TSess S2 y) a2) (Some 0) c t →
  fle b1 a1 → fle b2 a2 →
  typed W N ∅ Γ Δ F e (TProd (TSess S1 x) b1 (TSess S2 y) b2) (Some 0) c t.
Proof.
  intros He H1 H2. eapply e_sub; [exact He| |apply fle_refl|apply tle_refl].
  apply sub_prod; apply sub_sess; rewrite ?fadd_0_l; auto using sequiv_refl.
Qed.

Section body.
  Context (W : world) (Γ : hctx) (n : nat).
  Local Definition Γl : hctx := hc_fvar 1 (Some (pvar 2)) (hc_fvar 0 None (hc_open 3 cs_C Γ)).

  Lemma csl_in : (cs_C, ids 3) ∈ hc_hyps Γl.
  Proof. unfold Γl, hc_fvar, hc_open. simpl. apply elem_of_app. right. by left. Qed.

  Lemma φl_hyp : hc_fv Γl !! 1 = Some (Some (pvar 2)).
  Proof. unfold Γl, hc_fvar. simpl. by rewrite lookup_insert_eq. Qed.

  Ltac fct k := apply cs_fact; [apply csl_in|exists k;
    first [left; fact_eq | right; left; fact_eq | right; right; left; fact_eq | right; right; right; fact_eq]].

  Ltac dfut x :=
    apply (ub_below_varb _ _ x (pvar 2) _ _ 1); [bot_false|exact φl_hyp|
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
    Δ !! 6 = Some (Some (csl_box S1 S2, None)) → (∀ y o, y ≠ 6 → Δ !! y = Some o → spare o) →
    typed W (Some 3) ∅ Γl Δ F (EForce (Var 6))
      (TLolli (Some (pvar 2)) None None tz (Some 0)
         (TProd (TSess S1 (sh 1 (pvar 0))) (Some 1) (TSess S2 (sh 1 (pvar 1))) (Some 2)) (Some 0) TUnit None)
      None (fadd (Some 0) (Some 0)) (tseq tid tid).
  Proof.
    intros H6 Hs. eapply (lbox_force_eq _ _ _ _ _ _ 3 cs_C (Some (pvar 2)) (csl_T S1 S2) (Some 0) TUnit None
      (sh 1 (pvar 0) :: sh 1 (pvar 1) :: pvar 2 :: [])); [done|apply csl_hold|done|done|done|].
    by apply e_var'.
  Qed.

  Lemma csl_cli : ∃ c t,
    typed W (Some 3) ∅ Γl (Some (csl_T Sa Sb, Some 0) :: Some (csl_box Sa Sb, None) :: nones n)
      (∅, Some (FVar 1)) (LetP (Var 0) cli_e) TUnit None c t ∧ t.2 = Some 0.
  Proof.
    eexists _, _. split.
    { eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac. unfold cli_e, elet.
    eapply e_let_; [lsplit_tac (ESend (Pair EUnit (Var 1))) EUnit| | | |shelve].
    { eapply e_send with (x := pvar 0) (m := 0) (T := TUnit) (b := None) (S0 := Sa);
        [exact unfold_Sa|exact I|done|cbn; set_solver|dfut (pvar 0)| |age_tac|shelve].
      eapply e_pair_; [lsplit_tac EUnit (Var 1)| | | | |shelve].
      { apply e_unit'. spare_tac. }
      lage_tac.
      { eapply e_var'; [reflexivity|]. spare_tac. }
      age_tac. }
    lage_tac.
    eapply e_letp_; [lsplit_tac (ERecv (Var 1)) EUnit| | | |shelve].
    { eapply e_recv with (x := pvar 1) (m := 0) (T := TUnit) (b := None) (S0 := Sb);
        [exact unfold_Sb|exact I|dfut (pvar 1)|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (Var 1) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_app_; [lsplit_tac (EForce (Var 6)) EUnit| | | | |shelve|shelve|shelve].
    { eapply (ub_below_var _ _ _ (pvar 2) _ 1 φl_hyp); [intros y Hy; exfalso; set_solver|by left]. }
    { apply csl_self; [reflexivity|spare_tac]. }
    lage_tac.
    eapply e_sub_sess2; [|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Var 2) EUnit| | | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
    reflexivity.
    Unshelve. all: first [tok_tac | apply tsub_refl | exact None | simpl; lia | simpl; done].
  Qed.

  Lemma csl_srv : ∃ c t,
    typed W (Some 3) ∅ Γl (Some (csl_T Sb Sa, Some 0) :: Some (csl_box Sb Sa, None) :: nones n)
      (∅, Some (FVar 1)) (LetP (Var 0) srv_e) TUnit None c t ∧ t.2 = Some 0.
  Proof.
    eexists _, _. split.
    { eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac. unfold srv_e, elet.
    eapply e_letp_; [lsplit_tac (ERecv (Var 1)) EUnit| | | |shelve].
    { eapply e_recv with (x := pvar 0) (m := 0) (T := TUnit) (b := None) (S0 := Sb);
        [exact unfold_Sb|exact I|dfut (pvar 0)|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_letu_; [lsplit_tac (Var 1) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_let_; [lsplit_tac (ESend (Pair EUnit (Var 2))) EUnit| | | |shelve].
    { eapply e_send with (x := pvar 1) (m := 0) (T := TUnit) (b := None) (S0 := Sa);
        [exact unfold_Sa|exact I|done|cbn; set_solver|dfut (pvar 1)| |age_tac|shelve].
      eapply e_pair_; [lsplit_tac EUnit (Var 2)| | | | |shelve].
      { apply e_unit'. spare_tac. }
      lage_tac.
      { eapply e_var'; [reflexivity|]. spare_tac. }
      age_tac. }
    lage_tac.
    eapply e_app_; [lsplit_tac (EForce (Var 6)) EUnit| | | | |shelve|shelve|shelve].
    { eapply (ub_below_var _ _ _ (pvar 2) _ 1 φl_hyp); [intros y Hy; exfalso; set_solver|by left]. }
    { apply csl_self; [reflexivity|spare_tac]. }
    lage_tac.
    eapply e_sub_sess2; [|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Var 1) EUnit| | | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
    reflexivity.
    Unshelve. all: first [tok_tac | apply tsub_refl | exact None | simpl; lia | simpl; done].
  Qed.
End body.

Lemma csl_cli_typed Γ n F : hc_fv Γ = ∅ →
  typed W_cs (Some 3) ∅ Γ (nones n) F cli (csl_box Sa Sb) None (Some 0) tid.
Proof.
  intros HΓ. destruct (csl_cli W_cs Γ n) as (c & t & Hb & Ht).
  eapply lbox_typed; [done|reflexivity|exact Hb|exact Ht].
Qed.

Lemma csl_srv_typed Γ n F : hc_fv Γ = ∅ →
  typed W_cs (Some 3) ∅ Γ (nones n) F srv (csl_box Sb Sa) None (Some 0) tid.
Proof.
  intros HΓ. destruct (csl_srv W_cs Γ n) as (c & t & Hb & Ht).
  eapply lbox_typed; [done|reflexivity|exact Hb|exact Ht].
Qed.

Lemma csl_hold_main (b : bool) :
  hold_at W_cs Γm cs_C (pt_polar b (pvar 0) :: pt_polar b ((pvar 0)·0) :: (pvar 0)·1 :: []).
Proof.
  apply hold_at_nil. intros f (k & Hf) _.
  destruct Hf as [->|[->|[->| ->]]]; simpl; apply law_fact; exists k, b; destruct b;
    first [left; fact_eq | right; left; fact_eq | right; right; left; fact_eq | right; right; right; fact_eq].
Qed.

Lemma csl_typedN : ∃ c ϑ, typed W_cs (Some 3) ∅ hc_empty [] (∅, None) cs_main TUnit None c ϑ ∧ meets ϑ 0 0.
Proof.
  eexists _, _. split.
  { unfold cs_main, let_new.
  eapply e_let_; [apply lsplit_nil| | | |shelve].
  { apply (e_new' _ _ _ _ _ _ Sa); [spare_tac|set_solver]. }
  lage_tac.
  eapply e_open with (i := 0); [reflexivity|cbn; tauto|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold Γm.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (ENewAt 0 (Var 1)) EUnit| | | |shelve].
  { eapply (e_new_at _ _ _ _ _ _ _ 0 Sa (pvar 0) _ Sb). eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letp_; [lsplit_tac (Var 0) EUnit| | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_letu_; [lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce srv) (Pair (Var 5) (Var 1)))))) EUnit
                  | | | |shelve].
  { eapply e_spawn_lam; [apply thage_empty|lage_tac|].
    eapply e_letu_; [lsplit_tac (Var 0) EUnit| | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    eapply e_app_; [lsplit_tac (EForce srv) EUnit|apply ub_below_empty| | | |shelve|shelve|shelve].
    { eapply (lbox_force_eq _ _ _ _ _ _ 3 cs_C (Some (pvar 2)) (csl_T Sb Sa) (Some 0) TUnit None
        (pt_polar false (pvar 0) :: pt_polar false ((pvar 0)·0) :: (pvar 0)·1 :: []) _ _ _
        (Some ((pvar 0)·1)) (TProd (TSess Sb (pvar 0)‾) (Some 1) (TSess Sa ((pvar 0)·0)‾) (Some 2)));
        [done|apply csl_hold_main|done|done|done|].
      apply (csl_srv_typed _ 8). done. }
    lage_tac.
    eapply e_sub_sess2; [|shelve|shelve].
    eapply e_pair_; [lsplit_tac (Var 5) EUnit| | | | |shelve].
    { eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    { eapply e_var'; [reflexivity|]. spare_tac. }
    age_tac. }
  lage_tac.
  eapply e_app_; [lsplit_tac (EForce cli) EUnit|apply ub_below_empty| | | |shelve|shelve|shelve].
  { eapply (lbox_force_eq _ _ _ _ _ _ 3 cs_C (Some (pvar 2)) (csl_T Sa Sb) (Some 0) TUnit None
      (pt_polar true (pvar 0) :: pt_polar true ((pvar 0)·0) :: (pvar 0)·1 :: []) _ _ _
      (Some ((pvar 0)·1)) (TProd (TSess Sa (pvar 0)) (Some 1) (TSess Sb ((pvar 0)·0)) (Some 2)));
      [done|apply csl_hold_main|done|done|done|].
    apply (csl_cli_typed _ 7). done. }
  lage_tac.
  eapply e_sub_sess2; [|shelve|shelve].
  eapply e_pair_; [lsplit_tac (Var 3) EUnit| | | | |shelve].
  { eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  { eapply e_var'; [reflexivity|]. spare_tac. }
  age_tac. }
  meets_tac.
  Unshelve. all: first [tok_tac | exact None | simpl; lia | simpl; done].
Qed.

Lemma cs_guarded : guarded cs_main.
Proof. unfold guarded, cs_main, cli, srv, let_new, elet. guard_tac. Qed.

Theorem cs_lftyped : ∃ N, ∅ ⊩^N _ W_cs (∅, {[+ cs_main +]}) : TUnit.
Proof.
  destruct csl_typedN as (c & ϑ & Ht & Hm). exists 3.
  eapply lf_main_typed; [constructor|exact Ht|apply cs_guarded|exact Hm].
Qed.

Theorem cs_lock_free : lock_free (∅, {[+ cs_main +]}).
Proof.
  destruct csl_typedN as (c & ϑ & Ht & Hm).
  eapply lf_main; [apply W_cs_lfworld|constructor|exact Ht|apply cs_guarded|exact Hm].
Qed.
