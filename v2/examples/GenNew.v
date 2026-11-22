(** * Creations that use the generality of (gen-new)

    Two closed programs whose second creation has a constraint with exits,
    facts from the new tree to points of the context. (wf-new) admits no
    exit, so it rejects both creations. The examples of
    docs/redesign/check-general-new.md, section 6.

    - Two upper bounds. Γ has ρ·1 ≺ ρ̄ and ρ ≺ (ρ·0)‾, C has π ≺ ρ̄ and
      π ≺ (ρ·0)‾. The point π pairs with ρ·1 for the first exit and with
      ρ for the second, two partners for one point, so a relation S is
      needed (gen-new₁).
    - Two entries. Γ has ρ·0 ≺ ρ·2 ≺ ρ̄ and ρ·1 ≺ ρ·3 ≺ ρ̄, C has
      ρ·0 ≺ π, ρ·1 ≺ π and π ≺ ρ̄. The point π pairs with the set
      {ρ·2, ρ·3}, because no point of Γ lies above both entries (gen-new).

    Each program is typed end to end and deadlock free by
    [soundness_source]. [tu_rejected_wf_new] and [te_rejected_wf_new]:
    under every constraint that (wf-new) accepts, the opened context
    derives no fact from the new root to ρ̄, which the close of d asks. *)

From GV Require Export examples.Tools2 static.FundamentalProc examples.SemBranch.

(** ** Tools *)

(** A fact of a hypothesis of Γ with outer points. *)
Lemma slt_hyp_env W Γ C xs f x y :
  (C, xs) ∈ hc_hyps Γ → bc_facts C f → fact_scoped (length xs + length (bc_env C)) f →
  fact_map (pt_inst (plist xs)) (fact_map (pt_inst (pup (length xs) (plist (bc_env C)))) f) = FLt x y →
  slt W Γ x y.
Proof.
  intros Hin Hf Hs Hxy. apply fl_h. exists C, xs. split; [done|].
  exists (fact_map (pt_inst (pup (length xs) (plist (bc_env C)))) f). split; [|by rewrite Hxy].
  exists f. done.
Qed.

(** Program order alone is well-founded on the new tree when no fact of
    C joins two of its points. *)
Lemma wf_step_po C :
  (∀ x y, cfact C x y → in_tree0 x → in_tree0 y → False) → well_founded (new_step C).
Proof.
  intros HC. assert (∀ n x, pt_off x = n → Acc (new_step C) x) as H.
  { intros n. induction n as [n IH] using lt_wf_ind.
    intros x <-. constructor. intros y (Hy & Hx & [Hf|[->| ->]]).
    - exfalso. by apply (HC y x).
    - apply (IH (pt_off y)); [simpl; lia|done].
    - apply (IH (pt_off y)); [simpl; lia|done]. }
  intros x. by apply (H (pt_off x)).
Qed.

(** The root of the new tree has no step below it. *)
Lemma new_step_root C s : (∀ x, cfact C x (pvar 0) → in_tree0 x → False) → ¬ new_step C s (pvar 0).
Proof.
  intros HC (Hs & _ & [[Hf Hsc]|[E|E]]).
  - by apply (HC s); [split|].
  - apply (f_equal pt_off) in E. simpl in E. lia.
  - apply (f_equal pt_off) in E. simpl in E. lia.
Qed.

Ltac nt H := vm_compute in H; congruence.
Ltac disj_tac := hnf; repeat first [left; reflexivity | right]; reflexivity.

Lemma d_new_gen W Γ Δ F C S a1 a2 mt :
  (∀ y o, Δ !! y = Some o → spare o) → gen_new W Γ C → scontr S →
  dftyped W ∅ Γ Δ F ENew
    (TEx LBot 1 C (TProd (TSess S (pvar 0) a1 mt) (TSess (dual S) (pvar 0)‾ a2 mt))).
Proof. intros H HC HS. apply d_new; [by apply spare_unl|done|done]. Qed.

(** A measure for (wf-new) on a tree at offset 0: the offset first,
    then a height h of the points of the facts. *)
Lemma wf_new_height (L : fact → Prop) (h : point → nat) :
  (∀ x y, L (FLt x y) → in_tree0 x ∧ in_tree0 y) →
  (∀ x y, L (FLt x y) → pt_off x = pt_off y ∧ h x < h y) →
  wf_new (bcs_of L).
Proof.
  intros HL Hh. apply (wf_new_lex3 _ (λ x, (pt_off x, h x, 0))); [done| |].
  - intros x. simpl. lia.
  - intros x y Hf. destruct (Hh x y Hf) as [E Hlt]. simpl. lia.
Qed.

Abbreviation ρ0 := (pvar 0).

(** ** Two upper bounds

    main = let (a, a′) = new in                      a at ρ, a′ at ρ̄
           let (a, (b, b′)) = ⟨a, new⟩ in            b at ρ·0
           spawn (close a′; close b′);
           let (d, d′) = new in                      d at π
           spawn (close d′);
           close d; close a; close b

    The spawned thread closes a′ at ρ̄ while it holds b′, so ρ̄ ≺ ρ·0.
    main closes d at π while it holds a and b, so π ≺ ρ̄ and π ≺ (ρ·0)‾,
    then a while it holds b, so ρ ≺ (ρ·0)‾. *)

Definition tu_L (g : fact) : Prop :=
  g = FLt ρ0 (ρ0·0)‾ ∨ g = FLt (ρ0·1) ρ0‾ ∨ g = FLt ρ0‾ (ρ0·0).

Definition tu_h (x : point) : nat :=
  if decide (x = ρ0‾) then 1 else if decide (x = ρ0·0) then 2
  else if decide (x = (ρ0·0)‾) then 3 else 0.

Lemma tu_wf_new : wf_new (bcs_of tu_L).
Proof.
  apply (wf_new_height _ tu_h).
  - intros x y [E|[E|E]]; injection E as -> ->; split; reflexivity.
  - intros x y [E|[E|E]]; injection E as -> ->; (split; [reflexivity|vm_compute; lia]).
Qed.
#[global] Hint Resolve tu_wf_new : wfnew.

(** The constraint of d. Variable 0 is π, variable 1 is ρ, the point
    of its environment. *)
Definition tu_P (g : fact) : Prop :=
  g = FLt (pvar 0) (pvar 1)‾ ∨ g = FLt (pvar 0) ((pvar 1)·0)‾.
Definition tu_C : bcs := BCs [ρ0] tu_P.

Definition tu_S (s t : point) : Prop := s = pvar 0 ∧ (t = ρ0·1 ∨ t = ρ0).

Lemma tu_gen1 W : gen_new1 W (Γnew tu_L) tu_C.
Proof.
  split_and!.
  - apply wf_step_po. intros x y [[E|E] _] _ Hy; injection E as -> ->; nt Hy.
  - intros x y [[E|E] _] Hx _; injection E as -> ->; exfalso; by apply Hx.
  - exists tu_S. split_and!.
    + intros u y [[E|E] _] _ _; injection E as -> ->.
      * exists (ρ0·1). split; [split; [done|by left]|]. apply law_slt'; [disj_tac|cbn; lia].
      * exists ρ0. split; [split; [done|by right]|]. apply law_slt'; [disj_tac|cbn; lia].
    + intros s t s' [-> _] Hs. exfalso. revert Hs. apply new_step_root.
      intros x [[E|E] _] _; injection E as _ E; nt E.
    + intros s t z [-> _] [[E|E] _] _; injection E as _ E; nt E.
Qed.

Lemma tu_gen W : gen_new W (Γnew tu_L) tu_C.
Proof. apply gen_new1_gen, tu_gen1. Qed.

(** The constraint of d is not (wf-new). *)
Lemma tu_not_wf_new : ¬ wf_new tu_C.
Proof.
  intros [HC _]. assert (in_tree0 (pvar 1)‾) as H.
  { apply (HC (pvar 0)); [by left|cbn; lia]. }
  nt H.
Qed.

(** The hypotheses of the context after the second opening. *)
Lemma in_open_new m C Γ : (bcs_inst (pshift m) C, ids m) ∈ hc_hyps (hc_open m C Γ).
Proof. unfold hc_open. simpl. apply elem_of_app. right. by left. Qed.

Lemma in_open_old m C Γ C0 xs :
  (C0, xs) ∈ hc_hyps Γ → (bcs_inst (pshift m) C0, pt_inst (pshift m) <$> xs) ∈ hc_hyps (hc_open m C Γ).
Proof.
  intros H. unfold hc_open. simpl. apply elem_of_app. left. unfold hyps_inst.
  apply list_elem_of_fmap. by exists (C0, xs).
Qed.

Ltac new_fact f := eapply (slt_hyp_env _ _ _ _ f); [apply in_open_new|disj_tac|cbn; lia|reflexivity].
Ltac old_fact f := eapply (slt_hyp_env _ _ _ _ f); [apply in_open_old, Γnew_in|disj_tac|cbn; lia|reflexivity].

Definition tu_main : expr :=
  let_new (LetP (Pair (Var 1) ENew) (LetP (Var 0)
    (LetU (ESpawn (Lam (LetU (Var 0) (LetU (EClose (Var 5)) (EClose (Var 1))))))
    (ELet ENew (LetP (Var 0)
      (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
      (LetU (EClose (Var 1)) (LetU (EClose (Var 6)) (EClose (Var 4)))))))))).

Theorem tu_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) tu_main TUnit.
Proof.
  unfold tu_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ SEnd None None); [spare_tac|apply tu_wf_new|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew tu_L).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Pair (Var 1) ENew) EUnit| |].
  { eapply (d_new_at _ _ _ _ _ _ 0 SEnd ρ0 SEnd); [done|reflexivity| |contr_tac]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty
    |lsplit_tac (ESpawn (Lam (LetU (Var 0) (LetU (EClose (Var 5)) (EClose (Var 1)))))) EUnit| |].
  { eapply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 5)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ0‾); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy.
      apply law_slt'; [right; right; reflexivity|cbn; lia]. }
    eapply d_close with (S0 := SEnd) (x := (ρ0·0)‾); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_let; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
  { eapply (d_new_gen _ _ _ _ tu_C SEnd None None); [spare_tac|apply tu_gen|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|apply cons_gen; [by intros ?? []|apply tu_gen]|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert option_fmap option_map pinst_ty].
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| |].
  { eapply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := (pvar 0)‾); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
  { eapply d_close with (S0 := SEnd) (x := pvar 0); [done| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [bot_false|]. intros y Hy.
    heads_cases Hy; first [new_fact (FLt (pvar 0) (pvar 1)‾) | new_fact (FLt (pvar 0) ((pvar 1)·0)‾)]. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 6)) EUnit| |].
  { eapply d_close with (S0 := SEnd) (x := pvar 1); [done| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. old_fact (FLt ρ0 (ρ0·0)‾). }
  eapply d_close with (S0 := SEnd) (x := (pvar 1)·0); [done|apply ub_below_empty|].
  eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Theorem tu_deadlock_free : excluded_middle → deadlock_free (∅, {[+ tu_main +]}).
Proof.
  intros EM. apply (soundness_source sw_empty tu_main TUnit EM); [apply sw_empty_ok|apply sw_empty_ok|constructor|].
  exact tu_dftyped.
Qed.

(** ** Two entries

    main = let (a, a′) = new in                      a at ρ, a′ at ρ̄
           let (a, (e1, e1′)) = ⟨a, new⟩ in          e1 at ρ·0
           let (a, (e2, e2′)) = ⟨a, new⟩ in          e2 at ρ·1
           spawn (close e2′); spawn (close e1′); spawn (close a′);
           let (d, d′) = new in                      d at π
           spawn (close e1; close e2; close d′);
           close d; close a

    The spawned thread closes e1 while it holds e2 and d′, so ρ·0 ≺ (ρ·1)‾
    and ρ·0 ≺ π, then e2 while it holds d′, so ρ·1 ≺ π. main closes d at
    π while it holds a, so π ≺ ρ̄. The points ρ·2 and ρ·3 lie between the
    entries and ρ̄. *)

Definition te_L (g : fact) : Prop :=
  g = FLt (ρ0·0) (ρ0·1)‾ ∨ g = FLt (ρ0·0) (ρ0·2) ∨ g = FLt (ρ0·2) ρ0‾ ∨
  g = FLt (ρ0·1) (ρ0·3) ∨ g = FLt (ρ0·3) ρ0‾.

Definition te_h (x : point) : nat :=
  if decide (x = ρ0‾) then 2
  else if decide (x = (ρ0·1)‾ ∨ x = ρ0·2 ∨ x = ρ0·3) then 1 else 0.

Lemma te_wf_new : wf_new (bcs_of te_L).
Proof.
  apply (wf_new_height _ te_h).
  - intros x y [E|[E|[E|[E|E]]]]; injection E as -> ->; (split; reflexivity).
  - intros x y [E|[E|[E|[E|E]]]]; injection E as -> ->; (split; [reflexivity|vm_compute; lia]).
Qed.
#[global] Hint Resolve te_wf_new : wfnew.

Definition te_P (g : fact) : Prop :=
  g = FLt ((pvar 1)·0) (pvar 0) ∨ g = FLt ((pvar 1)·1) (pvar 0) ∨ g = FLt (pvar 0) (pvar 1)‾.
Definition te_C : bcs := BCs [ρ0] te_P.

Definition te_S (s : point) (T : list point) : Prop := s = pvar 0 ∧ T = (ρ0·2 :: ρ0·3 :: []).

Lemma te_gen W : gen_new W (Γnew te_L) te_C.
Proof.
  split_and!.
  - apply wf_step_po. intros x y [[E|[E|E]] _] Hx Hy; injection E as -> ->; first [nt Hx | nt Hy].
  - intros x y [[E|[E|E]] _] Hx Hy; injection E as -> ->; exfalso; first [by apply Hx | by apply Hy].
  - exists te_S. split_and!.
    + intros s T [_ ->]. congruence.
    + intros u y [[E|[E|E]] _] Hu Hy; injection E as -> ->; [nt Hu|nt Hu|].
      exists (ρ0·2 :: ρ0·3 :: []). split; [split; reflexivity|]. intros t Ht.
      apply elem_of_cons in Ht as [->|Ht]; [|apply list_elem_of_singleton in Ht as ->];
        (apply law_slt'; [disj_tac|cbn; lia]).
    + intros s T s' [-> _] Hs. exfalso. revert Hs. apply new_step_root.
      intros x [[E|[E|E]] _] Hx; injection E; intros; subst;
        first [nt Hx | (repeat match goal with H : @eq point _ _ |- _ => vm_compute in H end; congruence)].
    + intros s T z [-> ->] [[E|[E|E]] _] Hz; injection E; intros; subst.
      * exists (ρ0·2). split; [set_solver|]. apply law_slt'; [disj_tac|cbn; lia].
      * exists (ρ0·3). split; [set_solver|]. apply law_slt'; [disj_tac|cbn; lia].
      * exfalso. repeat match goal with H : @eq point _ _ |- _ => vm_compute in H end. congruence.
Qed.

Lemma te_not_wf_new : ¬ wf_new te_C.
Proof.
  intros [HC _]. assert (in_tree0 (pvar 1)‾) as H.
  { apply (HC (pvar 0)); [by right; right|cbn; lia]. }
  nt H.
Qed.

Definition te_main : expr :=
  let_new (LetP (Pair (Var 1) ENew) (LetP (Var 0)
    (LetP (Pair (Var 3) ENew) (LetP (Var 0)
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 5)))))
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 9)))))
    (ELet ENew (LetP (Var 0)
      (LetU (ESpawn (Lam (LetU (Var 0) (LetU (EClose (Var 9)) (LetU (EClose (Var 5)) (EClose (Var 1)))))))
      (LetU (EClose (Var 1)) (EClose (Var 6))))))))))))).

Ltac spawn_close i p :=
  eapply d_spawn_lam;
  eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |];
  [eapply d_var'; [reflexivity|spare_tac]|];
  eapply d_close with (S0 := SEnd) (x := p); [done|apply ub_below_empty|];
  eapply d_var'; [reflexivity|spare_tac].

Theorem te_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) te_main TUnit.
Proof.
  unfold te_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ SEnd None None); [spare_tac|apply te_wf_new|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew te_L).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Pair (Var 1) ENew) EUnit| |].
  { eapply (d_new_at _ _ _ _ _ _ 0 SEnd ρ0 SEnd); [done|reflexivity| |contr_tac]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Pair (Var 3) ENew) EUnit| |].
  { eapply (d_new_at _ _ _ _ _ _ 1 SEnd ρ0 SEnd); [done|reflexivity| |contr_tac]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| |].
  { spawn_close 1 (ρ0·1)‾. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 5))))) EUnit| |].
  { spawn_close 5 (ρ0·0)‾. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 9))))) EUnit| |].
  { spawn_close 9 ρ0‾. }
  eapply d_let; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
  { eapply (d_new_gen _ _ _ _ te_C SEnd None None); [spare_tac|apply te_gen|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|apply cons_gen; [by intros ?? []|apply te_gen]|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert option_fmap option_map pinst_ty].
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty
    |lsplit_tac (ESpawn (Lam (LetU (Var 0) (LetU (EClose (Var 9)) (LetU (EClose (Var 5)) (EClose (Var 1))))))) EUnit| |].
  { eapply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 9)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := (pvar 1)·0); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros y Hy.
      heads_cases Hy; first [new_fact (FLt ((pvar 1)·0) (pvar 0)) | old_fact (FLt (ρ0·0) (ρ0·1)‾)]. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 5)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := (pvar 1)·1); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. new_fact (FLt ((pvar 1)·1) (pvar 0)). }
    eapply d_close with (S0 := SEnd) (x := (pvar 0)‾); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
  { eapply d_close with (S0 := SEnd) (x := pvar 0); [done| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy. new_fact (FLt (pvar 0) (pvar 1)‾). }
  eapply d_close with (S0 := SEnd) (x := pvar 1); [done|apply ub_below_empty|].
  eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Theorem te_deadlock_free : excluded_middle → deadlock_free (∅, {[+ te_main +]}).
Proof.
  intros EM. apply (soundness_source sw_empty te_main TUnit EM); [apply sw_empty_ok|apply sw_empty_ok|constructor|].
  exact te_dftyped.
Qed.

(** ** Rejection under (wf-new)

    Under a constraint C of (wf-new) a fact of the opened context that
    ends outside the new tree also starts outside it ([slt_open_out]).
    So no such C derives π ≺ ρ̄, and the thread that closes d at π and
    then a at ρ, the thread reached after the creation, has no
    derivation in the opened context ([cl2_needs]). *)

Lemma exit_rejected_wf_new W Γ C : facts_const W → wf_new C →
  ¬ slt W (hc_open 1 C Γ) (pvar 0) (pvar 1)‾.
Proof.
  intros Hfc HC H. destruct (slt_open_out W Γ C _ _ Hfc HC H) as [Hx _]; [intros Hy; nt Hy|].
  by apply Hx.
Qed.

Lemma close_rejected_wf_new W N Γ C Θ Δ F T c od oa ed ea :
  facts_const W → wf_new C → od ≠ oa →
  Θ !! od = Some ed → te_pt ed = pvar 0 → Θ !! oa = Some ea → te_pt ea = pvar 1 →
  ¬ typed W N Θ (hc_open 1 C Γ) Δ F (cl2 od oa) T c.
Proof.
  intros Hfc HC Hne Hd Ed Ha Ea H.
  pose proof (cl2_needs _ _ _ _ _ _ _ _ _ _ _ _ Hne H Hd Ha) as Hlt. rewrite Ed, Ea in Hlt.
  exact (exit_rejected_wf_new W Γ C Hfc HC Hlt).
Qed.

(** The two examples: the creation of d is accepted by (gen-new) and
    not by (wf-new), and under every constraint of (wf-new) the close of
    d before a is rejected. *)
Theorem tu_rejected_wf_new N C Θ Δ F T c ed ea :
  wf_new C → Θ !! oc = Some ed → te_pt ed = pvar 0 → Θ !! od = Some ea → te_pt ea = pvar 1 →
  ¬ typed sw_empty N Θ (hc_open 1 C (Γnew tu_L)) Δ F (cl2 oc od) T c.
Proof. intros HC. apply close_rejected_wf_new; [by intros ?? []|done|apply oc_od]. Qed.

Theorem te_rejected_wf_new N C Θ Δ F T c ed ea :
  wf_new C → Θ !! oc = Some ed → te_pt ed = pvar 0 → Θ !! od = Some ea → te_pt ea = pvar 1 →
  ¬ typed sw_empty N Θ (hc_open 1 C (Γnew te_L)) Δ F (cl2 oc od) T c.
Proof. intros HC. apply close_rejected_wf_new; [by intros ?? []|done|apply oc_od]. Qed.
