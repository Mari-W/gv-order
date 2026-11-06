(** * T1 ∥ T2 ∥ T3 with primitive choice, translated

    The program of docs/extensions/choice-encoding.md written with the
    constants select₁ and branch:

      c : ⊕{A: !∗.Close, B: !∗.Close}      d : Close
      T1 = close (send ⟨∗, select₁ c⟩)
      T2 = case branch c′ of k ⇒ close d; recv k; close k | k ⇒ recv k; close d; close k
      T3 = close d′

    [native_fstyped] types it in the fragment of examples/ChoiceTranslate.v
    under the top-level constraint {a ≺ a[1], a[1] ≺ δ, δ ≺ a[0], δ ≺ a[1]+1},
    [native_deadlock_free] is deadlock freedom of the program itself, and
    [translated_deadlock_free] is deadlock freedom of its translation into
    sums plus delegation, by [choice_translate_df].

    With end points T2 holds c′ at ā and d at δ, T1 keeps k at a[0]‾,
    and the top-level constraint is
    {a ≺ a[0], a ≺ a[0]‾, a ≺ a[1]‾, ā ≺ a[0]‾, ā ≺ a[1]‾, ā ≺ δ̄,
     δ ≺ a[0]‾, a[1] ≺ δ̄, δ ≺ a[1]‾+1}: select₁ and the fragment ask
    the first three, branch at ā the next three, the arms the last
    three. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ChoiceTranslate.

Set Default Proof Using "All".

(** ** Derived rules of the fragment *)

Section frules.
  Lemma fv_var Φ Ψ Δ F x T :
    Δ !! x = Some (Some T) → oku x Δ = true → fstyped Φ Ψ Δ F (Var x) T.
  Proof. intros H1 H2. eapply f_wk; [by apply lonly_wk|]. apply f_var. by apply lonly_only. Qed.

  Lemma fv_unit Φ Ψ Δ F : allunl Δ = true → fstyped Φ Ψ Δ F EUnit TUnit.
  Proof. intros H. eapply f_wk; [by apply nones_wk|]. apply f_unit, lenv_empty_nones. Qed.

  Lemma fv_appk Φ Ψ Δ F k e2 ub T U :
    fstyped Φ Ψ Δ F e2 T →
    (∀ Δ0 F0, lenv_empty Δ0 → fstyped Φ Ψ Δ0 F0 (Konst k) (TLolli ub None T U)) →
    hub_below_s Ψ Φ ub F →
    fstyped Φ Ψ Δ F (App (Konst k) e2) U.
  Proof.
    intros H2 Hk Hu. eapply (f_app Φ Ψ Δ (lenv_nones Δ) Δ F _ _ ub None).
    - apply lenv_split_nones_l.
    - exact Hu.
    - apply Hk, lenv_empty_nones.
    - destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L.
  Qed.

  Lemma fv_pair Φ Ψ Δ F e1 e2 T U :
    sok e1 0 e2 0 Δ && negb (lenv_bot (lp e2 0 Δ)) = true →
    fstyped Φ Ψ (lp e2 0 Δ) (sf_unionb F (heads T) (hbot T)) e2 U →
    fstyped Φ Ψ (lp e1 0 Δ) (sf_union F (lenv_heads (lp e2 0 Δ))) e1 T →
    fstyped Φ Ψ Δ F (Pair e1 e2) (TProd T U).
  Proof.
    intros Hs H2 H1. apply andb_true_iff in Hs as [Hs Hb]. apply negb_true_iff in Hb.
    eapply f_pair; [by apply lp_split| |exact H2]. by rewrite Hb.
  Qed.

  Lemma fv_letu Φ Ψ Δ F e1 e2 T :
    sok e1 0 e2 0 Δ && negb (lenv_bot (lp e2 0 Δ)) = true →
    fstyped Φ Ψ (lp e1 0 Δ) (sf_union F (lenv_heads (lp e2 0 Δ))) e1 TUnit →
    fstyped Φ Ψ (lp e2 0 Δ) F e2 T →
    fstyped Φ Ψ Δ F (LetU e1 e2) T.
  Proof.
    intros Hs H1 H2. apply andb_true_iff in Hs as [Hs Hb]. apply negb_true_iff in Hb.
    eapply f_letu; [by apply lp_split| |exact H2]. by rewrite Hb.
  Qed.

  Lemma fv_letp Φ Ψ Δ F e1 e2 T1 T2 T :
    sok e1 0 e2 2 Δ && negb (lenv_bot (lp e2 2 Δ)) = true →
    fstyped Φ Ψ (lp e1 0 Δ) (sf_union F (lenv_heads (lp e2 2 Δ))) e1 (TProd T1 T2) →
    fstyped Φ Ψ (Some T2 :: Some T1 :: lp e2 2 Δ) F e2 T →
    fstyped Φ Ψ Δ F (LetP e1 e2) T.
  Proof.
    intros Hs H1 H2. apply andb_true_iff in Hs as [Hs Hb]. apply negb_true_iff in Hb.
    eapply f_letp; [by apply lp_split| |exact H2]. by rewrite Hb.
  Qed.

  Lemma fv_case Φ Ψ Δ F e e1 e2 T1 T2 T :
    sok e 0 (Lam (Pair e1 e2)) 0 Δ && negb (lenv_bot (lp (Lam (Pair e1 e2)) 0 Δ)) = true →
    fstyped Φ Ψ (lp e 0 Δ) (sf_union F (lenv_heads (lp (Lam (Pair e1 e2)) 0 Δ))) e (TSum T1 T2) →
    fstyped Φ Ψ (Some T1 :: lp (Lam (Pair e1 e2)) 0 Δ) F e1 T →
    fstyped Φ Ψ (Some T2 :: lp (Lam (Pair e1 e2)) 0 Δ) F e2 T →
    fstyped Φ Ψ Δ F (Case e e1 e2) T.
  Proof.
    intros Hs H H1 H2. apply andb_true_iff in Hs as [Hs Hb]. apply negb_true_iff in Hb.
    eapply f_case; [by apply lp_split| |exact H1|exact H2]. by rewrite Hb.
  Qed.

  Lemma fv_lam Φ Ψ Δ F e T U ub lb φ :
    φ ∉ dom Φ →
    hlb_below_hb Ψ lb (lenv_heads Δ) (lenv_bot Δ) →
    fstyped (<[φ := ub]> Φ) Ψ (Some T :: Δ) (∅, Some (FVar φ)) e U →
    fstyped Φ Ψ Δ F (Lam e) (TLolli ub lb T U).
  Proof. intros Hφ Hl H. by eapply f_lam. Qed.

  (** new at a known point x (new@x, [KTNewAt]). *)
  Lemma fv_new_open Φ Ψ Δ F e T S x :
    hyp_known Ψ x →
    fstyped Φ Ψ (Some (TSess (dual S) (pt_dual x)) :: Some (TSess S x) :: None :: None :: Δ) F e T →
    fstyped Φ Ψ Δ F (let_new e) T.
  Proof.
    intros Hx Hb. unfold let_new.
    set (X := TProd (TSess S x) (TSess (dual S) (pt_dual x))).
    apply (f_letp Φ Ψ Δ (lenv_nones Δ) Δ F _ _ X TUnit).
    { apply lenv_split_nones_l. }
    { apply (f_pair Φ Ψ (lenv_nones Δ) (lenv_nones Δ) (lenv_nones Δ)).
      - apply lenv_split_nones_nones.
      - eapply (f_app Φ Ψ _ _ _ _ _ _ None None TUnit).
        + apply lenv_split_nones_l.
        + done.
        + apply f_konst; [done|apply lenv_empty_nones| |done]. by apply KTNewAt.
        + apply f_unit. apply lenv_empty_nones.
      - apply f_unit. apply lenv_empty_nones. }
    apply (f_letu Φ Ψ _ (Some TUnit :: None :: lenv_nones Δ) (None :: Some X :: Δ)).
    { apply lsplit_l, lsplit_r, lenv_split_nones_l. }
    { apply f_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [by simplify_eq|done|].
      exfalso. unfold lenv_nones in Hy. rewrite list_lookup_fmap in Hy.
      apply fmap_Some in Hy as (? & _ & ?). congruence. }
    apply (f_letp _ _ _ (None :: Some X :: lenv_nones Δ) (None :: None :: Δ)
             _ _ _ (TSess S x) (TSess (dual S) (pt_dual x))).
    - apply lsplit_none, lsplit_l, lenv_split_nones_l.
    - apply f_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [done|by simplify_eq|].
      exfalso. unfold lenv_nones in Hy. rewrite list_lookup_fmap in Hy.
      apply fmap_Some in Hy as (? & _ & ?). congruence.
    - exact Hb.
  Qed.

  Lemma hlt_hyp0 Ψ P xs x y x' y' :
    (BCs [] P, xs) ∈ Ψ → P (FLt x y) → fact_scoped (length xs) (FLt x y) →
    pt_inst (plist xs) x = x' → pt_inst (plist xs) y = y' → hlt Ψ x' y'.
  Proof.
    intros Hg Hxy Hs <- <-. apply hl_h. exists (BCs [] P), xs. split; [done|].
    exists (FLt x y). split; [by apply bcs_open_nil|done].
  Qed.

  Lemma hubs_intro Ψ Φ x P o :
    (∀ y, y ∈ P → hlt Ψ x y) →
    match o with
    | Some (FVar φ) => ∃ u, Φ !! φ = Some (Some u) ∧ hle Ψ x u
    | Some (FBot _) => False
    | None => True
    end →
    hub_below_s Ψ Φ (Some x) (P, o).
  Proof.
    intros HP Ho. split_and!.
    - intros y Hy. by apply hlt_hfl, HP.
    - intros φ Hφ. destruct o as [[φ'|o']|]; simpl in Hφ; try done.
      injection Hφ as <-. destruct Ho as (u & Hu & [Heq|Hlt]).
      + eapply hl_eql; [exact Heq|]. by apply hl_v.
      + eapply hl_trans; [by apply hlt_hfl|]. by apply hl_v.
    - destruct o as [[|]|]; simpl; done.
  Qed.

  Lemma hle_refl Ψ x : hle Ψ x x.
  Proof. left. apply he_refl. Qed.
End frules.

(** ** The program *)

Definition Sp : sty := SPlus Sd Sd.

Definition t1n : expr := Lam (LetU (Var 0) (sendclose (App ESel1 (Var 4)))).
Definition arm1n : expr := LetU (App EClos (Var 2)) (recvclose (Var 0)).
Definition arm2n : expr :=
  LetP (App ERecv (Var 0)) (LetU (Var 1) (LetU (App EClos (Var 4)) (App EClos (Var 0)))).

Definition choice_native : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn t1n)
      (LetU (App ESpawn t3_thunk)
        (Case (App EBra (Var 2)) arm1n arm2n)))).

Definition cn_fact (g : fact) : Prop :=
  g = FLt (pa 0) (pa0 0) ∨ g = FLt (pa 0) (pt_dual (pa0 0)) ∨ g = FLt (pa 0) (pt_dual (pa1 0)) ∨
  g = FLt (pt_dual (pa 0)) (pt_dual (pa0 0)) ∨ g = FLt (pt_dual (pa 0)) (pt_dual (pa1 0)) ∨
  g = FLt (pt_dual (pa 0)) (pt_dual (pd 0)) ∨ g = FLt (pd 0) (pt_dual (pa0 0)) ∨
  g = FLt (pa1 0) (pt_dual (pd 0)) ∨ g = FLt (pd 0) (pt_dual (pa1 1)).
Definition Cn : bcs := BCs [] cn_fact.

Lemma cn_rank_ok : c0_acyclic 2 Cn.
Proof.
  set (r := λ x : point, match pt_name x with
    | NVar 0 => 10 * pt_off x
    | NPayload (NVar 0) 0 1 => 15 + 10 * pt_off x
    | NVar 1 => 17 + 10 * pt_off x
    | NPayload (NVar 0) 0 0 => 20 + 10 * pt_off x
    | _ => 10 * pt_off x
    end).
  apply (c0_acyclic_rank 2 _ r).
  - intros [p b o]. unfold r, pt_shift. simpl. repeat case_match; lia.
  - intros x y H. repeat destruct H as [H|H]; injection H as -> ->; unfold r; cbn; lia.
  - intros [p b o]. done.
Qed.

Ltac memc H :=
  cbn in H; rewrite ?set_map_empty, ?elem_of_union, ?elem_of_singleton in H;
  repeat match type of H with _ ∨ _ => destruct H as [H|H] end;
  try (by apply not_elem_of_empty in H);
  try (rewrite ?set_map_empty in H; by apply not_elem_of_empty in H); subst.

Ltac fk kt := let H := fresh in intros ? ? H; apply f_konst; [done|exact H|kt|kscope].

Lemma native_fstyped : fstyped ∅ [(Cn, ids 2)] [] (∅, None) choice_native TUnit.
Proof.
  unfold choice_native.
  apply (fv_new_open _ _ _ _ _ _ Sp (pa 0)).
  { exists Cn, (ids 2), (pvar 0). split_and!; [by left|by left|done]. }
  cbn. rewrite ?set_map_empty.
  apply (fv_new_open _ _ _ _ _ _ SEnd (pv 1 0)).
  { exists Cn, (ids 2), (pvar 1). split_and!; [by left|by right; left|done]. }
  cbn. rewrite ?set_map_empty.
  match goal with |- fstyped _ ?Q _ _ _ _ => set (Ψ2 := Q) end.
  assert ((BCs [] cn_fact, [pv 0 0; pv 1 0]) ∈ Ψ2) as Hin by (by left).
  assert (∀ x y, cn_fact (FLt x y) →
            hlt Ψ2 (pt_inst (plist [pv 0 0; pv 1 0]) x) (pt_inst (plist [pv 0 0; pv 1 0]) y)) as Hf.
  { intros x y Hxy. eapply (hlt_hyp0 _ _ _ x y); [exact Hin|exact Hxy| |done|done].
    repeat destruct Hxy as [Hxy|Hxy]; injection Hxy as -> ->; cbn; lia. }
  set (a := pv 0 0). set (δ := pv 1 0).
  set (a0 := Pt (NPayload (NVar 0) 0 0) 0). set (a1 := Pt (NPayload (NVar 0) 0 1) 0).
  assert (hlt Ψ2 a a0) as N1 by (apply (Hf (pa 0) (pa0 0)); by left).
  assert (hlt Ψ2 a (pt_dual a0)) as N2 by (apply (Hf (pa 0) (pt_dual (pa0 0))); do 1 right; by left).
  assert (hlt Ψ2 a (pt_dual a1)) as N3 by (apply (Hf (pa 0) (pt_dual (pa1 0))); do 2 right; by left).
  assert (hlt Ψ2 (pt_dual a) (pt_dual a0)) as N4
    by (apply (Hf (pt_dual (pa 0)) (pt_dual (pa0 0))); do 3 right; by left).
  assert (hlt Ψ2 (pt_dual a) (pt_dual a1)) as N5
    by (apply (Hf (pt_dual (pa 0)) (pt_dual (pa1 0))); do 4 right; by left).
  assert (hlt Ψ2 (pt_dual a) (pt_dual δ)) as N6
    by (apply (Hf (pt_dual (pa 0)) (pt_dual (pd 0))); do 5 right; by left).
  assert (hlt Ψ2 δ (pt_dual a0)) as N7 by (apply (Hf (pd 0) (pt_dual (pa0 0))); do 6 right; by left).
  assert (hlt Ψ2 a1 (pt_dual δ)) as N8 by (apply (Hf (pa1 0) (pt_dual (pd 0))); do 7 right; by left).
  assert (hlt Ψ2 δ (pt_dual (pt_shift 1 a1))) as N9 by (apply (Hf (pd 0) (pt_dual (pa1 1))); by do 8 right).
  assert (hlt Ψ2 a (pt_shift 1 (pt_dual a0))) as D3 by (eapply hlt_trans; [exact N1|apply hl_dpo]).
  assert (hlt Ψ2 (pt_dual a0) (pt_shift 1 (pt_dual a0))) as P0 by apply hlt_po.
  assert (hyp_known Ψ2 a) as Ka by (exists (BCs [] cn_fact), [pv 0 0; pv 1 0], (pv 0 0); split_and!; [done|by left|done]).
  (* T1 *)
  apply fv_letu; [reflexivity| |].
  { eapply fv_appk; [|fk ltac:(apply KTSpawn)|done].
    apply (fv_lam _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 (pt_dual a0))) (Some (pt_dual a)) 0); [set_solver| |].
    { intros y Hy. memc Hy. apply hle_refl. }
    apply fv_letu; [reflexivity|apply fv_var; reflexivity|]. cbn. unfold sendclose.
    eapply fv_appk; [|fk ltac:(apply (KTClos _ _ _ (pt_shift 1 (pt_dual a0))))|].
    - eapply fv_appk; [|fk ltac:(apply (KTSend _ _ _ 0 TUnit SEnd (pt_dual a0)); cbn; set_solver)|].
      + apply fv_pair; [reflexivity| |apply fv_unit; reflexivity].
        eapply fv_appk; [apply fv_var; reflexivity| |].
        * intros ? ? H. apply f_sel1; [exact H|exact Ka|exact N1|exact N2|exact N3].
        * apply hubs_intro; [intros y Hy; memc Hy|].
          exists (pt_shift 1 (pt_dual a0)). split; [done|]. right. exact D3.
      + apply hubs_intro; [intros y Hy; memc Hy|].
        exists (pt_shift 1 (pt_dual a0)). split; [done|]. right. exact P0.
    - apply hubs_intro; [intros y Hy; memc Hy|].
      exists (pt_shift 1 (pt_dual a0)). split; [done|]. apply hle_refl. }
  (* T3 *)
  cbn. apply fv_letu; [reflexivity| |].
  { eapply fv_appk; [|fk ltac:(apply KTSpawn)|done].
    apply (fv_lam _ _ _ _ _ TUnit TUnit (Some (pt_dual δ)) (Some δ) 0); [set_solver| |].
    { intros y Hy. memc Hy. apply hle_refl. }
    apply fv_letu; [reflexivity|apply fv_var; reflexivity|]. cbn.
    eapply fv_appk; [apply fv_var; reflexivity|fk ltac:(apply (KTClos _ _ _ (pt_dual δ)))|].
    apply hubs_intro; [intros y Hy; memc Hy|].
    exists (pt_dual δ). split; [done|]. apply hle_refl. }
  (* T2 *)
  cbn. eapply fv_case; [reflexivity| | |].
  - eapply fv_appk; [apply fv_var; reflexivity| |].
    + intros ? ? H. apply (f_bra _ _ _ _ _ _ (pt_dual a)); [exact H|exact N4|exact N5].
    + apply hubs_intro; [intros y Hy; memc Hy; exact N6|done].
  - (* branch A: close d, then receive on k at a[0] *)
    unfold arm1n, recvclose. apply fv_letu; [reflexivity| |].
    + eapply fv_appk; [apply fv_var; reflexivity|fk ltac:(apply (KTClos _ _ _ δ))|].
      apply hubs_intro; [intros y Hy; memc Hy; exact N7|done].
    + eapply fv_letp; [reflexivity| |].
      * eapply fv_appk; [apply fv_var; reflexivity|fk ltac:(apply KTRecv)|].
        apply hubs_intro; [intros y Hy; memc Hy|done].
      * cbn. apply fv_letu; [reflexivity|apply fv_var; reflexivity|].
        eapply fv_appk; [apply fv_var; reflexivity|fk ltac:(apply KTClos)|].
        apply hubs_intro; [intros y Hy; memc Hy|done].
  - (* branch B: receive on k at a[1], then close d *)
    unfold arm2n. eapply fv_letp; [reflexivity| |].
    + eapply fv_appk; [apply fv_var; reflexivity|fk ltac:(apply KTRecv)|].
      apply hubs_intro; [intros y Hy; memc Hy; exact N8|done].
    + cbn. apply fv_letu; [reflexivity|apply fv_var; reflexivity|].
      apply fv_letu; [reflexivity| |].
      * eapply fv_appk; [apply fv_var; reflexivity|fk ltac:(apply (KTClos _ _ _ δ))|].
        apply hubs_intro; [intros y Hy; memc Hy; exact N9|done].
      * eapply fv_appk; [apply fv_var; reflexivity|fk ltac:(apply KTClos)|].
        apply hubs_intro; [intros y Hy; memc Hy|done].
Qed.

Theorem native_deadlock_free : deadlock_free (∅, {[+ choice_native +]}).
Proof.
  apply (soundness_source 2 Cn _ TUnit (c0_acyclic_creation _ _ cn_rank_ok)); [constructor|].
  apply fstyped_styped, native_fstyped.
Qed.

Theorem translated_deadlock_free : deadlock_free (∅, {[+ tr_e choice_native +]}).
Proof.
  apply (choice_translate_df 2 Cn _ TUnit (c0_acyclic_creation _ _ cn_rank_ok)); [constructor|].
  apply native_fstyped.
Qed.
