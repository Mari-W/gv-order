(** * Two exchanges at one point (stage 1 of the slice in the world)

      pr_round i k = let (a, a′) = new in spawn (λu. u; close (select i a′));
                     case branch a of inl c ⇒ close c | inr c ⇒ close c; k
      pr_thread    = pr_round l (pr_round r ∗)

    Both creations type by E-New-Field at the field x·0 of the constant
    point x, so the end a of each round sits at x·0 and its dual end at
    (x·0)‾. The first round receives l at x·0, the second receives r at
    x·0. One thread runs both rounds, so every run of the closed program
    exchanges twice at x·0 with different labels.

    - [pr_round_typed]: one round types over any context of spare
      entries, with both ends at x·0 and (x·0)‾. The two rounds of
      [pr_thread] are this lemma twice.
    - [pr_dftyped], [pr_term]: the thread types, and P-Term types the
      closed program over the empty world.
    - [pr_deadlock_free]: deadlock freedom by [soundness].

    So point linearity, at most one exchange per point in a run, fails
    for typed programs. A slice λ : point → option label in the world
    (.claude/notes/redesign/check-transfinite-branches.md, section 4.3) cannot
    agree with this run at x·0. *)

From GV Require Export examples.Tools.
From GV Require Import static.FundamentalProc.

Definition pr_round (i : bool) (k : expr) : expr :=
  LetP ENew
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (ESel i (Var 1))))))
      (LetU (Case (EBra (Var 1)) (EClose (Var 0)) (EClose (Var 0))) k)).

Definition pr_thread : expr := pr_round false (pr_round true EUnit).

(** The point x and the protocol &{l : end, r : end} of a. *)
Definition px : point := MkPt (NConst 0) true 0.
Definition pS : sty := SWith SEnd SEnd.

(** A context of spare entries adds nothing to a future. *)
Lemma pr_sf F (Δ : lenv) :
  (∀ z o, Δ !! z = Some o → spare o) → sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ) (lenv_bot Δ) = F.
Proof.
  intros H. destruct (spare_heads Δ H) as [-> ->]. rewrite tenv_heads_empty.
  destruct F as [X r]. unfold sf_unionb. simpl. by rewrite !(right_id_L ∅ (∪)).
Qed.

(** A context of spare entries splits into itself twice. *)
Lemma lsplit_spare (Δ : lenv) : (∀ z o, Δ !! z = Some o → spare o) → lenv_split Δ Δ Δ.
Proof.
  induction Δ as [|[U|] Δ IH]; intros H; [apply lsplit_nil| |].
  - pose proof (H 0 _ eq_refl) as HU. apply lsplit_unl; [exact HU|]. apply IH. intros z o Hz. exact (H (S z) o Hz).
  - apply lsplit_none. apply IH. intros z o Hz. exact (H (S z) o Hz).
Qed.

(** u; close (select i a′) under the argument u of the spawned λ. *)
Lemma pr_sel_typed Γ (Δ : lenv) i :
  (∀ z o, Δ !! z = Some o → spare o) →
  dftyped sw_empty ∅ Γ (Some TUnit :: Some (TSess (dual pS) (px·0)‾ None None) :: Δ) (∅, None)
    (LetU (Var 0) (EClose (ESel i (Var 1)))) TUnit.
Proof.
  intros H.
  eapply (d_letu _ _ ∅ ∅ _ _ (Some TUnit :: None :: Δ) (None :: Some (TSess (dual pS) (px·0)‾ None None) :: Δ));
    [apply tsplit_empty|apply lsplit_l, lsplit_r, lsplit_spare, H| |].
  { eapply d_var'; [reflexivity|]. intros [|[|z]] o Hz Ho; [done|by injection Ho as <-|exact (H z o Ho)]. }
  eapply (d_close _ _ _ _ _ _ (if i then SEnd else SEnd) (sel_pt (px·0)‾ i)); [by destruct i|apply ub_below_empty|].
  eapply (d_select _ i _ _ _ _ _ (dual pS) (px·0)‾ SEnd SEnd); [reflexivity|apply ub_below_empty|].
  eapply d_var'; [reflexivity|]. intros [|[|z]] o Hz Ho; [by injection Ho as <-|done|exact (H z o Ho)].
Unshelve. all: try exact None.
Qed.

(** One round. The creation sits at the field x·0, whatever the round. *)
Lemma pr_round_typed (Δ : lenv) i k :
  (∀ z o, Δ !! z = Some o → spare o) →
  dftyped sw_empty ∅ hc_empty (None :: None :: Δ) (∅, None) k TUnit →
  dftyped sw_empty ∅ hc_empty Δ (∅, None) (pr_round i k) TUnit.
Proof.
  intros H Hk. unfold pr_round.
  eapply (d_letp _ _ ∅ ∅ _ _ Δ Δ _ _ _ (TSess pS (px·0) None None) (TSess (dual pS) (px·0)‾ None None));
    [apply tsplit_empty| | |].
  { by apply lsplit_spare. }
  { apply d_new_fld; [by apply spare_unl|contr_tac]. }
  eapply (d_letu _ _ ∅ ∅ _ _ (Some (TSess (dual pS) (px·0)‾ None None) :: None :: Δ)
            (None :: Some (TSess pS (px·0) None None) :: Δ)); [apply tsplit_empty| | |].
  { apply lsplit_l, lsplit_r. by apply lsplit_spare. }
  { apply d_spawn_lam. apply pr_sel_typed. intros [|z] o Hz; [by injection Hz as <-|]. exact (H z o Hz). }
  eapply (d_letu _ _ ∅ ∅ _ _ (None :: Some (TSess pS (px·0) None None) :: Δ) (None :: None :: Δ));
    [apply tsplit_empty| | |exact Hk].
  { apply lsplit_none, lsplit_l. by apply lsplit_spare. }
  assert (∀ z o, (None :: None :: Δ) !! z = Some o → spare o) as H2.
  { intros [|[|z]] o Hz; [by injection Hz as <-|by injection Hz as <-|exact (H z o Hz)]. }
  eapply (d_case _ _ ∅ ∅ _ _ (None :: Some (TSess pS (px·0) None None) :: Δ) (None :: None :: Δ));
    [apply tsplit_empty| | | |].
  { apply lsplit_none, lsplit_l. by apply lsplit_spare. }
  - eapply (d_branch _ _ _ _ _ _ pS (px·0) SEnd SEnd); [reflexivity| |].
    + rewrite !(pr_sf _ _ H2). apply ub_below_empty.
    + eapply d_var'; [reflexivity|]. intros [|[|z]] o Hz Ho; [by injection Ho as <-|done|exact (H z o Ho)].
  - eapply d_close with (S0 := SEnd); [done| |].
    + rewrite !(pr_sf _ _ H2). apply ub_below_empty.
    + eapply d_var'; [reflexivity|]. intros [|z] o Hz Ho; [done|exact (H2 z o Ho)].
  - eapply d_close with (S0 := SEnd); [done| |].
    + rewrite !(pr_sf _ _ H2). apply ub_below_empty.
    + eapply d_var'; [reflexivity|]. intros [|z] o Hz Ho; [done|exact (H2 z o Ho)].
Unshelve. all: try exact None.
Qed.

Theorem pr_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) pr_thread TUnit.
Proof.
  unfold pr_thread. apply pr_round_typed; [by intros ? ? ?|].
  apply pr_round_typed; [intros [|[|z]] o Hz; [by injection Hz as <-|by injection Hz as <-|done]|].
  apply d_unit'. intros [|[|[|[|z]]]] o Hz; try (by injection Hz as <-); done.
Qed.

Theorem pr_term : ptyped None (khalf None) sw_empty ∅ (∅, {[+ pr_thread +]}) TUnit.
Proof.
  apply (p_term_half None sw_empty ∅ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - apply pfree_empty.
  - intros o e He. by rewrite lookup_empty in He.
  - set_solver.
  - assert (tenv_of (fhalf None) ∅ ∪ ∅ = tenv_df ∅) as ->.
    { unfold tenv_of, tenv_df. by rewrite !fmap_empty, map_union_empty. }
    apply pr_dftyped.
  - apply sw_empty_wok.
Qed.

Theorem pr_deadlock_free : deadlock_free (∅, {[+ pr_thread +]}).
Proof. exact (soundness _ _ TUnit pr_term). Qed.
