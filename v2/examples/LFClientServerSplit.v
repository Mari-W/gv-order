(** * The client and the server as two components, each at its own world

      cli ⟨a⁺, b⁺⟩  ∥_{a, b}  srv ⟨a⁻, b⁻⟩

    The channels a and b of examples/LFClientServer.v are the cut Σ_C,
    a⁺ at the constant root ρ and b⁺ at ρ·0. The client forces its box at
    (ρ, ρ·0, ρ·1) and the server at (ρ‾, (ρ·0)‾, ρ·1). Each component
    lives in a static world of its own, which holds the instances of the
    box constraint it uses (the laws [cs_L] at polarity true and false).
    The two worlds share the constant 0. Their join is well-founded by
    the measure (field sum, offset, depth), so their restrictions to the
    shared constant are well-founded together. [lf_p_term] reads each
    thread at every ranked world of its own static world, and
    [lf_connect_adequacy] composes them at a ranked world of the join. *)

From GV Require Export examples.LFClientServer.

Definition ρ : point := MkPt (NConst 0) true 0.
Definition oa : cend := EPos "a".
Definition ob : cend := EPos "b".

(** The laws of [cs_L] at the constant ρ and one polarity. *)
Definition csw_L (b : bool) (g : fact) : Prop :=
  ∃ k, let α := pt_polar b ρ in let β := pt_polar b (ρ·0) in
    g = FLt (sh k α) (sh k β)‾ ∨ g = FLt (sh k β) (sh (S k) α)‾ ∨
    g = FLt (sh k α) (ρ·1) ∨ g = FLt (sh k β) (ρ·1).

Definition W_side (b : bool) : sworld := SWorld {[0]} (csw_L b).
Definition W_cli : sworld := W_side true.
Definition W_srv : sworld := W_side false.

Lemma W_side_wf b : sworld_wf (W_side b).
Proof.
  split. intros x y (k & Hk). unfold croot_in. simpl.
  destruct b; destruct Hk as [E|[E|[E|E]]]; injection E as -> ->;
    split; exists 0; (split; [reflexivity|set_solver]).
Qed.

(** A static world is well-founded when a lexicographic measure rises
    along its facts and along program order. *)
Lemma swf_lex3 W (m : point → nat * nat * nat) :
  (∀ x, lex3 (m x) (m x⁺) ∧ lex3 (m x) (m x‾⁺)) →
  (∀ x y, sw_facts W (FLt x y) → lex3 (m x) (m y)) → swf W.
Proof.
  intros Hpo Hf. apply swf_iff.
  assert (∀ a b, W ⊢ₛ a ≺ b → lex3 (m a) (m b)) as H.
  { assert (∀ a b, swstep W a b → lex3 (m a) (m b)) as Hs.
    { intros a b Hs. destruct Hs; [by apply Hf|apply Hpo|apply Hpo]. }
    induction 1 as [a b Hab|a b c Hab _ IH]; [by apply Hs|].
    apply Hs in Hab. by transitivity (m b). }
  assert (∀ k x, m x = k → Acc (sw_lt W) x) as Hacc.
  { intros k. induction (lex3_wf k) as [k _ IH]. intros x <-. constructor.
    intros y Hy. eapply IH; [apply H, Hy|done]. }
  intros x. by apply (Hacc (m x)).
Qed.

Lemma W_cs_join_wf : swf (W_cli ⊔ W_srv).
Proof.
  apply (swf_lex3 _ (λ x, (pt_fsum x, pt_off x, pt_depth x))).
  - intros x. unfold lex3, pt_fsum, pt_depth. simpl. lia.
  - intros x y [(k & Hk)|(k & Hk)]; destruct Hk as [E|[E|[E|E]]]; injection E as -> ->;
      unfold lex3, pt_fsum, pt_depth; simpl; lia.
Qed.

Lemma W_cs_parts :
  swf W_cli ∧ swf W_srv ∧
  swf (swrestrict W_cli (swshared W_cli W_srv) ⊔ swrestrict W_srv (swshared W_cli W_srv)).
Proof. exact (proj1 (wf_join_iff W_cli W_srv (W_side_wf true) (W_side_wf false)) W_cs_join_wf). Qed.

(** The box constraint holds at the instance of each side, by the facts
    of its world. *)
Lemma csw_hold (b : bool) :
  hold_at (W_side b) hc_empty cs_C (pt_polar b ρ :: pt_polar b (ρ·0) :: ρ·1 :: []).
Proof.
  apply hold_at_nil. intros f (k & Hf) _.
  destruct Hf as [->|[->|[->| ->]]]; simpl; apply sl_w, sw_lt_fact; simpl; exists k; destruct b;
    first [left; fact_eq | right; left; fact_eq | right; right; left; fact_eq | right; right; right; fact_eq].
Qed.

(** ** The two threads *)

Definition t_cli : expr := App (EForce cli) (Pair (Chan oa) (Chan ob)).
Definition t_srv : expr := App (EForce srv) (Pair (Chan (edual oa)) (Chan (edual ob))).

Definition ΣC : senv := <[oa := (Sa, ρ)]> {[ob := (Sb, ρ·0)]}.

Lemma thage_zero Θ : cr_tk Θ → thage (Some 0) Θ Θ.
Proof.
  intros HΘ o. destruct (Θ !! o) as [[S x a m]|] eqn:E; [|done]. simpl.
  split_and!; [done|done|done|destruct a; simpl; lia|by destruct a as [[|]|]|exact (HΘ o _ E)].
Qed.

Ltac crtk_tac :=
  let Hte := fresh in
  intros ?? Hte; repeat (apply lookup_insert_Some in Hte as [[_ <-]|[_ Hte]]; [simpl; lia|]);
  apply lookup_singleton_Some in Hte as [_ <-]; simpl; lia.

(** The two interface ends lose one unit of credit while the box is
    forced. *)
Lemma thage_force2 (o1 o2 : cend) S1 S2 x1 x2 : o1 ≠ o2 →
  thage (fadd (Some 0) (Some 1)) (<[o1 := TE S1 x1 (Some 3) (Some 3)]> {[o2 := TE S2 x2 (Some 3) (Some 3)]})
    (<[o1 := TE S1 x1 (Some 2) (Some 3)]> {[o2 := TE S2 x2 (Some 2) (Some 3)]}).
Proof.
  intros Hne o. destruct (decide (o = o1)) as [->|H1].
  { rewrite !lookup_insert_eq. simpl. split_and!; try done; lia. }
  rewrite !lookup_insert_ne by done. destruct (decide (o = o2)) as [->|H2].
  - rewrite !lookup_singleton_eq. simpl. split_and!; try done; lia.
  - by rewrite !lookup_singleton_ne.
Qed.

(** One side: force the box at the instance xs and apply it to the pair
    of the two interface ends, which hold 3 tickets and credit 3, and
    credit 2 after the force. *)
Lemma side_typed (b : bool) (bx : expr) S1 S2 (o1 o2 : cend) x1 x2 :
  o1 ≠ o2 →
  (∀ F, typed (W_side b) (Some 6) ∅ hc_empty [] F bx (csl_box S1 S2) (Some 0)) →
  x1 = pt_polar b ρ → x2 = pt_polar b (ρ·0) →
  ∃ c, typed (W_side b) (Some 6) (<[o1 := TE S1 x1 (Some 3) (Some 3)]> {[o2 := TE S2 x2 (Some 3) (Some 3)]})
         hc_empty [] (∅, None) (App (EForce bx) (Pair (Chan o1) (Chan o2))) TUnit c.
Proof.
  intros Ho Hbx -> ->. eexists _.
  set (Θ := <[o1 := TE S1 (pt_polar b ρ) (Some 3) (Some 3)]> {[o2 := TE S2 (pt_polar b (ρ·0)) (Some 3) (Some 3)]}).
  set (Θ' := <[o1 := TE S1 (pt_polar b ρ) (Some 2) (Some 3)]> {[o2 := TE S2 (pt_polar b (ρ·0)) (Some 2) (Some 3)]} : tenv).
  eapply (e_app (W_side b) (Some 6) Θ ∅ Θ Θ' hc_empty [] [] []).
  - split; [apply map_disjoint_empty_l|by rewrite map_empty_union].
  - apply lsplit_nil.
  - apply ubu_below_empty.
  - eapply (lbox_force_eq _ _ _ _ _ _ 3 cs_C (Some (pvar 2)) (csl_T S1 S2) TUnit
      (pt_polar b ρ :: pt_polar b (ρ·0) :: ρ·1 :: []) _ (UPt (ρ·1))
      (TProd (TSess S1 (pt_polar b ρ) (Some 1) (Some 3)) (TSess S2 (pt_polar b (ρ·0)) (Some 2) (Some 3))));
      [done|apply csw_hold|by destruct b|by destruct b|done|].
    apply Hbx.
  - apply thage_force2, Ho.
  - apply lage_nil.
  - eapply (e_sub _ _ _ _ _ _ _
      (TProd (TSess S1 (pt_polar b ρ) (Some 2) (Some 3)) (TSess S2 (pt_polar b (ρ·0)) (Some 2) (Some 3))));
      [|apply sub_prod; apply sub_sess; [apply ssub_refl|simpl; lia|apply ssub_refl|simpl; lia]|apply fle_refl
       |exact (λ H, H)].
    eapply (e_pair _ _ Θ' {[o1 := TE S1 (pt_polar b ρ) (Some 2) (Some 3)]}
              {[o2 := TE S2 (pt_polar b (ρ·0)) (Some 2) (Some 3)]} {[o2 := TE S2 (pt_polar b (ρ·0)) (Some 2) (Some 3)]}
              hc_empty [] [] [] []).
    + split; [by apply map_disjoint_singleton_l, lookup_singleton_ne|unfold Θ'; by rewrite insert_union_singleton_l].
    + apply lsplit_nil.
    + apply e_chan; [intros ? Hin; inversion Hin|solve [done|apply fle_refl|cbn; lia]].
    + apply thage_zero. crtk_tac.
    + apply lage_nil.
    + apply e_chan; [intros ? Hin; inversion Hin|solve [done|apply fle_refl|cbn; lia]].
    + apply tage_0.
  - apply fle_inf.
Qed.

Lemma cli_box F : typed W_cli (Some 6) ∅ hc_empty [] F cli (csl_box Sa Sb) (Some 0).
Proof.
  destruct (csl_cli W_cli hc_empty 0) as (c & Hb). change [] with (nones 0).
  eapply lbox_typed; [contr_tac|contr_tac|reflexivity|exact Hb].
Qed.

Lemma srv_box F : typed W_srv (Some 6) ∅ hc_empty [] F srv (csl_box Sb Sa) (Some 0).
Proof.
  destruct (csl_srv W_srv hc_empty 0) as (c & Hb). change [] with (nones 0).
  eapply lbox_typed; [contr_tac|contr_tac|reflexivity|exact Hb].
Qed.

(** ** Each component at its own static world *)

Lemma cli_term (EM : excluded_middle) : lf_sems 6 (khalf (Some 6)) W_cli ΣC (∅, {[+ t_cli +]}) TUnit.
Proof.
  destruct (side_typed true cli Sa Sb oa ob ρ (ρ·0) ltac:(done) cli_box eq_refl eq_refl) as [c Hc].
  apply (lf_p_term EM W_cli 6 (khalf (Some 6)) ΣC ∅ ∅ t_cli TUnit c).
  - apply W_side_wf.
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - intros; apply fhalf_le.
  - set_solver.
  - rewrite tenv_ofk_half. assert (tenv_of (fhalf (Some 6)) ΣC ∪ ∅ =
            <[oa := TE Sa ρ (Some 3) (Some 3)]> {[ob := TE Sb (ρ·0) (Some 3) (Some 3)]}) as ->.
    { unfold tenv_of, ΣC. by rewrite map_union_empty, fmap_insert, map_fmap_singleton. }
    exact Hc.
Qed.

Lemma senv_dual_ΣC :
  senv_dual ΣC = <[edual oa := (Sb, ρ‾)]> {[edual ob := (Sa, (ρ·0)‾)]}.
Proof. unfold senv_dual, ΣC. rewrite fmap_insert, map_fmap_singleton. rewrite kmap_insert; [|apply _]. rewrite kmap_singleton. reflexivity. Qed.

Lemma srv_term (EM : excluded_middle) : lf_sems 6 (khalf (Some 6)) W_srv (senv_dual ΣC) (∅, {[+ t_srv +]}) TUnit.
Proof.
  destruct (side_typed false srv Sb Sa (edual oa) (edual ob) ρ‾ (ρ·0)‾ ltac:(done) srv_box eq_refl eq_refl)
    as [c Hc].
  apply (lf_p_term EM W_srv 6 (khalf (Some 6)) (senv_dual ΣC) ∅ ∅ t_srv TUnit c).
  - apply W_side_wf.
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - intros; apply fhalf_le.
  - set_solver.
  - rewrite tenv_ofk_half. assert (tenv_of (fhalf (Some 6)) (senv_dual ΣC) ∪ ∅ =
            <[edual oa := TE Sb ρ‾ (Some 3) (Some 3)]> {[edual ob := TE Sa (ρ·0)‾ (Some 3) (Some 3)]}) as ->.
    { rewrite senv_dual_ΣC. unfold tenv_of. by rewrite map_union_empty, fmap_insert, map_fmap_singleton. }
    exact Hc.
Qed.

(** ** The composite *)

(** The client and the server, each read at the ranked worlds of its own
    static world, compose over the cut {a, b} to a lock-free process. *)
Theorem cs_split_lock_free : excluded_middle → functional_choice →
  lock_free (∅ ∪ ∅ ∪ chans_of ΣC, {[+ t_cli +]} ⊎ {[+ t_srv +]}).
Proof.
  intros EM FC. destruct W_cs_parts as (H1 & H2 & HS).
  apply (lf_connect_adequacy EM FC 6 (khalf (Some 6)) W_cli W_srv ΣC ∅ ∅ _ _ TUnit (cli_term EM) (srv_term EM) (λ _ _, tsum_fhalf (Some 6)));
    [|set_solver|set_solver|set_solver|apply W_side_wf|apply W_side_wf|done|done|done].
  intros o Ho. unfold ΣC in *. rewrite dom_insert_L, dom_singleton_L in *.
  apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_singleton in Ho as ->;
    rewrite elem_of_union, !elem_of_singleton; intros [H|H]; discriminate.
Qed.

(** ** The composite in the process judgment

    Each thread types at its own world, and P-Connect checks their join
    W_cli ⊔ W_srv, which is well-founded. So the split program types
    ([cs_split_typed]) and is lock free by the soundness of the process
    judgment ([cs_split_lock_free_typed]). *)

Lemma pfree_two (o1 o2 : cend) v1 v2 :
  (o1‾)%cend ≠ o1 → (o1‾)%cend ≠ o2 → (o2‾)%cend ≠ o1 → (o2‾)%cend ≠ o2 → pfree (<[o1 := v1]> {[o2 := v2]}).
Proof.
  intros H1 H2 H3 H4 o Ho Hd. rewrite dom_insert_L, dom_singleton_L in Ho, Hd.
  apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_singleton in Ho as ->;
    apply elem_of_union in Hd as [Hd|Hd]; apply elem_of_singleton in Hd; auto.
Qed.

Lemma cli_hterm : ptyped (Some 6) (khalf (Some 6)) W_cli ΣC (∅, {[+ t_cli +]}) TUnit.
Proof.
  destruct (side_typed true cli Sa Sb oa ob ρ (ρ·0) ltac:(done) cli_box eq_refl eq_refl) as [c Hc].
  apply (p_term_half (Some 6) W_cli ΣC ∅ ∅ t_cli TUnit c).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply pfree_two; done.
  - intros o e. unfold ΣC. rewrite lookup_insert_Some, lookup_singleton_Some.
    intros [[_ <-]|[_ [_ <-]]]; contr_tac.
  - set_solver.
  - assert (tenv_of (fhalf (Some 6)) ΣC ∪ ∅ =
            <[oa := TE Sa ρ (Some 3) (Some 3)]> {[ob := TE Sb (ρ·0) (Some 3) (Some 3)]}) as ->.
    { unfold tenv_of, ΣC. by rewrite map_union_empty, fmap_insert, map_fmap_singleton. }
    exact Hc.
  - split; [apply W_side_wf|apply W_cs_parts].
Qed.

Lemma srv_hterm :
  ptyped (Some 6) (khalf (Some 6)) W_srv (senv_dual ΣC) (∅, {[+ t_srv +]}) TUnit.
Proof.
  destruct (side_typed false srv Sb Sa (edual oa) (edual ob) ρ‾ (ρ·0)‾ ltac:(done) srv_box eq_refl eq_refl)
    as [c Hc].
  apply (p_term_half (Some 6) W_srv (senv_dual ΣC) ∅ ∅ t_srv TUnit c).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - rewrite senv_dual_ΣC. apply pfree_two; done.
  - rewrite senv_dual_ΣC. intros o e. rewrite lookup_insert_Some, lookup_singleton_Some.
    intros [[_ <-]|[_ [_ <-]]]; contr_tac.
  - set_solver.
  - assert (tenv_of (fhalf (Some 6)) (senv_dual ΣC) ∪ ∅ =
            <[edual oa := TE Sb ρ‾ (Some 3) (Some 3)]> {[edual ob := TE Sa (ρ·0)‾ (Some 3) (Some 3)]}) as ->.
    { rewrite senv_dual_ΣC. unfold tenv_of. by rewrite map_union_empty, fmap_insert, map_fmap_singleton. }
    exact Hc.
  - split; [apply W_side_wf|apply W_cs_parts].
Qed.

Theorem cs_split_typed : ∃ W, ptyped (Some 6) (khalf (Some 6)) W ∅ (∅ ∪ ∅ ∪ chans_of ΣC, {[+ t_cli +]} ⊎ {[+ t_srv +]}) TUnit.
Proof.
  eexists. pose proof (p_connect_half (Some 6) W_cli W_srv ∅ ∅ ΣC ∅ ∅ {[+ t_cli +]} {[+ t_srv +]} TUnit) as H.
  rewrite !(left_id_L ∅ (∪)) in H |- *. apply H; clear H; [rewrite (left_id_L ∅ (∪)); exact cli_hterm|rewrite (left_id_L ∅ (∪)); exact srv_hterm|..].
  all: try (rewrite ?chans_of_empty; set_solver).
  exact W_cs_join_wf.
Qed.

Theorem cs_split_lock_free_typed : excluded_middle → functional_choice →
  lock_free (∅ ∪ ∅ ∪ chans_of ΣC, {[+ t_cli +]} ⊎ {[+ t_srv +]}).
Proof.
  intros EM FC. destruct cs_split_typed as [W H]. exact (lf_soundness 6 _ W _ TUnit EM FC H).
Qed.
