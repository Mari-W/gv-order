(** * Terms related occurrence by occurrence (stage S4, compat/Fusion.v)

    [crel R e e'] relates two terms of the same shape whose ends are
    related by R occurrence by occurrence: an end o of e stands opposite
    an end o' of e' with R o o'. Two occurrences of the same end of e may
    stand opposite different ends of e'. [emap g e] is the special case
    of a function ([crel_emap]). [mcrel R] lifts the relation to soups.

    The fusion theorem of P (compat/Fusion.v) relates a process to its
    fusion by [crel] with R o o' := (o held → o' = h o). An end that is
    not held may stand opposite any end, which a single map of ends
    cannot express after a link (decision no-fus, 2026-11-25): a link of
    a restricted end a1 with an end a2 that nobody holds merges the
    occurrences of a1‾ and of a2 into one end a2, while their images may
    differ. *)

From GV Require Export compat.Rename.

Inductive crel (R : cend → cend → Prop) : expr → expr → Prop :=
  | CVar x : crel R (Var x) (Var x)
  | CUnit : crel R EUnit EUnit
  | CChan o o' : R o o' → crel R (Chan o) (Chan o')
  | CLam e e' : crel R e e' → crel R (Lam e) (Lam e')
  | CApp e1 e2 e1' e2' : crel R e1 e1' → crel R e2 e2' → crel R (App e1 e2) (App e1' e2')
  | CPair e1 e2 e1' e2' : crel R e1 e1' → crel R e2 e2' → crel R (Pair e1 e2) (Pair e1' e2')
  | CLetU e1 e2 e1' e2' : crel R e1 e1' → crel R e2 e2' → crel R (LetU e1 e2) (LetU e1' e2')
  | CLetP e1 e2 e1' e2' : crel R e1 e1' → crel R e2 e2' → crel R (LetP e1 e2) (LetP e1' e2')
  | CInj b e e' : crel R e e' → crel R (Inj b e) (Inj b e')
  | CCase e e1 e2 e' e1' e2' : crel R e e' → crel R e1 e1' → crel R e2 e2' →
      crel R (Case e e1 e2) (Case e' e1' e2')
  | CBox e e' : crel R e e' → crel R (EBox e) (EBox e')
  | CNew : crel R ENew ENew
  | COp k e e' : crel R e e' → crel R (Op k e) (Op k e').

Global Hint Constructors crel : core.

Section crel.
  Implicit Types (R : cend → cend → Prop).

  Lemma crel_mono R R' e e' : (∀ o o', o ∈ fends e → R o o' → R' o o') → crel R e e' → crel R' e e'.
  Proof. intros HR H. induction H; simpl in *; constructor; eauto; set_solver. Qed.

  Lemma crel_emap R g e : (∀ o, o ∈ fends e → R o (g o)) → crel R e (emap g e).
  Proof. induction e; simpl; intros H; constructor; eauto; set_solver. Qed.

  Lemma crel_refl R e : (∀ o, o ∈ fends e → R o o) → crel R e e.
  Proof. intros H. rewrite <-(emap_id e) at 2. by apply crel_emap. Qed.

  Lemma crel_compose R1 R2 e1 e2 e3 :
    crel R1 e1 e2 → crel R2 e2 e3 → crel (λ a c, ∃ b, R1 a b ∧ R2 b c) e1 e3.
  Proof. intros H. revert e3. induction H; intros e3 H3; inversion H3; subst; eauto. Qed.

  Lemma crel_flip R e e' : crel R e e' → crel (flip R) e' e.
  Proof. induction 1; eauto. Qed.

  Lemma crel_val R e e' : crel R e e' → is_val e = is_val e'.
  Proof. induction 1; simpl; congruence. Qed.

  Lemma crel_fends R e e' o : crel R e e' → o ∈ fends e → ∃ o', o' ∈ fends e' ∧ R o o'.
  Proof.
    induction 1; simpl; intros Ho;
      repeat match goal with Hx : _ ∈ _ ∪ _ |- _ => apply elem_of_union in Hx as [Hx|Hx] end;
      try set_solver.
    all: try (apply elem_of_singleton in Ho as ->; exists o'; set_solver).
    all: first [destruct (IHcrel1 Ho) as (x & ? & ?)|destruct (IHcrel2 Ho) as (x & ? & ?)
               |destruct (IHcrel3 Ho) as (x & ? & ?)|destruct (IHcrel Ho) as (x & ? & ?)];
      exists x; split; [set_solver|done].
  Qed.

  Lemma crel_fends_r R e e' o' : crel R e e' → o' ∈ fends e' → ∃ o, o ∈ fends e ∧ R o o'.
  Proof. intros H Ho. by destruct (crel_fends (flip R) e' e o' (crel_flip _ _ _ H) Ho) as (o & ? & ?); eauto. Qed.

  Lemma crel_rename R e e' r : crel R e e' → crel R (rename r e) (rename r e').
  Proof. intros H. revert r. induction H; intros r; simpl; eauto. Qed.

  Lemma crel_subst R e e' σ σ' : (∀ x, crel R (σ x) (σ' x)) → crel R e e' → crel R (subst σ e) (subst σ' e').
  Proof.
    intros Hσ H. revert σ σ' Hσ.
    assert (∀ σ σ', (∀ x, crel R (σ x) (σ' x)) → ∀ x, crel R (up σ x) (up σ' x)) as Hup.
    { intros σ σ' Hσ [|x]; simpl; [constructor|]. unfold compose. by apply crel_rename. }
    induction H; intros σ σ' Hσ; simpl; eauto 10.
  Qed.

  Lemma crel_subst1 R v v' e e' : crel R v v' → crel R e e' → crel R (subst1 v e) (subst1 v' e').
  Proof. intros Hv He. apply crel_subst; [|done]. intros [|x]; simpl; auto. Qed.

  Lemma crel_subst2 R u u' v v' e e' : crel R u u' → crel R v v' → crel R e e' →
    crel R (subst2 u v e) (subst2 u' v' e').
  Proof. intros Hu Hv He. apply crel_subst; [|done]. intros [|[|x]]; simpl; auto. Qed.

  (** ** Actions *)

  Definition arel R (a a' : action) : Prop :=
    match a, a' with
    | ABeta, ABeta | AForce, AForce | ANew, ANew => True
    | ASpawn v, ASpawn v' => crel R v v'
    | ARecv o, ARecv o' | AClose o, AClose o' | ABra o, ABra o' => R o o'
    | ASend o v, ASend o' v' => R o o' ∧ crel R v v'
    | ALink o1 o2, ALink o1' o2' => R o1 o1' ∧ R o2 o2'
    | ASel o i, ASel o' i' => R o o' ∧ i = i'
    | _, _ => False
    end.

  Lemma crel_act R e e' : crel R e e' →
    (act e = None ∧ act e' = None) ∨ ∃ a a', act e = Some a ∧ act e' = Some a' ∧ arel R a a'.
  Proof.
    induction 1; simpl; try (by left); try (right; by eexists _, _).
    - rewrite (crel_val _ _ _ H), (crel_val _ _ _ H0).
      destruct (is_val e1') eqn:E1; [destruct (is_val e2') eqn:E2|]; [|done|done].
      inversion H; subst; simpl; try (by left). right. by eexists _, _.
    - rewrite (crel_val _ _ _ H). by destruct (is_val e1').
    - rewrite (crel_val _ _ _ H). destruct (is_val e1'); [|done].
      inversion H; subst; simpl; try (by left). right. by eexists _, _.
    - rewrite (crel_val _ _ _ H). destruct (is_val e1'); [|done].
      inversion H; subst; simpl; try (by left). right. by eexists _, _.
    - exact IHcrel.
    - rewrite (crel_val _ _ _ H). destruct (is_val e'); [|done].
      inversion H; subst; simpl; try (by left). right. by eexists _, _.
    - rewrite (crel_val _ _ _ H). destruct (is_val e') eqn:Ev; [|done].
      destruct k; simpl; inversion H; subst; simpl; try (by left);
        try (right; eexists _, _; split_and!; [reflexivity|reflexivity|simpl; eauto]).
      all: repeat match goal with
        | Hc : crel _ ?a ?b |- context [match ?b with _ => _ end] => inversion Hc; subst; simpl
        end; try (by left); right; eexists _, _; split_and!; [reflexivity|reflexivity|simpl; eauto].
  Qed.

  (** ** Steps *)

  (** What the labels of two related steps must agree on beyond the
      redexes: the received value, the branch, the new channel. *)
  Definition lmatch R (α α' : tlabel) : Prop :=
    match α, α' with
    | LBeta, LBeta | LForce, LForce => True
    | LNew c, LNew c' => R (EPos c) (EPos c') ∧ R (ENeg c) (ENeg c')
    | LSpawn _, LSpawn _ => True
    | LSess (SSend _ _), LSess (SSend _ _) | LSess (SClose _), LSess (SClose _)
    | LSess (SSel _ _), LSess (SSel _ _) | LSess (SLink _), LSess (SLink _) => True
    | LSess (SRecv _ v), LSess (SRecv _ v') => crel R v v'
    | LSess (SBra _ i), LSess (SBra _ i') => i = i'
    | _, _ => False
    end.

  Lemma crel_fill_inv R f e E' : crel R (fill_frame f e) E' →
    ∃ f' e', E' = fill_frame f' e' ∧ crel R e e' ∧
      (frame_val f → frame_val f') ∧ (∀ e1 e1', crel R e1 e1' → crel R (fill_frame f e1) (fill_frame f' e1')).
  Proof.
    intros H. destruct f; simpl in H; inversion H; subst;
      [ eexists (FAppL _) | eexists (FAppR _) | eexists (FPairL _) | eexists (FPairR _)
      | eexists (FLetU _) | eexists (FLetP _) | eexists (FInj _) | eexists (FCase _ _) | eexists (FOp _) ].
    all: eexists; split; [reflexivity|]; split; [eassumption|]; split; [simpl; intros Hv;
      try done; by erewrite <-crel_val|intros x y Hxy; simpl; eauto].
  Qed.

  Lemma crel_head R e e' α f α' f' :
    crel R e e' → head_step e α f → head_step e' α' f' → lmatch R α α' → crel R f f'.
  Proof.
    intros Hc Hh Hh' Hl. inversion Hh; subst; inversion Hc; subst;
      repeat match goal with Hx : crel _ (_ _) _ |- _ => inversion Hx; subst; clear Hx end;
      inversion Hh'; subst; simpl in Hl; try done.
    all: try (by apply crel_subst1; eauto); try (by apply crel_subst2); try done; eauto.
    all: try (destruct Hl as [H1 H2]; by eauto).
    all: subst; eauto.
  Qed.

  Lemma crel_tstep R e e' α f α' f' :
    crel R e e' → tstep e α f → tstep e' α' f' → lmatch R α α' → crel R f f'.
  Proof.
    intros Hc Hs. revert e' α' f' Hc. induction Hs as [e α f Hh|fr e α f Hf Hs IH]; intros e' α' f' Hc Hs' Hl.
    - apply tstep_inv in Hs' as [Hh'|(fr & e0 & e0' & Hf & -> & -> & Hs0)].
      + by eapply crel_head.
      + exfalso. destruct (crel_fill_inv (flip R) fr e0 e) as (fr' & e1 & -> & Hc1 & Hfv & _).
        { by apply crel_flip. }
        apply (val_no_tstep e0 α' e0' Hs0). pose proof (crel_val _ _ _ Hc1) as Ev.
        apply is_val_of_true. rewrite Ev. apply is_val_true.
        apply (head_redex_val fr' e1 α f); [by apply Hfv|done].
    - destruct (crel_fill_inv R fr e e' Hc) as (fr' & e0 & -> & Hc0 & Hfv & Hfill).
      assert (¬ is_val e) as Hv by (intros Hv; exact (val_no_tstep e α f Hs Hv)).
      assert (¬ is_val e0) as Hv0 by (by rewrite <-(crel_val _ _ _ Hc0)).
      destruct (tstep_fill_inv fr' e0 α' f' (Hfv Hf) Hv0 Hs') as (f0 & Hs0 & ->).
      apply Hfill. by apply (IH e0 α' f0).
  Qed.
End crel.

(** ** Soups *)

Definition mrel (R : cend → cend → Prop) (M M' : gmap nat expr) : Prop :=
  ∀ i, match M !! i, M' !! i with
       | Some e, Some e' => crel R e e'
       | None, None => True
       | _, _ => False
       end.

Definition mcrel (R : cend → cend → Prop) (E E' : gmultiset expr) : Prop :=
  ∃ M M', soup M = E ∧ soup M' = E' ∧ mrel R M M'.

Section mcrel.
  Implicit Types (R : cend → cend → Prop).

  Lemma mrel_lookup R M M' i e : mrel R M M' → M !! i = Some e → ∃ e', M' !! i = Some e' ∧ crel R e e'.
  Proof. intros H Hi. specialize (H i). rewrite Hi in H. destruct (M' !! i); [eauto|done]. Qed.

  Lemma mrel_lookup_r R M M' i e' : mrel R M M' → M' !! i = Some e' → ∃ e, M !! i = Some e ∧ crel R e e'.
  Proof. intros H Hi. specialize (H i). rewrite Hi in H. destruct (M !! i); [eauto|done]. Qed.

  Lemma mrel_none R M M' i : mrel R M M' → M !! i = None ↔ M' !! i = None.
  Proof. intros H. specialize (H i). destruct (M !! i), (M' !! i); naive_solver. Qed.

  Lemma mrel_insert R M M' i e e' : mrel R M M' → crel R e e' → mrel R (<[i := e]> M) (<[i := e']> M').
  Proof. intros H He j. destruct (decide (i = j)) as [->|Hne]; [by rewrite !lookup_insert_eq|]. rewrite !lookup_insert_ne by done. apply H. Qed.

  Lemma mrel_delete R M M' i : mrel R M M' → mrel R (delete i M) (delete i M').
  Proof. intros H j. destruct (decide (i = j)) as [->|Hne]; [by rewrite !lookup_delete_eq|]. rewrite !lookup_delete_ne by done. apply H. Qed.

  Lemma mrel_mono R R' M M' : (∀ e e', crel R e e' → crel R' e e') → mrel R M M' → mrel R' M M'.
  Proof. intros HR H i. specialize (H i). destruct (M !! i), (M' !! i); auto. Qed.

  Lemma mrel_dom R M M' : mrel R M M' → dom M = dom M'.
  Proof. intros H. apply set_eq. intros i. rewrite !elem_of_dom, <-!not_eq_None_Some. by rewrite (mrel_none R M M' i H). Qed.

  (** Every lifting of the right soup has a related lifting of the left
      soup. *)
  Lemma mcrel_lift R E E' M' : mcrel R E E' → soup M' = E' → ∃ M, soup M = E ∧ mrel R M M'.
  Proof.
    intros (M0 & M0' & <- & HM0' & Hr) HM'. rewrite <-HM0' in HM'. clear HM0' E'.
    revert M0 M0' Hr HM'.
    induction M' as [|i e' M' Hi IH] using map_ind; intros M0 M0' Hr HM; symmetry in HM.
    - exists M0. split; [done|]. rewrite soup_empty in HM.
      assert (M0' = ∅) as -> by (apply map_empty; intros j; destruct (M0' !! j) eqn:E; [|done];
        exfalso; pose proof (soup_delete M0' j _ E) as Hd; rewrite HM in Hd; multiset_solver).
      intros j. specialize (Hr j). rewrite lookup_empty in Hr |- *. by destruct (M0 !! j).
    - rewrite soup_insert in HM by done.
      destruct (soup_extract M0' (soup M') e') as (k & Hk & Hdel); [done|].
      destruct (mrel_lookup_r R M0 M0' k e' Hr Hk) as (e & He & Hee).
      destruct (IH (delete k M0) (delete k M0') (mrel_delete R _ _ k Hr) (eq_sym Hdel)) as (M1 & HM1 & Hr1).
      exists (<[i := e]> M1). split.
      + rewrite soup_insert; [|by rewrite (mrel_none R M1 M' i Hr1)]. rewrite HM1. by rewrite <-(soup_delete M0 k e He).
      + by apply mrel_insert.
  Qed.

  Lemma mcrel_of_mrel R M M' : mrel R M M' → mcrel R (soup M) (soup M').
  Proof. intros H. by exists M, M'. Qed.

  Lemma mcrel_emapE R g E : (∀ e o, e ∈ E → o ∈ fends e → R o (g o)) → mcrel R E (emapE g E).
  Proof.
    intros H. destruct (soup_surj E) as [M <-]. exists M, (emap g <$> M). split_and!; [done| |].
    - unfold emapE. by rewrite soup_fmap.
    - intros i. rewrite lookup_fmap. destruct (M !! i) eqn:E; simpl; [|done].
      apply crel_emap. intros o Ho. apply (H e); [|done]. apply elem_of_soup. eauto.
  Qed.

  Lemma mcrel_compose R1 R2 E1 E2 E3 : mcrel R1 E1 E2 → mcrel R2 E2 E3 →
    mcrel (λ a c, ∃ b, R1 a b ∧ R2 b c) E1 E3.
  Proof.
    intros H12 (M2 & M3 & HM2 & HM3 & H23).
    destruct (mcrel_lift R1 E1 E2 M2 H12 HM2) as (M1 & HM1 & H12').
    exists M1, M3. split_and!; [done|done|]. intros i. specialize (H12' i). specialize (H23 i).
    destruct (M1 !! i), (M2 !! i), (M3 !! i); try done. by eapply crel_compose.
  Qed.

  Lemma mcrel_mono R R' E E' : (∀ e e', e ∈ E → crel R e e' → crel R' e e') → mcrel R E E' → mcrel R' E E'.
  Proof.
    intros HR (M & M' & HM & HM' & H). exists M, M'. split_and!; [done|done|]. intros i. specialize (H i).
    destruct (M !! i) eqn:E1, (M' !! i); try done. apply HR; [|done]. rewrite <-HM. apply elem_of_soup. eauto.
  Qed.
End mcrel.
