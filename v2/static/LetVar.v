(** * e versus let x = e in x (fx-open, 2026-11-22)

    [let_intro]: e : T gives let x = e in x : T, at the same bound N,
    world W, contexts and cost.

    The converse fails. [let_var_counter]: a forced box whose result is
    the existential ∃ι. Unit types let x = force f in x at Unit, because
    the let opens x and reads the body. The term force f itself types
    only at existentials ([force_types_ex]). E-Open opens an entry of Δ,
    the let puts the value of e there, and no rule opens the result of a
    term that is no variable.

    [let_elim] is what holds, over a Δ with no existential entry. A
    derivation of the let gives e : T1 at the same contexts and at most
    the same cost, together with the use of x : T1 and ∗ : T2 that
    builds T. When neither T1 nor T2 is an existential, e : T itself
    follows, at most at the cost of the let. The proof inverts the
    derivation through E-Sub and E-Pack. Over such a Δ no E-Open applies
    outside, the pair ⟨e, ∗⟩ ends with E-Pair under E-Sub, and the use
    of x is E-Var followed by E-Sub and E-Pack, whose steps apply to e
    ([inv_var_transfer], static/Inversion.v). *)

From GV Require Export static.Inversion static.Sinst.

(** ** Helpers *)

Local Abbreviation lnone Δ := ((λ _ : option ty, None) <$> Δ).

Lemma lsplit_all' Δ : lenv_split Δ Δ (lnone Δ).
Proof. induction Δ as [|[σ|] Δ IH]; simpl; constructor; done. Qed.

Lemma lnone_lookup' (Δ : lenv) (y : nat) (σ : ty) : lnone Δ !! y = Some (Some σ) → False.
Proof. revert y. induction Δ as [|o Δ IH]; intros [|y]; simpl; [done|done|congruence|apply IH]. Qed.

Lemma lheads_lnone' Δ : lenv_heads (lnone Δ) = ∅.
Proof. by induction Δ. Qed.

Lemma lbot_lnone' Δ : lenv_bot (lnone Δ) = false.
Proof. by induction Δ. Qed.

Lemma lage_lnone' c Δ : lage c (lnone Δ) (lnone Δ).
Proof. induction Δ; simpl; constructor; done. Qed.

Lemma tsplit_l' Θ : tsplit Θ Θ ∅.
Proof. split; [apply map_disjoint_empty_r|by rewrite map_union_empty]. Qed.

Lemma thage_nil' c : thage c ∅ ∅.
Proof. intros o. by rewrite lookup_empty. Qed.

Lemma sf_unionb_nil F : sf_unionb F ∅ false = F.
Proof. destruct F as [X o]. unfold sf_unionb. simpl. f_equal. set_solver. Qed.

Lemma tenv_heads_empty' : tenv_heads ∅ = ∅.
Proof. apply set_eq. intros y. rewrite elem_of_tenv_heads. setoid_rewrite lookup_empty. set_solver. Qed.

Lemma fle_fadd_l a b : fle a (fadd a b) ∨ b = None.
Proof. destruct a, b; simpl; auto with lia. Qed.

Lemma fle_fadd_l' a b : fle a (fadd a b).
Proof. destruct a, b; simpl; lia. Qed.

Lemma fle_fadd_r' a b : fle b (fadd a b).
Proof. destruct a, b; simpl; lia. Qed.

(** ** let x = e in x from e *)

Theorem let_intro W N Θ Γ Δ F e T c :
  typed W N Θ Γ Δ F e T c → typed W N Θ Γ Δ F (ELet e (Var 0)) T c.
Proof.
  intros H. rewrite <-(fadd_0_r' c).
  eapply (e_let W N Θ Θ ∅ ∅ Γ Δ Δ (lnone Δ) (lnone Δ)); [apply tsplit_l'|apply lsplit_all'| |apply thage_nil'
    |apply lage_lnone'|].
  - by rewrite tenv_heads_empty', lheads_lnone', lbot_lnone', (left_id_L ∅ (∪)), sf_unionb_nil.
  - apply e_var. split; [done|]. intros [|y] σ' Hne Hy; [done|]. by destruct (lnone_lookup' _ _ _ Hy).
Qed.

(** ** Facts about contexts *)

Lemma lenv_split_inv Δ Δ1 Δ2 j σ :
  lenv_split Δ Δ1 Δ2 → Δ !! j = Some (Some σ) →
  Δ1 !! j = Some (Some σ) ∨ Δ2 !! j = Some (Some σ).
Proof.
  intros H. revert j. induction H as [|Δ Δ1 Δ2 _ IH|σ' Δ Δ1 Δ2 _ IH|σ' Δ Δ1 Δ2 _ IH|U Δ Δ1 Δ2 _ _ IH];
    intros [|j]; simpl; try done; try (by apply IH); intros [= ->]; auto.
Qed.

Lemma lenv_split_noex_l Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_noex Δ → lenv_noex Δ1.
Proof. intros Hs Hn i T Hi. apply (Hn i). by eapply lenv_split_sub_l. Qed.

Lemma lenv_split_contr_l Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_contr Δ → lenv_contr Δ1.
Proof. intros Hs Hn i T Hi. apply (Hn i). by eapply lenv_split_sub_l. Qed.

Lemma tsplit_contr_l Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → tenv_contr Θ → tenv_contr Θ1.
Proof. intros [Hd ->] H o e Ho. apply (H o). by apply lookup_union_Some_l. Qed.

Definition lenv_unl' (Δ : lenv) : Prop := ∀ j σ, Δ !! j = Some (Some σ) → unlimited σ.

Lemma lenv_heads_unl Δ : lenv_unl' Δ → lenv_heads Δ = ∅.
Proof.
  induction Δ as [|[σ|] Δ IH]; intros H; simpl; [done| |by apply IH; intros j; apply (H (S j))].
  rewrite unlimited_heads by (by apply (H 0)). rewrite IH; [set_solver|]. intros j. apply (H (S j)).
Qed.

Lemma lenv_bot_unl Δ : lenv_unl' Δ → lenv_bot Δ = false.
Proof.
  induction Δ as [|[σ|] Δ IH]; intros H; simpl; [done| |by apply IH; intros j; apply (H (S j))].
  rewrite unlimited_hbot by (by apply (H 0)). apply IH. intros j. apply (H (S j)).
Qed.

Lemma lenv_wk_split Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_unl' Δ2 → lenv_wk Δ1 Δ.
Proof.
  induction 1 as [|Δ Δ1 Δ2 _ IH|σ Δ Δ1 Δ2 _ IH|σ Δ Δ1 Δ2 _ IH|U Δ Δ1 Δ2 _ _ IH]; intros H.
  - constructor.
  - constructor. apply IH. intros j. apply (H (S j)).
  - constructor. apply IH. intros j. apply (H (S j)).
  - apply lwk_drop; [by apply (H 0)|]. apply IH. intros j. apply (H (S j)).
  - constructor. apply IH. intros j. apply (H (S j)).
Qed.

Lemma thage_empty_r c Θ Θ' : thage c Θ Θ' → Θ' = ∅ → Θ = ∅.
Proof.
  intros H ->. apply map_eq. intros o. specialize (H o). rewrite lookup_empty in H |- *.
  by destruct (Θ !! o).
Qed.

Lemma lage_unl_back c Δ Δ' : lage c Δ Δ' → lenv_unl' Δ' → lenv_unl' Δ.
Proof.
  intros Ha%lage_Forall2 H j σ Hj. destruct (Forall2_orel_l _ _ _ _ _ Ha Hj) as (σ' & Hj' & Hag).
  eapply tage_unl_r; [exact Hag|]. by apply (H j).
Qed.

Lemma tage_is_ex c T T' : tage c T T' → is_ex T' ↔ is_ex T.
Proof. destruct 1; done. Qed.

Lemma lage_noex c Δ Δ' : lage c Δ Δ' → lenv_noex Δ → lenv_noex Δ'.
Proof.
  intros Ha%lage_Forall2 H j σ' Hj. destruct (Forall2_orel_r _ _ _ _ _ Ha Hj) as (σ & Hj0 & Hag).
  rewrite (tage_is_ex _ _ _ Hag). exact (H j σ Hj0).
Qed.

Lemma lenv_noex_unl Δ : lenv_unl' Δ → lenv_noex Δ.
Proof. intros H j σ Hj. specialize (H j σ Hj). destruct σ; simpl in *; tauto. Qed.

(** Aging lowers credits, a subtype step. *)
Lemma tage_tsub W c T T' : tage c T T' → ∀ Γ, tsub W Γ T T'.
Proof.
  induction 1; intros Γ.
  - apply tsub_refl.
  - apply sub_sess; [apply sequiv_refl|apply fsub_le].
  - apply sub_sess; [apply sequiv_refl|apply fsub_le].
  - apply sub_arr; [apply fle_refl|apply fsub_le|apply tsub_refl|apply tsub_refl].
  - by apply sub_prod.
  - by apply sub_sum.
  - apply sub_ex; [apply hold_open_self|by left|auto].
Qed.

(** ** The use of x and ∗

    The continuation of the let is let ∗ = u in x over Δ = u : T2,
    x : T1, Δc. It holds no end, and every entry of Δc is unlimited,
    whatever E-Open does to T1 and T2. *)

Section cont.
  Context (W : sworld) (N : fuel).

  Lemma inv_cont Θ Γ T2 T1 Δc F T c :
    typed W N Θ Γ (Some T2 :: Some T1 :: Δc) F (LetU (Var 0) (Var 1)) T c →
    Θ = ∅ ∧ lenv_unl' Δc.
  Proof.
    intros H. apply inv_letu in H as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T' & c1 & c2
      & Ho & Hs & Hl & H1 & Ha & Hla & H2).
    destruct (inv_var_ctx _ _ _ _ _ _ _ _ _ H1) as (HΘ1 & _ & Hu1).
    destruct (inv_var_ctx _ _ _ _ _ _ _ _ _ H2) as (HΘ2 & _ & Hu2).
    split.
    - apply (opened_tenv_empty _ _ _ _ _ _ _ _ _ Ho). destruct Hs as [_ ->].
      rewrite HΘ1, (thage_empty_r _ _ _ Ha HΘ2). by rewrite map_union_empty.
    - intros j σ Hj. apply (opened_unl_back _ _ _ _ _ _ _ _ _ Ho (S (S j))); [|done].
      intros σ' Hj'. destruct (lenv_split_inv _ _ _ _ _ Hl Hj') as [Hj1|Hj2].
      + by apply (Hu1 (S (S j))).
      + apply lage_Forall2 in Hla. destruct (Forall2_orel_l _ _ _ _ _ Hla Hj2) as (σ'' & Hj'' & Hag).
        eapply tage_unl_r; [exact Hag|]. by apply (Hu2 (S (S j))).
  Qed.

  (** Over a Δ with no existential entry the use of x is a derivation of
      x at T over the aged context of the second premise of E-LetU. *)
  Lemma inv_cont_noex Θ Γ T2 T1 Δc F T c :
    typed W N Θ Γ (Some T2 :: Some T1 :: Δc) F (LetU (Var 0) (Var 1)) T c →
    lenv_noex (Some T2 :: Some T1 :: Δc) →
    ∃ Δb' T1' c0 cv, Δb' !! 1 = Some (Some T1') ∧ tage c0 T1 T1' ∧ lenv_noex Δb' ∧
      typed W N ∅ Γ Δb' F (Var 1) T cv ∧ fle cv c.
  Proof.
    remember (LetU (Var 0) (Var 1)) as e0 eqn:He. remember (Some T2 :: Some T1 :: Δc) as Δ0 eqn:HΔ.
    induction 1; try discriminate; intros Hn.
    - injection He as -> ->. subst Δ.
      destruct (inv_var_ctx _ _ _ _ _ _ _ _ _ H1) as (_ & _ & _).
      destruct (inv_var_ctx _ _ _ _ _ _ _ _ _ H4) as (HΘ2 & (T0 & H0b) & _).
      apply lage_Forall2 in H3 as Hla. destruct (Forall2_orel_r _ _ _ _ _ Hla H0b) as (A & HA & Hag).
      assert (A = T1) as ->.
      { pose proof (lenv_split_sub_r _ _ _ _ _ H0 HA) as E. simpl in E. congruence. }
      subst Θ2'. exists Δ2', T0, c1, c2. split_and!; [done|done| |exact H4|apply fle_fadd_r'].
      apply (lage_noex _ _ _ H3). intros j σ Hj. apply (Hn j). by eapply lenv_split_sub_r.
    - destruct (IHtyped He HΔ Hn) as (Δb' & T1' & c0 & cv & Hb & Hag & Hnb & Hv & Hc).
      exists Δb', T1', c0, cv. split_and!; [done|done|done| |by eapply fle_trans].
      eapply e_sub; [exact Hv|exact H0|apply fle_refl|exact H2].
    - destruct (IHtyped He HΔ Hn) as (Δb' & T1' & c0 & cv & Hb & Hag & Hnb & Hv & Hc).
      exists Δb', T1', c0, cv. split_and!; [done|done|done| |done].
      eapply e_pack; [exact H|exact H0|exact H1|exact H2|exact Hv].
    - exfalso. subst Δ. exact (Hn _ _ H I).
  Qed.
End cont.

(** ** The pair ⟨e1, e2⟩ at a product

    Over a Δ with no existential entry, a derivation of a pair at
    T1 × T2 is E-Pair under E-Sub, so e1 types at T1. *)

Lemma inv_pair_prod W N Θ Γ Δ F e1 e2 U c :
  typed W N Θ Γ Δ F (Pair e1 e2) U c → lenv_noex Δ → tenv_contr Θ → lenv_contr Δ →
  ∀ A B, U = TProd A B →
  ∃ Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' T2 c1 c2,
    tsplit Θ Θ1 Θ2 ∧ lenv_split Δ Δ1 Δ2 ∧
    typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 A c1 ∧
    thage c1 Θ2 Θ2' ∧ lage c1 Δ2 Δ2' ∧
    typed W N Θ2' Γ Δ2' (sf_unionb F (heads T2) (hbot T2)) e2 B c2 ∧ fle c1 c.
Proof.
  intros H. remember (Pair e1 e2) as e0 eqn:He. induction H; try discriminate; intros Hn HcΘ HcΔ A B HU.
  - injection He as -> ->. injection HU as <- <-.
    assert (tcontr (TProd T1' T2)) as Hc.
    { eapply typed_scontr; [|done|done]. eapply e_pair; eauto. }
    cbn [tcontr] in Hc. apply Is_true_andb in Hc as [HcA HcB].
    exists Θ1, Θ2, Θ2', Δ1, Δ2, Δ2', T1, (fadd c1 (Some 0)), c2. split_and!; try done.
    + eapply e_sub; [exact H1|by eapply tage_tsub|rewrite fadd_0_r'; apply fle_refl|by intros _].
    + rewrite fadd_0_r'. done.
    + rewrite fadd_0_r'. done.
    + rewrite fadd_0_r'. apply fle_fadd_l'.
  - subst T'. inversion H0 as [| | ? A' B' ? ? HA HB | | | |]; subst T.
    destruct (IHtyped He Hn HcΘ HcΔ A' B' eq_refl)
      as (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T2 & c1 & c2 & Hs & Hl & Hy1 & Ha & Hla & Hy2 & Hc).
    assert (tcontr (TProd A B)) as Hct.
    { eapply typed_scontr; [|done|done]. eapply e_sub; eauto. }
    cbn [tcontr] in Hct. apply Is_true_andb in Hct as [HcA HcB].
    exists Θ1, Θ2, Θ2', Δ1, Δ2, Δ2', T2, c1, c2. split_and!; try done.
    + eapply e_sub; [exact Hy1|exact HA|apply fle_refl|by intros _].
    + eapply e_sub; [exact Hy2|exact HB|apply fle_refl|].
      intros _. done.
    + by eapply fle_trans.
  - exfalso. exact (Hn _ _ H I).
Qed.

(** ** The converse, over a Δ with no existential entry *)

Theorem let_elim W N Θ Γ Δ F e T c :
  tenv_contr Θ → lenv_contr Δ → lenv_noex Δ →
  typed W N Θ Γ Δ F (ELet e (Var 0)) T c →
  ∃ T1 T2 Δc c1 c2,
    typed W N Θ Γ Δ F e T1 c1 ∧ fle c1 c ∧ lenv_unl' Δc ∧
    typed W N ∅ Γ (Some T2 :: Some T1 :: Δc) F (LetU (Var 0) (Var 1)) T c2 ∧
    (¬ is_ex T1 → ¬ is_ex T2 → ∃ c', typed W N Θ Γ Δ F e T c' ∧ fle c' c).
Proof.
  intros HcΘ' HcΔ' Hn' H. remember (ELet e (Var 0)) as e0 eqn:He.
  revert HcΘ' HcΔ' Hn'. induction H; try discriminate; intros HcΘ HcΔ Hn.
  - (* E-LetP *)
    unfold ELet in He. injection He as -> ->. cbn [rename] in H4.
    destruct (inv_cont _ _ _ _ _ _ _ _ _ _ H4) as (HΘ2' & Hu2).
    assert (Θ2 = ∅) as -> by exact (thage_empty_r _ _ _ H2 HΘ2').
    assert (lenv_unl' Δ2) as Hu2' by exact (lage_unl_back _ _ _ H3 Hu2).
    destruct H as [_ HΘ]. rewrite map_union_empty in HΘ. subst Θ1.
    rewrite tenv_heads_empty', lenv_heads_unl, lenv_bot_unl, (left_id_L ∅ (∪)), sf_unionb_nil in H1 by done.
    destruct (inv_pair_prod _ _ _ _ _ _ _ _ _ _ H1 (lenv_split_noex_l _ _ _ H0 Hn) HcΘ
      (lenv_split_contr_l _ _ _ H0 HcΔ) T1 T2 eq_refl)
      as (Θ3 & Θ4 & Θ4' & Δ3 & Δ4 & Δ4' & T4 & c3 & c4 & Hs3 & Hl3 & He3 & Ha3 & Hla3 & Hu & Hc3).
    destruct (inv_unit_ctx _ _ _ _ _ _ _ _ Hu) as [HΘ4' Hu4].
    assert (Θ4 = ∅) as -> by exact (thage_empty_r _ _ _ Ha3 HΘ4').
    assert (lenv_unl' Δ4) as Hu4' by exact (lage_unl_back _ _ _ Hla3 Hu4).
    destruct Hs3 as [_ HΘ3]. rewrite map_union_empty in HΘ3. subst Θ3.
    rewrite tenv_heads_empty', lenv_heads_unl, lenv_bot_unl, (left_id_L ∅ (∪)), sf_unionb_nil in He3 by done.
    assert (typed W N Θ Γ Δ F e T1 c3) as HeT.
    { eapply e_weak; [exact (lenv_wk_split _ _ _ H0 Hu2')|].
      eapply e_weak; [exact (lenv_wk_split _ _ _ Hl3 Hu4')|exact He3]. }
    assert (fle c3 (fadd c1 c2)) as Hc3' by (eapply fle_trans; [exact Hc3|apply fle_fadd_l']).
    exists T1, T2, Δ2', c3, c2. split_and!; [done|done|done|by rewrite <-HΘ2'|].
    intros HT1 HT2.
    assert (lenv_noex (Some T2 :: Some T1 :: Δ2')) as Hn'.
    { intros [|[|j]] σ Hj; simpl in Hj; [by injection Hj as <-|by injection Hj as <-|].
      exact (lenv_noex_unl Δ2' Hu2 j σ Hj). }
    destruct (inv_cont_noex _ _ _ _ _ _ _ _ _ _ H4 Hn')
      as (Δb' & T1' & c0 & cv & Hb & Hag & Hnb & Hv & Hcv).
    pose proof (inv_var_transfer _ _ _ _ _ _ _ _ _ _ Hv Hnb Hb) as Htr.
    exists (fadd c3 cv). split.
    + apply (Htr Θ Δ F e c3). eapply e_sub; [exact HeT|by eapply tage_tsub|apply fle_refl|].
      by rewrite (tage_tcontr _ _ _ Hag).
    + by apply fle_fadd_mono.
  - destruct (IHtyped He HcΘ HcΔ Hn) as (T1 & T2 & Δc & c1 & c2 & Hy1 & Hc1 & Hu & Hk & Hx).
    exists T1, T2, Δc, c1, c2. split_and!; [done|by eapply fle_trans|done| |].
    + eapply e_sub; [exact Hk|exact H0|apply fle_refl|exact H2].
    + intros HT1 HT2. destruct (Hx HT1 HT2) as (c'' & He' & Hc''). exists c''. split; [|by eapply fle_trans].
      eapply e_sub; [exact He'|exact H0|apply fle_refl|exact H2].
  - destruct (IHtyped He HcΘ HcΔ Hn) as (T1 & T2 & Δc & c1 & c2 & Hy1 & Hc1 & Hu & Hk & Hx).
    exists T1, T2, Δc, c1, c2. split_and!; [done|done|done| |].
    + eapply e_pack; [exact H|exact H0|exact H1|exact H2|exact Hk].
    + intros HT1 HT2. destruct (Hx HT1 HT2) as (c'' & He' & Hc''). exists c''. split; [|done].
      eapply e_pack; [exact H|exact H0|exact H1|exact H2|exact He'].
  - exfalso. exact (Hn _ _ H I).
Qed.
