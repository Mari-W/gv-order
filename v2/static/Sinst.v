(** * Session instantiation preserves typing (item 1 of 2026-11-21)

    [typed_sinst]: a derivation over contexts whose session types are
    contractive, instantiated at contractive, scoped instances, is a
    derivation. Checking a box body once at the identity instance is
    then enough for every instance (finding 6.1 of
    docs/redesign/algorithmic-plan.md).

    The proof is one induction on the judgment. Three facts carry it.

    - [typed_scontr]. Over contractive contexts every derived type is
      contractive, because every rule that brings in a session type asks
      it contractive (E-Abs, E-Inj, E-Box, E-New, E-Sub).
    - [sequiv_sinst] and [teq_sinst] (types/Contractive.v) for E-Sub.
    - [unfoldS_sinst_*] (types/Contractive.v) for the actions. The
      continuation of an instance is ≈ to the instance of the
      continuation, and E-Sub closes the gap.

    A box body at an instance ss'' of the instantiated box is the body at
    the instance ss'' shifted past every free variable of the box and its
    context, instantiated by σ below that bound ([tfv], [lfv]).
    examples/SinstStuck.v shows that the premise on the contexts is
    needed. *)

From GV Require Export static.Inversion.

(** ** Contractive contexts *)

Definition tenv_contr (Θ : tenv) : Prop := ∀ o e, Θ !! o = Some e → scontr (te_sty e).
Definition lenv_contr (Δ : lenv) : Prop := ∀ i T, Δ !! i = Some (Some T) → tcontr T.

Lemma tage_tcontr c T T' : tage c T T' → tcontr T' = tcontr T.
Proof. induction 1; simpl; congruence. Qed.

Lemma lage_contr c Δ Δ' : lage c Δ Δ' → lenv_contr Δ → lenv_contr Δ'.
Proof.
  induction 1 as [|Δ Δ' _ IH|σ σ' Δ Δ' Ht _ IH]; intros H [|i] T Hi; simpl in Hi; try done.
  - apply (IH (λ j U Hj, H (S j) U Hj) i T Hi).
  - injection Hi as <-. rewrite (tage_tcontr _ _ _ Ht). by apply (H 0).
  - apply (IH (λ j U Hj, H (S j) U Hj) i T Hi).
Qed.

Lemma thage_contr c Θ Θ' : thage c Θ Θ' → tenv_contr Θ → tenv_contr Θ'.
Proof.
  intros Ht H o e He. specialize (Ht o). rewrite He in Ht.
  destruct (Θ !! o) as [e0|] eqn:E; [|done]. destruct Ht as (-> & _). by apply (H o).
Qed.

Lemma tsplit_contr Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → tenv_contr Θ → tenv_contr Θ1 ∧ tenv_contr Θ2.
Proof.
  intros [Hd ->] H. split; intros o e He; apply (H o).
  - by apply lookup_union_Some_l.
  - by apply lookup_union_Some_r.
Qed.

Lemma lenv_split_lookup Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → ∀ i T,
  (Δ1 !! i = Some (Some T) ∨ Δ2 !! i = Some (Some T)) → Δ !! i = Some (Some T).
Proof.
  induction 1 as [|Δ Δ1 Δ2 _ IH|σ Δ Δ1 Δ2 _ IH|σ Δ Δ1 Δ2 _ IH|U Δ Δ1 Δ2 _ _ IH];
    intros [|i] T [Hi|Hi]; simpl in *; try done; auto.
Qed.

Lemma lenv_split_contr Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_contr Δ → lenv_contr Δ1 ∧ lenv_contr Δ2.
Proof.
  intros Hs H. split; intros i T Hi; apply (H i); eapply lenv_split_lookup; eauto.
Qed.

Lemma lenv_contr_cons o Δ : lenv_contr (o :: Δ) ↔ (∀ T, o = Some T → tcontr T) ∧ lenv_contr Δ.
Proof.
  split.
  - intros H. split; [intros T ->; by apply (H 0)|]. intros i T Hi. by apply (H (S i)).
  - intros [H1 H2] [|i] T Hi; simpl in Hi; [injection Hi as ->; by apply H1|by apply H2 in Hi].
Qed.

Lemma lenv_contr_some T Δ : tcontr T → lenv_contr Δ → lenv_contr (Some T :: Δ).
Proof. intros. apply lenv_contr_cons. split; [by intros ? [= <-]|done]. Qed.

Lemma lenv_contr_pinst σ Δ : lenv_contr Δ → lenv_contr (lenv_pinst σ Δ).
Proof.
  intros H i T Hi. rewrite lenv_pinst_lookup in Hi.
  destruct (Δ !! i) as [[U|]|] eqn:E; simplify_eq/=. rewrite tcontr_pinst. by apply (H i).
Qed.

Lemma tenv_contr_pinst σ Θ : tenv_contr Θ → tenv_contr (tenv_pinst σ Θ).
Proof.
  intros H o e He. unfold tenv_pinst in He. rewrite lookup_fmap in He.
  destruct (Θ !! o) as [e0|] eqn:E; simplify_eq/=. by apply (H o).
Qed.

Lemma lenv_contr_insert Δ i T : tcontr T → lenv_contr Δ → lenv_contr (<[i := Some T]> Δ).
Proof.
  intros HT H j U Hj. destruct (decide (i = j)) as [->|Hne].
  - apply list_lookup_insert_Some in Hj as [(_ & [= <-] & _)|[? _]]; done.
  - rewrite list_lookup_insert_ne in Hj by done. by apply (H j).
Qed.

Lemma lenv_only_contr Δ x T : lenv_only Δ x T → lenv_contr Δ → tcontr T.
Proof. intros [Hx _] H. by apply (H x). Qed.

Lemma tenv_contr_empty : tenv_contr ∅.
Proof. intros o e. by rewrite lookup_empty. Qed.

Lemma tenv_contr_singleton o e : scontr (te_sty e) → tenv_contr {[o := e]}.
Proof. intros H o' e' He. by apply lookup_singleton_Some in He as [_ <-]. Qed.

Local Ltac tc_split H := cbn [tcontr] in H; apply Is_true_andb in H as [? ?].

(** Over contractive contexts every derived type is contractive. *)
Theorem typed_scontr W N Θ Γ Δ F e T c :
  typed W N Θ Γ Δ F e T c → tenv_contr Θ → lenv_contr Δ → tcontr T.
Proof.
  induction 1 as
    [Γ Δ F HΔ
    |Γ Δ F x T HΔ
    |Γ Δ F o S x a mt HΔ
    |Θ Θh Γ Δ Δh F e T U ub lb c a Hlb Hth Hlc HTc Hb IH
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c T U a1 c1 c2 Hsp Hl Hub H1 IH1 Hta Hla H2 IH2 Hc
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T1' T2 c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2 Hag
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T2 T c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2
    |i Θ Γ Δ F e T U c HTc H IH
    |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e e1 e2 T1 T2 T c0 c1 c2 Hsp Hl H0 IH0 Hta Hla H1 IH1 H2 IH2
    |Γ Δ F e m k C ub c U HΔ HUc Hb IH
    |Θ Γ Δ F e m k C ub c U xs ss c0 Hxs HC Hss Hsi Hub H IH
    |Θ Γ Δ F e S0 x m T S aS mS Tp Tp' c0 Hu Hsc Hbot Hh Hub H IH Hag Hsub
    |Θ Γ Δ F e S0 x m T S a mS c0 Hu Hsc Hub H IH
    |Θ Γ Δ F e S0 x a mS c0 Hu Hub H IH
    |i Θ Γ Δ F e S0 x S1 S2 a mS c0 Hu Hub H IH
    |Θ Γ Δ F e S0 x S1 S2 a mS c0 Hu Hub H IH
    |Θ Γ Δ F e S x a1 m1 a2 m2 c0 H IH Hl1 Hl2
    |Θ Γ Δ F e ub lb c' a c0 H IH Hle
    |Γ Δ F C S m1 m2 HΔ HC Htk HSc
    |Γ Δ F x κf S m1 m2 HΔ Htk HSc
    |Θ Γ Δ F e T T' c c' H IH Hsub Hc HTc
    |Θ Γ Δ F e lb m C T xs c Hxs HC Hlb Hwf H IH
    |Θ Γ Δ F e i lb m C T U c Hi Hun Hcons H IH]; intros HΘ HΔc.
  - done.
  - by eapply lenv_only_contr.
  - exact (HΘ o _ (lookup_singleton_eq _ _)).
  - cbn [tcontr]. apply Is_true_andb. split; [done|].
    apply IH; [by eapply thage_contr|apply lenv_contr_some; [done|by eapply lage_contr]].
  - destruct (tsplit_contr _ _ _ Hsp HΘ), (lenv_split_contr _ _ _ Hl HΔc).
    assert (tcontr (TLolli ub lb c T U a1)) as HL by auto. by tc_split HL.
  - destruct (tsplit_contr _ _ _ Hsp HΘ), (lenv_split_contr _ _ _ Hl HΔc).
    cbn [tcontr]. apply Is_true_andb. split.
    + rewrite (tage_tcontr _ _ _ Hag). auto.
    + apply IH2; [by eapply thage_contr|by eapply lage_contr].
  - destruct (tsplit_contr _ _ _ Hsp HΘ), (lenv_split_contr _ _ _ Hl HΔc).
    apply IH2; [by eapply thage_contr|by eapply lage_contr].
  - destruct (tsplit_contr _ _ _ Hsp HΘ), (lenv_split_contr _ _ _ Hl HΔc).
    assert (tcontr (TProd T1 T2)) as HP by auto. tc_split HP.
    apply IH2; [by eapply thage_contr|]. apply lenv_contr_some; [done|]. apply lenv_contr_some; [done|].
    by eapply lage_contr.
  - done.
  - destruct (tsplit_contr _ _ _ Hsp HΘ), (lenv_split_contr _ _ _ Hl HΔc).
    assert (tcontr (TSum T1 T2)) as HS by auto. tc_split HS.
    apply IH1; [by eapply thage_contr|]. apply lenv_contr_some; [done|]. by eapply lage_contr.
  - done.
  - assert (tcontr (TBox m k C ub c U)) as HB by auto. cbn [tcontr] in HB.
    apply tcontr_sinst; [apply scontr_slist, Hsi|]. by rewrite tcontr_ty_inst.
  - assert (tcontr (TProd Tp (TSess S0 x aS mS))) as HP by auto. tc_split HP.
    by destruct (unfoldS_seq_contr _ _ _ H1 Hu).
  - assert (tcontr (TSess S0 x a mS)) as HP by auto. cbn [tcontr] in HP.
    destruct (unfoldS_seq_contr _ _ _ HP Hu). cbn [tcontr]. apply Is_true_andb. split; [|done].
    unfold payload_at. by rewrite tcontr_ty_inst.
  - done.
  - assert (tcontr (TSess S0 x a mS)) as HP by auto. cbn [tcontr] in HP.
    destruct (unfoldS_choice_contr S0 S1 S2 HP (or_introl Hu)). by destruct i.
  - assert (tcontr (TSess S0 x a mS)) as HP by auto. cbn [tcontr] in HP.
    destruct (unfoldS_choice_contr S0 S1 S2 HP (or_intror Hu)). cbn [tcontr]. by apply Is_true_andb.
  - done.
  - done.
  - cbn [tcontr]. repeat (apply Is_true_andb; split); try done. by rewrite scontr_dual.
  - cbn [tcontr]. apply Is_true_andb; split; [done|]. by rewrite scontr_dual.
  - auto.
  - cbn [tcontr]. rewrite <-(tcontr_ty_inst xs). auto.
  - rewrite <-(tcontr_pinst (pshift m)). apply IH; [by apply tenv_contr_pinst|].
    apply lenv_contr_insert; [|by apply lenv_contr_pinst].
    assert (tcontr (TEx lb m C T)) as HE by (by apply (HΔc i)). done.
Qed.

(** ** Instantiation of contexts *)

Definition tentry_sinst (σ : nat → sty) (e : tentry) : tentry :=
  TE (sinst σ (te_sty e)) (te_pt e) (te_cr e) (te_tk e).
Definition tenv_sinst (σ : nat → sty) (Θ : tenv) : tenv := tentry_sinst σ <$> Θ.
Definition lenv_sinst (σ : nat → sty) (Δ : lenv) : lenv := fmap (M:=option) (sinst_ty σ) <$> Δ.

Lemma heads_sinst σ T : heads (sinst_ty σ T) = heads T.
Proof. induction T; simpl; congruence. Qed.
Lemma hbot_sinst σ T : hbot (sinst_ty σ T) = hbot T.
Proof. induction T; simpl; try congruence; by destruct lb. Qed.
Lemma unlimited_sinst σ T : unlimited (sinst_ty σ T) ↔ unlimited T.
Proof. by destruct T. Qed.
Lemma tfree_sinst σ T : tfree T → tfree (sinst_ty σ T).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma tenv_sinst_empty σ : tenv_sinst σ ∅ = ∅.
Proof. apply fmap_empty. Qed.
Lemma tenv_sinst_singleton σ o S x a m : tenv_sinst σ {[o := TE S x a m]} = {[o := TE (sinst σ S) x a m]}.
Proof. unfold tenv_sinst. by rewrite map_fmap_singleton. Qed.

Lemma tsplit_sinst σ Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → tsplit (tenv_sinst σ Θ) (tenv_sinst σ Θ1) (tenv_sinst σ Θ2).
Proof. intros [Hd ->]. split; [by apply map_disjoint_fmap|]. unfold tenv_sinst. by rewrite map_fmap_union. Qed.

Lemma tenv_heads_sinst σ Θ : tenv_heads (tenv_sinst σ Θ) = tenv_heads Θ.
Proof.
  apply set_eq. intros y. rewrite !elem_of_tenv_heads. unfold tenv_sinst.
  setoid_rewrite lookup_fmap. split.
  - intros (o & e & He & ->). destruct (Θ !! o) as [e0|] eqn:E; simplify_eq/=. eauto.
  - intros (o & e & He & ->). exists o, (tentry_sinst σ e). by rewrite He.
Qed.

Lemma lenv_sinst_lookup σ Δ i : lenv_sinst σ Δ !! i = fmap (M:=option) (sinst_ty σ) <$> Δ !! i.
Proof. unfold lenv_sinst. by rewrite list_lookup_fmap. Qed.

Lemma lenv_only_sinst σ Δ x T : lenv_only Δ x T → lenv_only (lenv_sinst σ Δ) x (sinst_ty σ T).
Proof.
  intros [Hx Hy]. split; [by rewrite lenv_sinst_lookup, Hx|].
  intros y σ' Hne Hσ. rewrite lenv_sinst_lookup in Hσ.
  destruct (Δ !! y) as [[U|]|] eqn:E; simplify_eq/=. apply unlimited_sinst. exact (Hy y U Hne E).
Qed.

Lemma lenv_split_sinst σ Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_split (lenv_sinst σ Δ) (lenv_sinst σ Δ1) (lenv_sinst σ Δ2).
Proof.
  induction 1 as [|? ? ? _ IH|T ? ? ? _ IH|T ? ? ? _ IH|U ? ? ? HU _ IH];
    simpl; constructor; try done. by apply unlimited_sinst.
Qed.

Lemma lenv_unl_sinst σ Δ : lenv_unl Δ → lenv_unl (lenv_sinst σ Δ).
Proof.
  intros H o Ho. unfold lenv_sinst in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (H o' Ho') as [->|(U & -> & HU)]; [by left|right].
  eexists _. split; [done|]. by apply unlimited_sinst.
Qed.

Lemma lenv_heads_sinst σ Δ : lenv_heads (lenv_sinst σ Δ) = lenv_heads Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; rewrite ?heads_sinst; congruence. Qed.
Lemma lenv_bot_sinst σ Δ : lenv_bot (lenv_sinst σ Δ) = lenv_bot Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; rewrite ?hbot_sinst; congruence. Qed.

Lemma thage_sinst σ c Θ Θ' : thage c Θ Θ' → thage c (tenv_sinst σ Θ) (tenv_sinst σ Θ').
Proof.
  intros H o. specialize (H o). unfold tenv_sinst. rewrite !lookup_fmap.
  destruct (Θ !! o), (Θ' !! o); simpl in *; try done.
  destruct H as (E1 & E2 & E3 & E4 & E5). unfold tentry_sinst. simpl. by rewrite E1, E2, E3, E5.
Qed.

Section with_σ.
  Context (σ : nat → sty) (Hσ : ∀ a, scontr (σ a)).

  Lemma tage_sinst c T T' : tage c T T' → tcontr T → tage c (sinst_ty σ T) (sinst_ty σ T').
  Proof.
    induction 1; intros HT; simpl in *; contr_simpl.
    - by apply age_free, tfree_sinst.
    - by apply age_sess.
    - apply age_idle. by apply idle_sinst.
    - by apply age_arr.
    - apply age_prod; auto.
    - apply age_sum; auto.
    - apply age_ex; auto.
  Qed.

  Lemma lage_sinst c Δ Δ' : lage c Δ Δ' → lenv_contr Δ → lage c (lenv_sinst σ Δ) (lenv_sinst σ Δ').
  Proof.
    induction 1 as [|Δ Δ' _ IH|T T' Δ Δ' Ht _ IH]; intros H; simpl; constructor.
    - apply IH. by apply lenv_contr_cons in H as [_ ?].
    - apply tage_sinst; [done|]. by apply (H 0).
    - apply IH. by apply lenv_contr_cons in H as [_ ?].
  Qed.
End with_σ.

Lemma payload_at_sinst σ m T x : sinst_ty σ (payload_at m T x) = payload_at m (sinst_ty σ T) x.
Proof. unfold payload_at, ty_inst. by rewrite pinst_sinst. Qed.

Lemma ty_inst_sinst σ xs T : sinst_ty σ (ty_inst xs T) = ty_inst xs (sinst_ty σ T).
Proof. unfold ty_inst. by rewrite pinst_sinst. Qed.

Lemma lenv_sinst_pinst σ ρ Δ : lenv_sinst σ (lenv_pinst ρ Δ) = lenv_pinst ρ (lenv_sinst σ Δ).
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal]. by rewrite pinst_sinst, IH. Qed.

Lemma tenv_sinst_pinst σ ρ Θ : tenv_sinst σ (tenv_pinst ρ Θ) = tenv_pinst ρ (tenv_sinst σ Θ).
Proof.
  unfold tenv_sinst, tenv_pinst. rewrite <-!map_fmap_compose. apply map_fmap_ext.
  intros _ [S x a m] _. done.
Qed.

Lemma lenv_sinst_insert σ Δ i o : lenv_sinst σ (<[i := o]> Δ) = <[i := fmap (M:=option) (sinst_ty σ) o]> (lenv_sinst σ Δ).
Proof. unfold lenv_sinst. by rewrite list_fmap_insert. Qed.

(** *** Scoping *)

Lemma scoped_sren_mut :
  (∀ T k r, pscoped k (sren_ty r T) ↔ pscoped k T) ∧ (∀ s r, sscoped (sren r s) ↔ sscoped s).
Proof. apply ty_sty_mut_ind; intros; simpl; try done; naive_solver. Qed.

Lemma scoped_sflip_mut :
  (∀ T k j, pscoped k (sflip_ty j T) ↔ pscoped k T) ∧ (∀ s j, sscoped (sflip j s) ↔ sscoped s).
Proof. apply ty_sty_mut_ind; intros; simpl; try (by destruct (decide _)); try done; naive_solver. Qed.

Lemma sscoped_dual s : sscoped (dual s) ↔ sscoped s.
Proof. induction s; simpl; try done; rewrite ?(proj2 scoped_sflip_mut); naive_solver. Qed.

Lemma sscoped_iter_sty_up k σ : (∀ a, sscoped (σ a)) → ∀ a, sscoped (Nat.iter k sty_up σ a).
Proof.
  revert σ. induction k as [|k IH]; intros σ H; simpl; [done|].
  intros [|a]; simpl; [done|]. unfold compose. apply (proj2 scoped_sren_mut). by apply IH.
Qed.

Lemma scoped_sinst_mut :
  (∀ T k σ, (∀ a, sscoped (σ a)) → pscoped k T → pscoped k (sinst_ty σ T)) ∧
  (∀ s σ, (∀ a, sscoped (σ a)) → sscoped s → sscoped (sinst σ s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *; try done; try naive_solver.
  - destruct H1 as (? & ? & ?). split_and!; try done. apply H; [|done]. by apply sscoped_iter_sty_up.
  - apply H; [|done]. by apply (sscoped_iter_sty_up 1).
  - by apply sscoped_dual.
Qed.

(** *** Subtyping *)

Lemma tsub_sinst σ T U : (∀ a, scontr (σ a)) → tsub T U → tcontr T → tcontr U →
  tsub (sinst_ty σ T) (sinst_ty σ U).
Proof.
  intros Hσ. induction 1; intros HT HU; simpl in *; contr_simpl.
  - constructor.
  - apply sub_arr; auto.
  - apply sub_prod; auto.
  - apply sub_sum; auto.
  - apply sub_box; [done|]. destruct k; [|by subst]. simpl. by apply teq_sinst.
  - apply sub_sess; [|done]. by apply sequiv_sinst.
  - apply sub_ex; auto.
Qed.

(** ** A bound on the free session variables *)

Fixpoint tfv (T : ty) : nat :=
  match T with
  | TUnit => 0
  | TLolli _ _ _ T1 U _ | TProd T1 U | TSum T1 U => tfv T1 `max` tfv U
  | TBox _ k _ _ _ U => tfv U - k
  | TSess s _ _ _ => sfv s
  | TEx _ _ _ T1 => tfv T1
  end
with sfv (s : sty) : nat :=
  match s with
  | SRcv _ T | SSnd _ T => tfv T
  | SEnd | SSkip => 0
  | SMu b => sfv b - 1
  | SVar a | SVarD a => S a
  | SSeq a b | SPlus a b | SWith a b => sfv a `max` sfv b
  end.

Lemma iter_sty_up_agree k n σ τ : (∀ a, a < n - k → σ a = τ a) →
  ∀ a, a < n → Nat.iter k sty_up σ a = Nat.iter k sty_up τ a.
Proof.
  revert n σ τ. induction k as [|k IH]; intros n σ τ H a Ha; simpl.
  - apply H. lia.
  - destruct a as [|a]; simpl; [done|]. unfold compose. f_equal.
    apply (IH (n - 1)); [intros b Hb; apply H; lia|lia].
Qed.

Lemma sinst_fv_mut :
  (∀ T σ τ, (∀ a, a < tfv T → σ a = τ a) → sinst_ty σ T = sinst_ty τ T) ∧
  (∀ s σ τ, (∀ a, a < sfv s → σ a = τ a) → sinst σ s = sinst τ s).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *; f_equal; auto with lia.
  - apply H. intros b Hb. apply (iter_sty_up_agree k (tfv U)); [|done]. intros d Hd. apply H0. lia.
  - apply H. intros b Hb. apply (iter_sty_up_agree 1 (sfv S)); [|done]. intros d Hd. apply H0. lia.
Qed.

Fixpoint lfv (Δ : lenv) : nat :=
  match Δ with [] => 0 | Some T :: Δ' => tfv T `max` lfv Δ' | None :: Δ' => lfv Δ' end.

Lemma lenv_sinst_fv σ τ Δ : (∀ a, a < lfv Δ → σ a = τ a) → lenv_sinst σ Δ = lenv_sinst τ Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; intros H; simpl in *; [done| |by rewrite IH].
  rewrite IH by (intros; apply H; lia). f_equal. f_equal. apply sinst_fv_mut. intros; apply H; lia.
Qed.

Lemma tfv_pinst ρ T : tfv (pinst_ty ρ T) = tfv T.
Proof. revert ρ. induction T; intros ρ; simpl; try done; congruence. Qed.

Lemma lfv_pinst ρ Δ : lfv (lenv_pinst ρ Δ) = lfv Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |done]. by rewrite tfv_pinst, IH. Qed.

(** *** The instance of a box *)

Lemma iter_sty_up_lt k σ a : a < k → Nat.iter k sty_up σ a = SVar a.
Proof.
  revert σ a. induction k as [|k IH]; intros σ a Ha; [lia|]. simpl.
  destruct a as [|a]; simpl; [done|]. unfold compose. rewrite IH by lia. done.
Qed.

Lemma iter_sty_up_ge k σ b : Nat.iter k sty_up σ (k + b) = sren (Nat.add k) (σ b).
Proof.
  revert σ b. induction k as [|k IH]; intros σ b; simpl.
  - transitivity (sinst SVar (σ b)); [by rewrite sinst_ids|].
    rewrite <-(sinst_ids (sren _ _)), sinst_sren. by apply sinst_ext.
  - unfold compose. rewrite IH, sren_sren. by apply sren_ext_mut.
Qed.

Lemma slist_shift ss b : slist ss (length ss + b) = SVar b.
Proof. unfold slist. rewrite lookup_ge_None_2 by lia. f_equal. lia. Qed.

Lemma sinst_slist_shift ss s : sinst (slist ss) (sren (Nat.add (length ss)) s) = s.
Proof. rewrite sinst_sren. transitivity (sinst SVar s); [|apply sinst_ids]. apply sinst_ext. intros a. apply slist_shift. Qed.

(** The force of an instantiated box. *)
Lemma sinst_force σ ss T :
  sinst_ty σ (sinst_ty (slist ss) T) =
  sinst_ty (slist (sinst σ <$> ss)) (sinst_ty (Nat.iter (length ss) sty_up σ) T).
Proof.
  rewrite !sinst_ty_sinst. apply sinst_ext_mut. intros a. unfold compose.
  destruct (decide (a < length ss)) as [Ha|Ha].
  - rewrite iter_sty_up_lt by done. cbn [sinst]. unfold slist. rewrite list_lookup_fmap.
    destruct (ss !! a) eqn:E; [done|]. apply lookup_ge_None in E. lia.
  - replace a with (length ss + (a - length ss)) by lia.
    rewrite iter_sty_up_ge, slist_shift. simpl.
    rewrite <-(length_fmap (sinst σ) ss) at 2. by rewrite sinst_slist_shift.
Qed.
