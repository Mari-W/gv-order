(** * The ends of a typed term (stage S7, decision Q15)

    [typed_tfacts]: a term typed by the merged judgment mentions exactly
    the ends of Θ, every free variable has an entry in Δ, and every
    entry that is not unlimited occurs. [fends_ground] then computes the
    ends of a grounded instance: those of Θ and those of the values the
    grounding puts in. E-Abs and E-Box need it to show the
    closure or box they build exact, as Q15 asks of [Vfuel].

    These are lemmas about derivations and terms. No relation reads
    them. *)

From GV Require Export static.Weakening.

(** ** Occurrence facts *)

Definition vfacts (Δ : lenv) (P : nat → Prop) : Prop :=
  (∀ x, P x → ∃ σ, Δ !! x = Some (Some σ)) ∧
  (∀ x U, Δ !! x = Some (Some U) → ¬ unlimited U → P x).

Definition tfacts (Θ : tenv) (Δ : lenv) (e : expr) : Prop :=
  fends e = dom Θ ∧ vfacts Δ (λ x, freevar x e).

Lemma vfacts_under o Δ P : vfacts (o :: Δ) P → vfacts Δ (λ x, P (S x)).
Proof. intros [H1 H2]. split; [intros x Hx; apply (H1 (S x) Hx)|intros x U Hx; apply (H2 (S x) U Hx)]. Qed.

Lemma vfacts_under2 o1 o2 Δ P : vfacts (o1 :: o2 :: Δ) P → vfacts Δ (λ x, P (S (S x))).
Proof. intros H. by apply vfacts_under, vfacts_under in H. Qed.

Lemma lenv_split_inv Δ Δ1 Δ2 x σ :
  lenv_split Δ Δ1 Δ2 → Δ !! x = Some (Some σ) → Δ1 !! x = Some (Some σ) ∨ Δ2 !! x = Some (Some σ).
Proof.
  intros Hs. revert x. induction Hs; intros [|x] Hx; simpl in *; try done; try (by left); try (by right); auto.
Qed.

Lemma vfacts_split Δ Δ1 Δ2 P1 P2 :
  lenv_split Δ Δ1 Δ2 → vfacts Δ1 P1 → vfacts Δ2 P2 → vfacts Δ (λ x, P1 x ∨ P2 x).
Proof.
  intros Hs [A1 B1] [A2 B2]. split.
  - intros x [Hx|Hx]; [destruct (A1 x Hx) as [σ Hσ]|destruct (A2 x Hx) as [σ Hσ]]; exists σ;
      [by eapply lenv_split_sub_l|by eapply lenv_split_sub_r].
  - intros x U Hx Hu. destruct (lenv_split_inv _ _ _ _ _ Hs Hx) as [H|H]; [left|right]; eauto.
Qed.

(** [lsame Δ Δ']: every entry of Δ' has one in Δ, and every entry of Δ
    that is not unlimited has one in Δ' that is not unlimited. Capture,
    aging, point instantiation and weakening relate the contexts of a
    rule and of its premise this way. *)
Definition lsame (Δ Δ' : lenv) : Prop :=
  ∀ x, (∀ σ, Δ' !! x = Some (Some σ) → ∃ σ0, Δ !! x = Some (Some σ0)) ∧
       (∀ U, Δ !! x = Some (Some U) → ¬ unlimited U →
          ∃ U', Δ' !! x = Some (Some U') ∧ ¬ unlimited U').

Lemma vfacts_lsame Δ Δ' P : lsame Δ Δ' → vfacts Δ' P → vfacts Δ P.
Proof.
  intros Hs [A B]. split.
  - intros x Hx. destruct (A x Hx) as [σ Hσ]. exact (proj1 (Hs x) σ Hσ).
  - intros x U Hx Hu. destruct (proj2 (Hs x) U Hx Hu) as (U' & Hx' & Hu'). eauto.
Qed.

Lemma lsame_cons o o' Δ Δ' :
  (∀ σ, o' = Some σ → ∃ σ0, o = Some σ0) →
  (∀ U, o = Some U → ¬ unlimited U → ∃ U', o' = Some U' ∧ ¬ unlimited U') →
  lsame Δ Δ' → lsame (o :: Δ) (o' :: Δ').
Proof.
  intros H1 H2 Hs [|x]; simpl; [|apply Hs]. split.
  - intros σ [= Hσ]. destruct (H1 σ Hσ) as [σ0 ->]. eauto.
  - intros U [= Ho] Hu. destruct (H2 U Ho Hu) as (U' & -> & Hu'). eauto.
Qed.

Lemma lsame_nil : lsame [] [].
Proof. intros x. split; intros; rewrite lookup_nil in *; done. Qed.

Lemma tage_unl c T T' : tage c T T' → unlimited T' ↔ unlimited T.
Proof. inversion 1; subst; done. Qed.

Lemma lage_lsame c Δ Δ' : lage c Δ Δ' → lsame Δ Δ'.
Proof.
  induction 1 as [|Δ Δ' _ IH|T T' Δ Δ' Hc _ IH]; [apply lsame_nil| |].
  - apply lsame_cons; [done|done|done].
  - apply lsame_cons; [eauto|intros U [= ->] Hu; exists T'; split; [done|]|done].
    by rewrite (tage_unl _ _ _ Hc).
Qed.

Lemma lsame_pinst σ Δ : lsame Δ (lenv_pinst σ Δ).
Proof.
  intros x. rewrite lenv_pinst_lookup. split.
  - intros σ' H. destruct (Δ !! x) as [[T|]|]; simpl in H; try done. eauto.
  - intros U Hx Hu. rewrite Hx. simpl. exists (pinst_ty σ U). split; [done|].
    by rewrite unlimited_pinst_iff.
Qed.

Lemma lsame_pinst_insert σ Δ i T lb m C T0 :
  Δ !! i = Some (Some (TEx lb m C T0)) → ¬ unlimited T →
  lsame Δ (<[i := Some T]> (lenv_pinst σ Δ)).
Proof.
  intros Hi Hu x. destruct (decide (x = i)) as [->|Hne].
  - rewrite list_lookup_insert_eq; [|unfold lenv_pinst; rewrite length_fmap; by eapply lookup_lt_Some].
    split; [eauto|]. intros U _ _. eauto.
  - rewrite list_lookup_insert_ne by done. apply lsame_pinst.
Qed.

(** ** Renaming of variables *)

(** ** The facts of a derivation *)

Lemma vfacts_or Δ P Q : vfacts Δ P → vfacts Δ Q → vfacts Δ (λ x, P x ∨ Q x).
Proof. intros [A1 B1] [A2 B2]. split; [intros x [H|H]; eauto|intros; left; eauto]. Qed.

Lemma vfacts_empty Δ : lenv_unl Δ → vfacts Δ (λ _, False).
Proof.
  intros H. split; [done|]. intros x U Hx Hu.
  destruct (H _ (list_elem_of_lookup_2 _ _ _ Hx)) as [?|(U' & [= <-] & ?)]; done.
Qed.

Lemma vfacts_only Δ x σ : lenv_only Δ x σ → vfacts Δ (λ y, y = x).
Proof.
  intros [Hx H]. split; [intros y ->; eauto|]. intros y U Hy Hu.
  destruct (decide (y = x)) as [->|Hne]; [done|]. by destruct (Hu (H y _ Hne Hy)).
Qed.

Lemma thage_dom c Θ Θ' : thage c Θ Θ' → dom Θ' = dom Θ.
Proof.
  intros H. apply set_eq. intros o. rewrite !elem_of_dom. specialize (H o).
  destruct (Θ !! o), (Θ' !! o); naive_solver.
Qed.

Lemma tsplit_dom Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → dom Θ = dom Θ1 ∪ dom Θ2.
Proof. intros [_ ->]. apply dom_union_L. Qed.

Lemma hcontractive_end : hcontractive SEnd.
Proof. intros [|n]; done. Qed.

Lemma sinsts_end N k : sinsts N (repeat SEnd k).
Proof.
  split; [|intros _]; induction k; simpl; constructor; auto; apply hcontractive_end.
Qed.

Theorem typed_tfacts W N Θ Γ Δ F e T c t : typed W N Θ Γ Δ F e T c t → tfacts Θ Δ e.
Proof.
  induction 1; unfold tfacts in *; simpl; destruct_and?.
  all: try match goal with H : tsplit _ _ _ |- _ => rewrite (tsplit_dom _ _ _ H) end.
  all: try match goal with H : thage _ _ _ |- _ => rewrite <-(thage_dom _ _ _ H) end.
  - split; [by rewrite dom_empty_L|by apply vfacts_empty].
  - split; [by rewrite dom_empty_L|by eapply vfacts_only].
  - split; [by rewrite dom_singleton_L|by apply vfacts_empty].
  - (* e_abs *)
    split; [done|].
    eapply vfacts_lsame; [by eapply lage_lsame|]. by eapply (vfacts_under _ _ (λ x, freevar x _)).
  - (* e_app *)
    split; [congruence|]. eapply vfacts_split; [done|done|].
    eapply vfacts_lsame; [by eapply lage_lsame|done].
  - (* e_pair *)
    split; [congruence|]. eapply vfacts_split; [done|done|].
    eapply vfacts_lsame; [by eapply lage_lsame|done].
  - (* e_letu *)
    split; [congruence|]. eapply vfacts_split; [done|done|].
    eapply vfacts_lsame; [by eapply lage_lsame|done].
  - (* e_letp *)
    split; [congruence|]. eapply vfacts_split; [done|done|].
    eapply vfacts_lsame; [by eapply lage_lsame|]. by eapply (vfacts_under2 _ _ _ (λ x, freevar x _)).
  - split; done.
  - (* e_case *)
    split; [set_solver|]. eapply vfacts_split; [done|done|].
    eapply vfacts_lsame; [by eapply lage_lsame|].
    apply vfacts_or; by eapply (vfacts_under _ _ (λ x, freevar x _)).
  - (* e_box *)
    match goal with H : ∀ ss, length ss = ?k → _ → _ |- _ =>
      destruct (H (repeat SEnd k) (repeat_length _ _) (sinsts_end _ _)) as [Hf Hv] end.
    split; [done|]. eapply (vfacts_under _ _ (λ x, freevar x _)). eapply vfacts_lsame; [apply lsame_pinst|exact Hv].
  - split; done.
  - split; done.
  - split; done.
  - split; done.
  - split; done.
  - split; done.
  - split; done.
  - split; done.
  - split; [by rewrite dom_empty_L|by apply vfacts_empty].
  - split; done.
  - split; done.
  - split; done.
  - (* e_open *)
    split; [unfold tenv_pinst in *; by rewrite <-dom_fmap_L with (f := tentry_pinst (pshift m))|].
    eapply vfacts_lsame; [by eapply lsame_pinst_insert|done].
Qed.

(** ** The ends of a grounded instance *)

Lemma upP_of (P Q : nat → Prop) : (∀ x, Q (S x) → P x) → ∀ x, Q x → upP P x.
Proof. intros H [|x] Hx; simpl; auto. Qed.

Lemma allfv_of_freevar e : ∀ (P : nat → Prop), (∀ x, freevar x e → P x) → allfv P e.
Proof.
  induction e; intros P H; simpl in *.
  - by apply H.
  - done.
  - done.
  - apply IHe. apply (upP_of _ (λ y, freevar y e)). intros x Hx. by apply H.
  - split; [apply IHe1|apply IHe2]; intros x Hx; apply H; tauto.
  - split; [apply IHe1|apply IHe2]; intros x Hx; apply H; tauto.
  - split; [apply IHe1|apply IHe2]; intros x Hx; apply H; tauto.
  - split; [apply IHe1; intros x Hx; apply H; tauto|].
    apply IHe2. apply (upP_of _ (λ y, freevar y e2)). apply (upP_of _ (λ y, freevar (S y) e2)).
    intros x Hx. apply H. tauto.
  - by apply IHe.
  - split_and!; [apply IHe1; intros x Hx; apply H; tauto| |].
    + apply IHe2. apply (upP_of _ (λ y, freevar y e2)). intros x Hx. apply H. tauto.
    + apply IHe3. apply (upP_of _ (λ y, freevar y e3)). intros x Hx. apply H. tauto.
  - apply IHe. apply (upP_of _ (λ y, freevar y e)). intros x Hx. by apply H.
  - done.
  - by apply IHe.
Qed.

Lemma fends_subst_eq e γ (D : gset cend) :
  (∀ x, freevar x e → fends (γ x) ⊆ D) → (∀ o, o ∈ D → ∃ x, freevar x e ∧ o ∈ fends (γ x)) →
  fends (subst γ e) = fends e ∪ D.
Proof.
  intros H1 H2. apply set_eq. intros o. split.
  - intros Ho. by apply (fends_subst e γ D (allfv_of_freevar e _ H1)).
  - intros [Ho|Ho]%elem_of_union; [by apply fends_subst_super|].
    destruct (H2 o Ho) as (x & Hx & Ho'). by apply (fends_subst_free e x γ).
Qed.

Lemma freevar_emap (g : cend → cend) e : ∀ x, freevar x (emap g e) ↔ freevar x e.
Proof. induction e; intros y; simpl; rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; done. Qed.
