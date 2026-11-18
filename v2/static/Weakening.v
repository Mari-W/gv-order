(** * Weakening (stage S2)

    Two structural lemmas of the judgment [typed].

    - [typed_wext]: a derivation at W is a derivation at every extension
      W ⊑ W'. Every fact the judgment reads is monotone in W. E-New reads
      the laws of W, and an existential may drop facts of its constraint,
      so E-New at W' followed by E-Sub gives the type at W.
    - [typed_rename]: a renaming of term variables that moves every entry
      of Δ to an entry of Δ' with the same type. Linear entries move
      injectively, unlimited entries may merge and keep their type at any
      credit, and Δ' may carry extra unlimited entries. Weakening by an
      absent entry at any position ([typed_insert_none]), at the head
      ([typed_weaken_head]), exchange and contraction are instances. *)

From GV Require Export static.Conservativity.

(** ** Monotonicity in the world *)

Section wext.
  Context (W W' : world) (HW : W ⊑ W').

  Lemma fl_wext Γ a b : fl W Γ a b → fl W' Γ a b.
  Proof.
    induction 1.
    - apply fl_w. by eapply w_lt_mono.
    - by apply fl_h.
    - by apply fl_v.
    - by eapply fl_trans.
  Qed.

  Lemma slt_wext Γ x y : slt W Γ x y → slt W' Γ x y.
  Proof. apply fl_wext. Qed.

  Lemma sle_wext Γ x y : sle W Γ x y → sle W' Γ x y.
  Proof. intros [->|H]; [by left|right; by apply slt_wext]. Qed.

  Lemma hold_at_wext Γ C xs : hold_at W Γ C xs → hold_at W' Γ C xs.
  Proof. intros H x y Hf. by apply slt_wext, H. Qed.

  Lemma ub_below_s_wext Γ ub F : ub_below_s W Γ ub F → ub_below_s W' Γ ub F.
  Proof.
    destruct ub; simpl; [|done]. intros (H1 & H2 & H3). split_and!; [| |done].
    - intros y Hy. by apply slt_wext, H1.
    - intros φ Hφ. by apply fl_wext, H2.
  Qed.

  Lemma lb_below_hb_wext Γ lb H b : lb_below_hb W Γ lb H b → lb_below_hb W' Γ lb H b.
  Proof.
    unfold lb_below_hb, lb_below_h. destruct b; [done|].
    destruct lb; [|done]. intros Hy y Hyy. by apply sle_wext, Hy.
  Qed.

  Lemma lbx_below_h_wext Γ lb H b : lbx_below_h W Γ lb H b → lbx_below_h W' Γ lb H b.
  Proof.
    destruct lb; simpl; try done. intros [Hy Hb]. split; [|done].
    intros y Hyy. by apply sle_wext, Hy.
  Qed.
End wext.

Theorem typed_wext W W' N Θ Γ Δ F e T a c t :
  W ⊑ W' → typed W N Θ Γ Δ F e T a c t → typed W' N Θ Γ Δ F e T a c t.
Proof.
  intros HW. induction 1.
  - by apply e_unit.
  - by eapply e_var.
  - by apply e_chan.
  - eapply e_abs; eauto using lb_below_hb_wext.
  - eapply e_app; eauto using ub_below_s_wext.
  - eapply e_pair; eauto.
  - eapply e_letu; eauto.
  - eapply e_letp; eauto.
  - by eapply e_inj1.
  - by eapply e_inj2.
  - eapply e_case; eauto.
  - eapply e_box; eauto.
  - eapply e_force; eauto using hold_at_wext, ub_below_s_wext.
  - eapply e_send; eauto using slt_wext, ub_below_s_wext.
  - eapply e_recv; eauto using ub_below_s_wext.
  - eapply e_close; eauto using ub_below_s_wext.
  - eapply e_select; eauto using slt_wext, ub_below_s_wext.
  - eapply e_branch; eauto using slt_wext, ub_below_s_wext.
  - eapply e_link; eauto.
  - eapply e_spawn_lam; eauto.
  - eapply e_spawn; eauto.
  - eapply e_sub; [eapply e_new; [done|by apply (wext_fams _ _ HW)]| |apply fle_refl|apply tle_refl].
    apply sub_ex; [done| |apply teq_refl|apply fle_refl].
    intros g Hg. simpl in *. by apply (wext_laws _ _ HW).
  - eapply e_new_at; eauto.
  - eapply e_sub; eauto.
  - eapply e_weak; eauto.
  - eapply e_contract; eauto.
  - eapply e_pack; eauto using hold_at_wext, lbx_below_h_wext.
  - eapply e_open; eauto.
Qed.

(** ** Renaming of term variables *)

Global Instance unlimited_dec T : Decision (unlimited T).
Proof. destruct T; simpl; apply _. Defined.

Lemma unlimited_heads T : unlimited T → heads T = ∅.
Proof. by destruct T. Qed.

Lemma unlimited_hbot T : unlimited T → hbot T = false.
Proof. by destruct T. Qed.

(** [lren r Δ Δ']: the renaming r moves every entry of Δ to an entry of
    Δ' with the same type. A linear entry keeps its credit and is the
    only entry of Δ that r moves there. An unlimited entry may land at
    any credit, and Δ' may hold unlimited entries nobody moves there. *)
Definition lren (r : nat → nat) (Δ Δ' : lenv) : Prop :=
  (∀ x T a, Δ !! x = Some (Some (T, a)) → unlimited T →
     ∃ a', Δ' !! r x = Some (Some (T, a'))) ∧
  (∀ x T a, Δ !! x = Some (Some (T, a)) → ¬ unlimited T →
     Δ' !! r x = Some (Some (T, a))) ∧
  (∀ y T a, Δ' !! y = Some (Some (T, a)) → ¬ unlimited T →
     ∃ x, r x = y ∧ Δ !! x = Some (Some (T, a)) ∧
       ∀ x' σ, Δ !! x' = Some (Some σ) → r x' = y → x' = x).

(** *** Heads and the ⊥ flag of a context, entry by entry *)

Lemma lenv_heads_lookup Δ y :
  y ∈ lenv_heads Δ ↔ ∃ x T a, Δ !! x = Some (Some (T, a)) ∧ y ∈ heads T.
Proof.
  induction Δ as [|[[T a]|] Δ IH]; simpl.
  - split; [set_solver|]. by intros (x & T & a & H & _).
  - rewrite elem_of_union, IH. split.
    + intros [Hy|(x & T' & a' & Hx & Hy)]; [by exists 0, T, a|by exists (S x), T', a'].
    + intros ([|x] & T' & a' & Hx & Hy); simpl in Hx; [injection Hx as -> ->; by left|right; eauto].
  - rewrite IH. split.
    + intros (x & T & a & Hx & Hy). by exists (S x), T, a.
    + intros ([|x] & T & a & Hx & Hy); simpl in Hx; [done|eauto].
Qed.

Lemma lenv_bot_lookup Δ :
  lenv_bot Δ = true ↔ ∃ x T a, Δ !! x = Some (Some (T, a)) ∧ hbot T = true.
Proof.
  induction Δ as [|[[T a]|] Δ IH]; simpl.
  - split; [done|]. by intros (x & T & a & H & _).
  - rewrite orb_true_iff, IH. split.
    + intros [Hy|(x & T' & a' & Hx & Hy)]; [by exists 0, T, a|by exists (S x), T', a'].
    + intros ([|x] & T' & a' & Hx & Hy); simpl in Hx; [injection Hx as -> ->; by left|right; eauto].
  - rewrite IH. split.
    + intros (x & T & a & Hx & Hy). by exists (S x), T, a.
    + intros ([|x] & T & a & Hx & Hy); simpl in Hx; [done|eauto].
Qed.

Lemma lren_heads r Δ Δ' : lren r Δ Δ' → lenv_heads Δ' = lenv_heads Δ.
Proof.
  intros (H1 & H2 & H3). apply set_eq. intros y. rewrite !lenv_heads_lookup. split.
  - intros (y0 & T & a & Hy0 & Hy). destruct (decide (unlimited T)) as [Hu|Hu].
    + rewrite unlimited_heads in Hy by done. set_solver.
    + destruct (H3 _ _ _ Hy0 Hu) as (x & _ & Hx & _). by exists x, T, a.
  - intros (x & T & a & Hx & Hy). destruct (decide (unlimited T)) as [Hu|Hu].
    + destruct (H1 _ _ _ Hx Hu) as [a' Ha']. exists (r x), T, a'. done.
    + exists (r x), T, a. split; [by apply H2|done].
Qed.

Lemma lren_bot r Δ Δ' : lren r Δ Δ' → lenv_bot Δ' = lenv_bot Δ.
Proof.
  intros (H1 & H2 & H3). apply Bool.eq_iff_eq_true. rewrite !lenv_bot_lookup. split.
  - intros (y0 & T & a & Hy0 & Hy). destruct (decide (unlimited T)) as [Hu|Hu].
    + by rewrite unlimited_hbot in Hy.
    + destruct (H3 _ _ _ Hy0 Hu) as (x & _ & Hx & _). by exists x, T, a.
  - intros (x & T & a & Hx & Hy). destruct (decide (unlimited T)) as [Hu|Hu].
    + destruct (H1 _ _ _ Hx Hu) as [a' Ha']. exists (r x), T, a'. done.
    + exists (r x), T, a. split; [by apply H2|done].
Qed.

(** *** The preimage of a linear entry *)

Definition pre (r : nat → nat) (Δ : lenv) (y : nat) : option nat :=
  snd <$> list_find (λ x, r x = y ∧ is_Some (mjoin (Δ !! x))) (seq 0 (length Δ)).

Lemma pre_spec r Δ y x : pre r Δ y = Some x → r x = y ∧ ∃ σ, Δ !! x = Some (Some σ).
Proof.
  unfold pre. destruct (list_find _ _) as [[i z]|] eqn:E; simpl; [|done]. intros [= <-].
  apply list_find_Some in E as (Hz & [Hr [σ Hσ]] & _).
  split; [done|]. exists σ. destruct (Δ !! z) as [[]|]; simpl in Hσ; congruence.
Qed.

Lemma pre_some r Δ y x σ :
  Δ !! x = Some (Some σ) → r x = y →
  (∀ x' σ', Δ !! x' = Some (Some σ') → r x' = y → x' = x) → pre r Δ y = Some x.
Proof.
  intros Hx Hr Hu. destruct (pre r Δ y) as [z|] eqn:E.
  - apply pre_spec in E as [Hz [σ' Hσ']]. f_equal. by eapply Hu.
  - exfalso. unfold pre in E.
    destruct (list_find_elem_of (λ x, r x = y ∧ is_Some (mjoin (Δ !! x))) (seq 0 (length Δ)) x)
      as [p Hp].
    + apply elem_of_seq. apply lookup_lt_Some in Hx. lia.
    + split; [done|]. rewrite Hx. by eexists.
    + rewrite Hp in E. done.
Qed.

(** The preimage of a linear entry of Δ'. *)
Lemma lren_pre r Δ Δ' y T a :
  lren r Δ Δ' → Δ' !! y = Some (Some (T, a)) → ¬ unlimited T →
  ∃ x, pre r Δ y = Some x ∧ r x = y ∧ Δ !! x = Some (Some (T, a)) ∧
    ∀ x' σ, Δ !! x' = Some (Some σ) → r x' = y → x' = x.
Proof.
  intros (_ & _ & H3) Hy Hu. destruct (H3 _ _ _ Hy Hu) as (x & Hr & Hx & Hun).
  exists x. split_and!; try done. by eapply pre_some.
Qed.

(** *** Pointwise relations *)

Definition orel (R : ty * fuel → ty * fuel → Prop) (o o' : option (ty * fuel)) : Prop :=
  match o, o' with None, None => True | Some σ, Some σ' => R σ σ' | _, _ => False end.

Lemma lage_Forall2 c Δ Δ' : lage c Δ Δ' ↔ Forall2 (orel (tage c)) Δ Δ'.
Proof.
  split.
  - induction 1; constructor; simpl; auto.
  - induction 1 as [|o o' Δ Δ' Ho _ IH]; [constructor|].
    destruct o, o'; simpl in Ho; try done; constructor; auto.
Qed.

Lemma lcap_Forall2 h a Δ Δ' : lcap h a Δ Δ' ↔ Forall2 (orel (tcap h a)) Δ Δ'.
Proof.
  split.
  - induction 1; constructor; simpl; auto.
  - induction 1 as [|o o' Δ Δ' Ho _ IH]; [constructor|].
    destruct o, o'; simpl in Ho; try done; constructor; auto.
Qed.

Lemma Forall2_orel_l R Δ Δ2 x σ :
  Forall2 (orel R) Δ Δ2 → Δ !! x = Some (Some σ) → ∃ σ2, Δ2 !! x = Some (Some σ2) ∧ R σ σ2.
Proof.
  intros HF Hx. destruct (Forall2_lookup_l _ _ _ _ _ HF Hx) as ([σ2|] & H & HR); [eauto|done].
Qed.

Lemma Forall2_orel_r R Δ Δ2 x σ2 :
  Forall2 (orel R) Δ Δ2 → Δ2 !! x = Some (Some σ2) → ∃ σ, Δ !! x = Some (Some σ) ∧ R σ σ2.
Proof.
  intros HF Hx. destruct (Forall2_lookup_r _ _ _ _ _ HF Hx) as ([σ|] & H & HR); [eauto|done].
Qed.

(** A pointwise relation on entries that keeps unlimited entries and
    linearity carries along a renaming. Aging and capture are two. *)
Lemma lren_rel (R : ty * fuel → ty * fuel → Prop) r Δ Δ2 Δr :
  (∀ U a, unlimited U → R (U, a) (U, a)) →
  (∀ T a T' a', R (T, a) (T', a') → unlimited T → T' = T) →
  (∀ T a T' a', R (T, a) (T', a') → unlimited T' → unlimited T) →
  Forall2 (orel R) Δ Δ2 → lren r Δ Δr →
  ∃ Δr', Forall2 (orel R) Δr Δr' ∧ lren r Δ2 Δr'.
Proof.
  intros HR1 HR2 HR3 HF Hr.
  set (f := λ (y : nat) (o : option (ty * fuel)),
    match o with
    | Some (T, a) => if decide (unlimited T) then o else
        match pre r Δ y with Some x => mjoin (Δ2 !! x) | None => o end
    | None => None
    end).
  exists (imap f Δr). split.
  - apply Forall2_lookup. intros y. rewrite list_lookup_imap.
    destruct (Δr !! y) as [o|] eqn:Ey; simpl; constructor.
    destruct o as [[T a]|]; simpl; [|done].
    case_decide as Hu; [by apply HR1|].
    destruct (lren_pre _ _ _ _ _ _ Hr Ey Hu) as (x & -> & _ & Hx & _).
    destruct (Forall2_orel_l _ _ _ _ _ HF Hx) as (σ2 & -> & HR). done.
  - destruct Hr as (H1 & H2 & H3). split_and!.
    + intros x T' a' Hx Hu'. destruct (Forall2_orel_r _ _ _ _ _ HF Hx) as ([T a] & Hx0 & HR).
      pose proof (HR3 _ _ _ _ HR Hu') as Hu. pose proof (HR2 _ _ _ _ HR Hu) as ->.
      destruct (H1 _ _ _ Hx0 Hu) as [a'' Ha''].
      exists a''. rewrite list_lookup_imap, Ha''. simpl. by rewrite decide_True.
    + intros x T' a' Hx Hu'. destruct (Forall2_orel_r _ _ _ _ _ HF Hx) as ([T a] & Hx0 & HR).
      assert (¬ unlimited T) as Hu.
      { intros Hu. apply Hu'. by rewrite (HR2 _ _ _ _ HR Hu). }
      pose proof (H2 _ _ _ Hx0 Hu) as Hy.
      destruct (lren_pre r Δ Δr _ _ _ (conj H1 (conj H2 H3)) Hy Hu) as (x0 & Hp & Hrx & Hx1 & Hun).
      assert (x0 = x) as -> by (symmetry; by eapply Hun).
      rewrite list_lookup_imap, Hy. simpl. rewrite decide_False by done. by rewrite Hp, Hx.
    + intros y T' a' Hy Hu'. rewrite list_lookup_imap in Hy.
      destruct (Δr !! y) as [[[T a]|]|] eqn:Ey; simpl in Hy; try done.
      case_decide as Hu; [by simplify_eq|].
      destruct (lren_pre r Δ Δr _ _ _ (conj H1 (conj H2 H3)) Ey Hu) as (x & Hp & Hrx & Hx & Hun).
      rewrite Hp in Hy. exists x. split_and!; [done| |].
      * by destruct (Δ2 !! x) as [[]|]; simpl in Hy; simplify_eq.
      * intros x' σ Hx' Hrx'. destruct (Forall2_orel_r _ _ _ _ _ HF Hx') as (σ0 & Hx0' & _).
        by eapply Hun.
Qed.

Lemma tage_unl c T a T' a' : tage c (T, a) (T', a') → unlimited T → T' = T.
Proof. inversion 1; subst; simpl; done. Qed.

Lemma tage_unl_r c T a T' a' : tage c (T, a) (T', a') → unlimited T' → unlimited T.
Proof. inversion 1; subst; simpl; done. Qed.

Lemma tcap_unl h b T a T' a' : tcap h b (T, a) (T', a') → unlimited T → T' = T.
Proof. inversion 1; subst; simpl; done. Qed.

Lemma tcap_unl_r h b T a T' a' : tcap h b (T, a) (T', a') → unlimited T' → unlimited T.
Proof. inversion 1; subst; simpl; done. Qed.

Lemma lren_lage c r Δ Δ2 Δr :
  lage c Δ Δ2 → lren r Δ Δr → ∃ Δr', lage c Δr Δr' ∧ lren r Δ2 Δr'.
Proof.
  intros HF Hr. apply lage_Forall2 in HF.
  destruct (lren_rel (tage c) r Δ Δ2 Δr) as (Δr' & ? & ?); try done.
  - intros U a HU. by apply age_free, unlimited_tfree.
  - apply tage_unl.
  - apply tage_unl_r.
  - exists Δr'. by rewrite lage_Forall2.
Qed.

Lemma lren_lcap h b r Δ Δ2 Δr :
  lcap h b Δ Δ2 → lren r Δ Δr → ∃ Δr', lcap h b Δr Δr' ∧ lren r Δ2 Δr'.
Proof.
  intros HF Hr. apply lcap_Forall2 in HF.
  destruct (lren_rel (tcap h b) r Δ Δ2 Δr) as (Δr' & ? & ?); try done.
  - intros U a HU. by apply cap_free, unlimited_tfree.
  - apply tcap_unl.
  - apply tcap_unl_r.
  - exists Δr'. by rewrite lcap_Forall2.
Qed.

(** *** Splits *)

Definition ssplit (o o1 o2 : option (ty * fuel)) : Prop :=
  match o, o1, o2 with
  | None, None, None => True
  | Some σ, Some σ1, None => σ1 = σ
  | Some σ, None, Some σ2 => σ2 = σ
  | Some σ, Some σ1, Some σ2 => σ1 = σ ∧ σ2 = σ ∧ unlimited σ.1
  | _, _, _ => False
  end.

Lemma lenv_split_lookup Δ Δ1 Δ2 :
  lenv_split Δ Δ1 Δ2 ↔
    length Δ1 = length Δ ∧ length Δ2 = length Δ ∧
    ∀ i o o1 o2, Δ !! i = Some o → Δ1 !! i = Some o1 → Δ2 !! i = Some o2 → ssplit o o1 o2.
Proof.
  split.
  - induction 1 as [|? ? ? _ (IH1 & IH2 & IH)|? ? ? ? _ (IH1 & IH2 & IH)|? ? ? ? _ (IH1 & IH2 & IH)
                   |? ? ? ? ? HU _ (IH1 & IH2 & IH)]; simpl; split_and!; try lia; try done.
    all: intros [|i] o o1 o2 Ho Ho1 Ho2; simpl in *; [simplify_eq/=; try done|eauto].
  - revert Δ1 Δ2. induction Δ as [|o Δ IH]; intros [|o1 Δ1] [|o2 Δ2] (Hl1 & Hl2 & H);
      simpl in *; try lia; [constructor|].
    pose proof (H 0 o o1 o2 eq_refl eq_refl eq_refl) as H0.
    assert (lenv_split Δ Δ1 Δ2) as IH' by (apply IH; split_and!; [lia|lia|]; intros i; apply (H (S i))).
    destruct o as [σ|], o1 as [σ1|], o2 as [σ2|]; simpl in H0; try done.
    + destruct H0 as (-> & -> & HU). destruct σ. by constructor.
    + subst. by constructor.
    + subst. by constructor.
    + by constructor.
Qed.

Lemma lenv_split_sub_l Δ Δ1 Δ2 x σ :
  lenv_split Δ Δ1 Δ2 → Δ1 !! x = Some (Some σ) → Δ !! x = Some (Some σ).
Proof.
  intros (Hl1 & Hl2 & H)%lenv_split_lookup Hx.
  destruct (lookup_lt_is_Some_2 Δ x) as [o Ho]; [apply lookup_lt_Some in Hx; lia|].
  destruct (lookup_lt_is_Some_2 Δ2 x) as [o2 Ho2]; [apply lookup_lt_Some in Hx; lia|].
  specialize (H x o (Some σ) o2 Ho Hx Ho2). destruct o, o2; simpl in H; naive_solver.
Qed.

Lemma lenv_split_sub_r Δ Δ1 Δ2 x σ :
  lenv_split Δ Δ1 Δ2 → Δ2 !! x = Some (Some σ) → Δ !! x = Some (Some σ).
Proof.
  intros (Hl1 & Hl2 & H)%lenv_split_lookup Hx.
  destruct (lookup_lt_is_Some_2 Δ x) as [o Ho]; [apply lookup_lt_Some in Hx; lia|].
  destruct (lookup_lt_is_Some_2 Δ1 x) as [o1 Ho1]; [apply lookup_lt_Some in Hx; lia|].
  specialize (H x o o1 (Some σ) Ho Ho1 Hx). destruct o, o1; simpl in H; naive_solver.
Qed.

(** The part of Δ' that comes from Δi ⊆ Δ, plus every unlimited entry. *)
Definition lsel (r : nat → nat) (Δ Δi Δ' : lenv) : lenv :=
  imap (λ y o,
    match o with
    | Some (T, a) => if decide (unlimited T) then o else
        match pre r Δ y with
        | Some x => if decide (is_Some (mjoin (Δi !! x))) then o else None
        | None => None
        end
    | None => None
    end) Δ'.

Lemma lsel_lren r Δ Δi Δ' :
  (∀ x σ, Δi !! x = Some (Some σ) → Δ !! x = Some (Some σ)) →
  lren r Δ Δ' → lren r Δi (lsel r Δ Δi Δ').
Proof.
  intros Hsub Hr. pose proof Hr as (H1 & H2 & H3). unfold lsel. split_and!.
  - intros x T a Hx Hu. destruct (H1 _ _ _ (Hsub _ _ Hx) Hu) as [a' Ha'].
    exists a'. rewrite list_lookup_imap, Ha'. simpl. by rewrite decide_True.
  - intros x T a Hx Hu. pose proof (H2 _ _ _ (Hsub _ _ Hx) Hu) as Hy.
    destruct (lren_pre _ _ _ _ _ _ Hr Hy Hu) as (x0 & Hp & _ & _ & Hun).
    assert (x0 = x) as -> by (symmetry; eapply Hun; [apply Hsub, Hx|done]).
    rewrite list_lookup_imap, Hy. simpl. rewrite decide_False, Hp by done.
    rewrite decide_True; [done|]. rewrite Hx. by eexists.
  - intros y T a Hy Hu. rewrite list_lookup_imap in Hy.
    destruct (Δ' !! y) as [[[T0 a0]|]|] eqn:Ey; simpl in Hy; try done.
    case_decide as Hu0; [by simplify_eq|].
    destruct (lren_pre _ _ _ _ _ _ Hr Ey Hu0) as (x & Hp & Hrx & Hx & Hun).
    rewrite Hp in Hy. case_decide as Hs; [|done]. simplify_eq.
    exists x. split_and!; [done| |].
    + destruct (Δi !! x) as [[σ|]|] eqn:Ei; simpl in Hs; try by destruct Hs.
      apply Hsub in Ei. congruence.
    + intros x' σ Hx' Hrx'. eapply Hun; [apply Hsub, Hx'|done].
Qed.

Lemma lren_split r Δ Δ1 Δ2 Δ' :
  lenv_split Δ Δ1 Δ2 → lren r Δ Δ' →
  ∃ Δ1' Δ2', lenv_split Δ' Δ1' Δ2' ∧ lren r Δ1 Δ1' ∧ lren r Δ2 Δ2'.
Proof.
  intros Hs Hr. exists (lsel r Δ Δ1 Δ'), (lsel r Δ Δ2 Δ'). split_and!.
  - apply lenv_split_lookup. unfold lsel. rewrite !length_imap. split_and!; [done|done|].
    intros y o o1 o2 Ho Ho1 Ho2. rewrite list_lookup_imap, Ho in Ho1, Ho2. simpl in Ho1, Ho2.
    destruct o as [[T a]|]; [|by simplify_eq].
    case_decide as Hu; [simplify_eq; simpl; done|].
    destruct (lren_pre _ _ _ _ _ _ Hr Ho Hu) as (x & Hp & _ & Hx & _). rewrite Hp in Ho1, Ho2.
    apply lenv_split_lookup in Hs as (Hl1 & Hl2 & Hs).
    destruct (lookup_lt_is_Some_2 Δ1 x) as [p1 Hp1]; [apply lookup_lt_Some in Hx; lia|].
    destruct (lookup_lt_is_Some_2 Δ2 x) as [p2 Hp2]; [apply lookup_lt_Some in Hx; lia|].
    specialize (Hs x _ _ _ Hx Hp1 Hp2). rewrite Hp1 in Ho1. rewrite Hp2 in Ho2.
    destruct p1, p2; simpl in Hs; try done; [destruct Hs as (_ & _ & ?); done| |].
    all: revert Ho1 Ho2; simpl; repeat case_decide; intros; simplify_eq/=; try done.
    all: repeat match goal with
           | H : ¬ is_Some (Some _) |- _ => destruct H; by eexists
           | H : is_Some None |- _ => by destruct H
           end.
  - apply lsel_lren; [|done]. intros x σ Hx. by eapply lenv_split_sub_l.
  - apply lsel_lren; [|done]. intros x σ Hx. by eapply lenv_split_sub_r.
Qed.

(** *** Weakening, emptiness, unlimited contexts *)

Lemma lenv_wk_intro Δ0 Δ :
  length Δ0 = length Δ →
  (∀ x o0 o, Δ0 !! x = Some o0 → Δ !! x = Some o →
     o0 = o ∨ (o0 = None ∧ ∃ U a, o = Some (U, a) ∧ unlimited U)) →
  lenv_wk Δ0 Δ.
Proof.
  revert Δ0. induction Δ as [|o Δ IH]; intros [|o0 Δ0] Hl H; simpl in *; try lia; [constructor|].
  assert (lenv_wk Δ0 Δ) by (apply IH; [lia|]; intros x; apply (H (S x))).
  destruct (H 0 o0 o eq_refl eq_refl) as [->|(-> & U & a & -> & HU)]; by constructor.
Qed.

Lemma lenv_wk_sub Δ0 Δ x σ : lenv_wk Δ0 Δ → Δ0 !! x = Some (Some σ) → Δ !! x = Some (Some σ).
Proof.
  intros H. revert x. induction H as [|o Δ0 Δ _ IH|U a Δ0 Δ _ _ IH]; intros [|x] Hx; simpl in *; auto.
  done.
Qed.

Lemma lenv_wk_lin Δ0 Δ x T a :
  lenv_wk Δ0 Δ → Δ !! x = Some (Some (T, a)) → ¬ unlimited T → Δ0 !! x = Some (Some (T, a)).
Proof.
  intros H. revert x. induction H as [|o Δ0 Δ _ IH|U b Δ0 Δ HU _ IH]; intros [|x] Hx Hu; simpl in *; auto.
  simplify_eq. done.
Qed.

Lemma lren_wk r Δ0 Δ Δ' : lenv_wk Δ0 Δ → lren r Δ Δ' → lren r Δ0 Δ'.
Proof.
  intros Hw (H1 & H2 & H3). split_and!.
  - intros x T a Hx. apply (H1 x T a). by eapply lenv_wk_sub.
  - intros x T a Hx. apply (H2 x T a). by eapply lenv_wk_sub.
  - intros y T a Hy Hu. destruct (H3 _ _ _ Hy Hu) as (x & Hrx & Hx & Hun).
    exists x. split_and!; [done|by eapply lenv_wk_lin|].
    intros x' σ Hx'. apply Hun with σ. by eapply lenv_wk_sub.
Qed.

(** Δ' with every entry absent: Δ' weakens to it when its only entries
    are unlimited. *)
Lemma lren_empty r Δ Δ' :
  lenv_empty Δ → lren r Δ Δ' →
  lenv_wk ((λ _ : option (ty * fuel), None) <$> Δ') Δ' ∧
  lenv_empty ((λ _ : option (ty * fuel), None) <$> Δ').
Proof.
  intros He (_ & _ & H3). split.
  - apply lenv_wk_intro; [by rewrite length_fmap|].
    intros x o0 o Ho0 Ho. rewrite list_lookup_fmap, Ho in Ho0. simpl in Ho0. simplify_eq.
    destruct o as [[T a]|]; [|by left]. right. split; [done|].
    destruct (decide (unlimited T)) as [Hu|Hu]; [eauto|].
    destruct (H3 _ _ _ Ho Hu) as (x' & _ & Hx' & _).
    by apply list_elem_of_lookup_2, He in Hx'.
  - intros o Ho. apply list_elem_of_fmap in Ho as (? & -> & _). done.
Qed.

Lemma lren_unl r Δ Δ' : lenv_unl Δ → lren r Δ Δ' → lenv_unl Δ'.
Proof.
  intros Hu (_ & _ & H3) o Ho. apply list_elem_of_lookup_1 in Ho as [y Hy].
  destruct o as [[T a]|]; [|by left]. right. exists T, a. split; [done|].
  destruct (decide (unlimited T)) as [?|HT]; [done|].
  destruct (H3 _ _ _ Hy HT) as (x & _ & Hx & _).
  apply list_elem_of_lookup_2, Hu in Hx as [?|(U & b & ? & ?)]; simplify_eq; done.
Qed.

(** *** Binders, instantiation, update, contraction *)

Lemma lren_up r o Δ Δ' : lren r Δ Δ' → lren (upren r) (o :: Δ) (o :: Δ').
Proof.
  intros (H1 & H2 & H3). split_and!.
  - intros [|x] T a Hx Hu; simpl in *; [simplify_eq; by eexists|]. by eapply H1.
  - intros [|x] T a Hx Hu; simpl in *; [done|]. by apply H2.
  - intros [|y] T a Hy Hu; simpl in *.
    + exists 0. split_and!; [done|done|]. intros [|x'] σ _ Hx'; [done|]. done.
    + destruct (H3 _ _ _ Hy Hu) as (x & Hrx & Hx & Hun). exists (S x).
      split_and!; [simpl; unfold compose; by rewrite Hrx|done|].
      intros [|x'] σ Hx' Hrx'; [done|]. simpl in Hrx'. unfold compose in Hrx'.
      f_equal. eapply Hun; [done|lia].
Qed.

Lemma lenv_pinst_lookup σ Δ x :
  lenv_pinst σ Δ !! x = fmap (M:=option) (λ '(T, a), (pinst_ty σ T, a)) <$> Δ !! x.
Proof. unfold lenv_pinst. by rewrite list_lookup_fmap. Qed.

Lemma unlimited_pinst_iff σ T : unlimited (pinst_ty σ T) ↔ unlimited T.
Proof. by destruct T. Qed.

Lemma lren_pinst σ r Δ Δ' : lren r Δ Δ' → lren r (lenv_pinst σ Δ) (lenv_pinst σ Δ').
Proof.
  intros (H1 & H2 & H3). split_and!.
  - intros x T a Hx Hu. rewrite lenv_pinst_lookup in Hx.
    destruct (Δ !! x) as [[[T0 a0]|]|] eqn:E; simplify_eq/=.
    apply unlimited_pinst_iff in Hu. destruct (H1 _ _ _ E Hu) as [a' Ha'].
    exists a'. by rewrite lenv_pinst_lookup, Ha'.
  - intros x T a Hx Hu. rewrite lenv_pinst_lookup in Hx.
    destruct (Δ !! x) as [[[T0 a0]|]|] eqn:E; simplify_eq/=.
    rewrite unlimited_pinst_iff in Hu. by rewrite lenv_pinst_lookup, (H2 _ _ _ E Hu).
  - intros y T a Hy Hu. rewrite lenv_pinst_lookup in Hy.
    destruct (Δ' !! y) as [[[T0 a0]|]|] eqn:E; simplify_eq/=.
    rewrite unlimited_pinst_iff in Hu. destruct (H3 _ _ _ E Hu) as (x & Hrx & Hx & Hun).
    exists x. split_and!; [done|by rewrite lenv_pinst_lookup, Hx|].
    intros x' σ' Hx'. rewrite lenv_pinst_lookup in Hx'.
    destruct (Δ !! x') as [[[]|]|] eqn:E'; simplify_eq/=. by eapply Hun.
Qed.

Lemma lren_insert r Δ Δ' i T0 a0 T b :
  lren r Δ Δ' → Δ !! i = Some (Some (T0, a0)) → ¬ unlimited T0 → ¬ unlimited T →
  lren r (<[i := Some (T, b)]> Δ) (<[r i := Some (T, b)]> Δ').
Proof.
  intros Hr Hi Hu0 Hu. pose proof Hr as (H1 & H2 & H3).
  pose proof (H2 _ _ _ Hi Hu0) as Hri.
  destruct (lren_pre _ _ _ _ _ _ Hr Hri Hu0) as (x0 & _ & _ & _ & Hun).
  assert (x0 = i) as -> by (symmetry; by eapply Hun).
  assert (i < length Δ) by (by apply lookup_lt_Some in Hi).
  assert (r i < length Δ') by (by apply lookup_lt_Some in Hri).
  split_and!.
  - intros x T' a' Hx Hu'. destruct (decide (x = i)) as [->|Hne].
    + rewrite list_lookup_insert_eq in Hx by done. simplify_eq. by destruct Hu.
    + rewrite list_lookup_insert_ne in Hx by done.
      destruct (H1 _ _ _ Hx Hu') as [a'' Ha'']. exists a''.
      rewrite list_lookup_insert_ne; [done|]. intros Heq. apply Hne. by eapply Hun.
  - intros x T' a' Hx Hu'. destruct (decide (x = i)) as [->|Hne].
    + rewrite list_lookup_insert_eq in Hx by done. simplify_eq.
      by rewrite list_lookup_insert_eq.
    + rewrite list_lookup_insert_ne in Hx by done.
      rewrite list_lookup_insert_ne; [by apply H2|]. intros Heq. apply Hne. by eapply Hun.
  - intros y T' a' Hy Hu'. destruct (decide (y = r i)) as [->|Hne].
    + rewrite list_lookup_insert_eq in Hy by done. simplify_eq.
      exists i. split_and!; [done|by rewrite list_lookup_insert_eq|].
      intros x' σ Hx' Hrx'. destruct (decide (x' = i)) as [->|Hne']; [done|].
      rewrite list_lookup_insert_ne in Hx' by done. by eapply Hun.
    + rewrite list_lookup_insert_ne in Hy by done.
      destruct (H3 _ _ _ Hy Hu') as (x & Hrx & Hx & Hun').
      assert (x ≠ i) by (intros ->; done).
      exists x. split_and!; [done|by rewrite list_lookup_insert_ne|].
      intros x' σ Hx' Hrx'. destruct (decide (x' = i)) as [->|Hne']; [done|].
      rewrite list_lookup_insert_ne in Hx' by done. by eapply Hun'.
Qed.

Lemma lren_contract r U aU Δ Δ' :
  unlimited U → lren r (Some (U, aU) :: Δ) Δ' →
  lren (λ x, r (pred x)) (Some (U, aU) :: Some (U, aU) :: Δ) Δ'.
Proof.
  intros HU (H1 & H2 & H3). split_and!.
  - intros [|[|x]] T a Hx Hu; simpl in *; [by eapply (H1 0)|by eapply (H1 0)|by eapply (H1 (S x))].
  - intros [|[|x]] T a Hx Hu; simpl in *; [simplify_eq; by destruct Hu|simplify_eq; by destruct Hu|by apply (H2 (S x))].
  - intros y T a Hy Hu. destruct (H3 _ _ _ Hy Hu) as ([|x] & Hrx & Hx & Hun); simpl in Hx.
    + simplify_eq. by destruct Hu.
    + exists (S (S x)). split_and!; [done|done|].
      intros [|[|x']] σ Hx' Hrx'; simpl in *.
      * exfalso. by pose proof (Hun 0 _ eq_refl Hrx').
      * exfalso. by pose proof (Hun 0 _ eq_refl Hrx').
      * f_equal. by pose proof (Hun (S x') _ Hx' Hrx') as [= ->].
Qed.

(** An injective renaming into a context that holds the same entries at
    the image and nothing elsewhere. *)
Lemma lren_inj r Δ Δ' :
  (∀ x, Δ' !! r x = Δ !! x) → (∀ x x', r x = r x' → x = x') →
  (∀ y σ, Δ' !! y = Some (Some σ) → ∃ x, r x = y) → lren r Δ Δ'.
Proof.
  intros Hl Hi Hp. split_and!.
  - intros x T a Hx _. exists a. by rewrite Hl.
  - intros x T a Hx _. by rewrite Hl.
  - intros y T a Hy _. destruct (Hp _ _ Hy) as [x <-]. exists x.
    split_and!; [done|by rewrite <-Hl|]. intros x' σ _ Hx'. by apply Hi.
Qed.

Lemma lren_refl Δ : lren id Δ Δ.
Proof. apply lren_inj; [done|done|]. intros y _ _. by exists y. Qed.

(** The shift past a new variable at position i. *)
Definition shift_at (i : nat) : nat → nat := λ x, if decide (x < i) then x else S x.

Lemma upren_shift_at i x : upren (shift_at i) x = shift_at (S i) x.
Proof.
  unfold shift_at, upren, scons, compose. destruct x as [|x];
    repeat destruct (decide _); simpl in *; lia.
Qed.

Lemma shift_at_0 x : shift_at 0 x = S x.
Proof. unfold shift_at. by rewrite decide_False by lia. Qed.

Definition linsert (i : nat) (Δ : lenv) : lenv := take i Δ ++ None :: drop i Δ.

Lemma lren_linsert i Δ : i ≤ length Δ → lren (shift_at i) Δ (linsert i Δ).
Proof.
  intros Hi. assert (length (take i Δ) = i) as Ht by (rewrite length_take; lia).
  apply lren_inj.
  - intros x. unfold shift_at, linsert. case_decide.
    + rewrite lookup_app_l by lia. by rewrite lookup_take_lt by lia.
    + rewrite lookup_app_r by lia. replace (S x - length (take i Δ)) with (S (x - i)) by lia.
      simpl. rewrite lookup_drop. f_equal. lia.
  - intros x x'. unfold shift_at. repeat case_decide; lia.
  - intros y σ Hy. unfold linsert in Hy.
    destruct (decide (y < i)).
    + exists y. unfold shift_at. by rewrite decide_True.
    + destruct (decide (y = i)) as [->|].
      * rewrite lookup_app_r in Hy by lia. by rewrite Ht, Nat.sub_diag in Hy.
      * exists (pred y). unfold shift_at. rewrite decide_False by lia. lia.
Qed.

Lemma linsert_0 Δ : linsert 0 Δ = None :: Δ.
Proof. done. Qed.

(** *** The renaming lemma *)

Lemma tsub_unl_credit T a a' : unlimited T → tsub T a T a'.
Proof.
  destruct T; try done. intros _. apply sub_box; [apply fle_refl|apply tle_refl|].
  destruct k; [apply teq_refl|done].
Qed.

Local Ltac ren_split Hr :=
  match goal with
  | Hs0 : lenv_split _ _ _, Ha0 : lage _ _ _ |- _ =>
      destruct (lren_split _ _ _ _ _ Hs0 Hr) as (Δ1r & Δ2r & Hs & Hr1 & Hr2);
      destruct (lren_lage _ _ _ _ _ Ha0 Hr2) as (Δ2r' & Ha & Hr2')
  end.

Theorem typed_rename W N Θ Γ Δ F e T a c t :
  typed W N Θ Γ Δ F e T a c t →
  ∀ r Δ', lren r Δ Δ' → typed W N Θ Γ Δ' F (rename r e) T a c t.
Proof.
  induction 1; intros r Δr Hr; simpl.
  - destruct (lren_empty _ _ _ H Hr) as [Hw He]. eapply e_weak; [exact Hw|]. by apply e_unit.
  - (* E-Var *)
    destruct H as [Hx Hun]. pose proof Hr as (H1 & H2 & H3).
    set (Δk := imap (λ z o, if decide (z = r x) then o else None) Δr).
    assert (∀ σ, Δr !! r x = Some (Some σ) → lenv_wk Δk Δr ∧ lenv_only Δk (r x) σ) as Hk.
    { intros σ Hσ. unfold Δk. split.
      - apply lenv_wk_intro; [by rewrite length_imap|].
        intros z o0 o Ho0 Ho. rewrite list_lookup_imap, Ho in Ho0. simpl in Ho0.
        case_decide as Hz; simplify_eq; [by left|]. destruct o as [[U b]|]; [|by left]. right.
        split; [done|]. destruct (decide (unlimited U)) as [HU|HU]; [eauto|].
        destruct (H3 _ _ _ Ho HU) as (x' & Hrx' & Hx' & _).
        destruct (Hun _ _ Hx') as [-> _]. done.
      - split; [rewrite list_lookup_imap, Hσ; simpl; case_decide; done|].
        intros y σ' Hy. rewrite list_lookup_imap in Hy.
        destruct (Δr !! y) eqn:Ey; simpl in Hy; [|done].
        case_decide; simplify_eq; split; [done|congruence]. }
    destruct (decide (unlimited T)) as [HU|HU].
    + destruct (H1 _ _ _ Hx HU) as [a' Ha']. destruct (Hk _ Ha') as [Hw Ho].
      eapply e_weak; [exact Hw|]. eapply e_sub; [by eapply e_var|by apply tsub_unl_credit
                                                 |apply fle_refl|apply tle_refl].
    + destruct (Hk _ (H2 _ _ _ Hx HU)) as [Hw Ho].
      eapply e_weak; [exact Hw|]. by eapply e_var.
  - destruct (lren_empty _ _ _ H Hr) as [Hw He]. eapply e_weak; [exact Hw|]. by apply e_chan.
  - (* E-Abs *)
    destruct (lren_lcap _ _ _ _ _ _ H2 Hr) as (Δhr & Hc & Hr').
    eapply e_abs; [done| |done|exact Hc|].
    + by rewrite (lren_heads _ _ _ Hr), (lren_bot _ _ _ Hr).
    + by apply IHtyped, lren_up.
  - (* E-App *)
    ren_split Hr.
    eapply e_app; [done|exact Hs|done| |done|exact Ha| |done|done|done].
    + rewrite (lren_heads _ _ _ Hr2), (lren_bot _ _ _ Hr2). by apply IHtyped1.
    + by apply IHtyped2.
  - ren_split Hr.
    eapply e_pair; [done|exact Hs| |done|exact Ha| |done|done].
    + rewrite (lren_heads _ _ _ Hr2), (lren_bot _ _ _ Hr2). by apply IHtyped1.
    + by apply IHtyped2.
  - ren_split Hr.
    eapply e_letu; [done|exact Hs| |done|exact Ha| |done].
    + rewrite (lren_heads _ _ _ Hr2), (lren_bot _ _ _ Hr2). by apply IHtyped1.
    + by apply IHtyped2.
  - ren_split Hr.
    eapply e_letp; [done|exact Hs| |done|exact Ha| |done].
    + rewrite (lren_heads _ _ _ Hr2), (lren_bot _ _ _ Hr2). by apply IHtyped1.
    + by apply IHtyped2, lren_up, lren_up.
  - by eapply e_inj1, IHtyped.
  - by eapply e_inj2, IHtyped.
  - ren_split Hr.
    eapply e_case; [done|exact Hs| |done|exact Ha| | |done].
    + rewrite (lren_heads _ _ _ Hr2), (lren_bot _ _ _ Hr2). by apply IHtyped1.
    + by apply IHtyped2, lren_up.
    + by apply IHtyped3, lren_up.
  - (* E-Box *)
    eapply e_box; [by eapply lren_unl|done|].
    intros ss Hk Hss. apply H2; [done|done|]. by apply lren_pinst, lren_up.
  - eapply e_force; eauto.
  - eapply e_send; eauto.
  - eapply e_recv; eauto.
  - eapply e_close; eauto.
  - eapply e_select; eauto.
  - eapply e_branch; eauto.
  - eapply e_link; eauto.
  - destruct (lren_lage _ _ _ _ _ H0 Hr) as (Δr' & Ha & Hr').
    eapply e_spawn_lam; [done|exact Ha|]. by apply IHtyped, lren_up.
  - eapply e_spawn; eauto.
  - destruct (lren_empty _ _ _ H Hr) as [Hw He]. eapply e_weak; [exact Hw|]. by apply e_new.
  - eapply e_new_at; eauto.
  - eapply e_sub; eauto.
  - apply IHtyped. by eapply lren_wk.
  - (* E-Contract *)
    rewrite rename_rename. by apply IHtyped, lren_contract.
  - eapply e_pack; eauto.
  - (* E-Open *)
    pose proof Hr as (_ & Hl2 & _). pose proof (Hl2 _ _ _ H ltac:(simpl; tauto)) as Hri.
    eapply e_open; [exact Hri|done|]. apply IHtyped.
    eapply (lren_insert _ _ _ _ (pinst_ty (pshift m) (TEx lb m C T aT)) a);
      [by apply lren_pinst| |simpl; tauto|done].
    by rewrite lenv_pinst_lookup, H.
Qed.

(** Weakening by an absent entry at position i. *)
Corollary typed_insert_none W N Θ Γ Δ F e T a c t i :
  i ≤ length Δ → typed W N Θ Γ Δ F e T a c t →
  typed W N Θ Γ (linsert i Δ) F (rename (shift_at i) e) T a c t.
Proof. intros Hi H. by eapply typed_rename, lren_linsert. Qed.

Corollary typed_weaken_head W N Θ Γ Δ F e T a c t :
  typed W N Θ Γ Δ F e T a c t → typed W N Θ Γ (None :: Δ) F (rename S e) T a c t.
Proof.
  intros H. eapply typed_rename; [exact H|]. apply lren_inj; [done|by intros ?? [=]|].
  intros [|y] σ Hy; [done|]. by exists y.
Qed.

(** *** Renaming in the deadlock-freedom projection *)

Lemma lren_df r Δ Δ' : lren r Δ Δ' → lren r (lenv_df Δ) (lenv_df Δ').
Proof.
  intros (H1 & H2 & H3). split_and!.
  - intros x T a. rewrite !lenv_df_lookup. intros Hx Hu.
    destruct (Δ !! x) as [[[T0 a0]|]|] eqn:E; unfold ent_df in *; simplify_eq/=.
    rewrite unlimited_df in Hu. destruct (H1 _ _ _ E Hu) as [a' Ha']. rewrite Ha'. by eexists.
  - intros x T a. rewrite !lenv_df_lookup. intros Hx Hu.
    destruct (Δ !! x) as [[[T0 a0]|]|] eqn:E; unfold ent_df in *; simplify_eq/=.
    rewrite unlimited_df in Hu. by rewrite (H2 _ _ _ E Hu).
  - intros y T a. rewrite lenv_df_lookup. intros Hy Hu.
    destruct (Δ' !! y) as [[[T0 a0]|]|] eqn:E; unfold ent_df in *; simplify_eq/=.
    rewrite unlimited_df in Hu. destruct (H3 _ _ _ E Hu) as (x & Hrx & Hx & Hun).
    exists x. rewrite !lenv_df_lookup, Hx. split_and!; [done|done|].
    intros x' σ Hx' Hr'. rewrite lenv_df_lookup in Hx'. destruct (Δ !! x') as [[σ0|]|] eqn:E'; unfold ent_df in *; simplify_eq/=; eapply Hun; eauto.
Qed.

Theorem dftyped_rename W Θ Γ Δ F e T :
  dftyped W Θ Γ Δ F e T →
  ∀ r Δ', lren r Δ Δ' → dftyped W Θ Γ Δ' F (rename r e) T.
Proof. intros H r Δ' Hr. eapply typed_rename; [exact H|]. by apply lren_df. Qed.

Corollary dftyped_weaken_head W Θ Γ Δ F e T :
  dftyped W Θ Γ Δ F e T → dftyped W Θ Γ (None :: Δ) F (rename S e) T.
Proof.
  intros H. eapply dftyped_rename; [exact H|]. apply lren_inj; [done|by intros ?? [=]|].
  intros [|y] σ Hy; [done|]. by exists y.
Qed.

(** *** let x = e1 in e2 is admissible

    [ELet] is ⟨e1, ∗⟩ split by LetP, then u matched by LetU. E-Pair
    gives e1 the whole context and ∗ none, aging by 0 leaves every
    entry as it is, and E-LetU consumes u. Costs and transformers come
    out as fadd c1 c2 and tseq t1 t2 up to the units 0 and [tid]. *)

Section let_admissible.
  Local Abbreviation lnone Δ := ((λ _ : option (ty * fuel), None) <$> Δ).

  Local Lemma lsplit_all Δ : lenv_split Δ Δ (lnone Δ).
  Proof. induction Δ as [|[σ|] Δ IH]; simpl; constructor; done. Qed.
  Local Lemma lsplit_allr Δ : lenv_split Δ (lnone Δ) Δ.
  Proof. induction Δ as [|[σ|] Δ IH]; simpl; constructor; done. Qed.
  Local Lemma lempty_lnone Δ : lenv_empty (lnone Δ).
  Proof. intros o Ho. by apply list_elem_of_fmap in Ho as (? & -> & _). Qed.
  Local Lemma lnone_lookup (Δ : lenv) (y : nat) (σ : ty * fuel) : lnone Δ !! y = Some (Some σ) → False.
  Proof. revert y. induction Δ as [|o Δ IH]; intros [|y]; simpl; [done|done|congruence|apply IH]. Qed.
  Local Lemma lnone_lookup_S o (Δ : lenv) (y : nat) (σ : ty * fuel) :
    (o :: lnone Δ) !! S y = Some (Some σ) → False.
  Proof. apply lnone_lookup. Qed.
  Local Lemma lheads_lnone Δ : lenv_heads (lnone Δ) = ∅.
  Proof. by induction Δ. Qed.
  Local Lemma lbot_lnone Δ : lenv_bot (lnone Δ) = false.
  Proof. by induction Δ. Qed.
  Local Lemma lage_lnone c Δ : lage c (lnone Δ) (lnone Δ).
  Proof. induction Δ; simpl; constructor; done. Qed.
  Local Lemma fsub_0 a : fsub a (Some 0) = a.
  Proof. destruct a as [[|m]|]; done. Qed.
  Local Lemma fle_0 a : fle (Some 0) a.
  Proof. destruct a; simpl; lia. Qed.
  Local Lemma tage_0 σ : tage (Some 0) σ σ.
  Proof. destruct σ as [T a]. rewrite <-(fsub_0 a) at 2. apply age_credit, fle_0. Qed.
  Local Lemma lage_0 Δ : lage (Some 0) Δ Δ.
  Proof. induction Δ as [|[σ|] Δ IH]; constructor; auto using tage_0. Qed.
  Local Lemma thage_0 Θ : thage (Some 0) Θ Θ.
  Proof.
    intros o. destruct (Θ !! o) as [[S x a]|]; [|done]. simpl. split_and!; [done|done|apply fle_0|by rewrite fsub_0].
  Qed.
  Local Lemma thage_nil c : thage c ∅ ∅.
  Proof. intros o. by rewrite lookup_empty. Qed.
  Local Lemma tsplit_l Θ : tsplit Θ Θ ∅.
  Proof. split; [apply map_disjoint_empty_r|by rewrite map_union_empty]. Qed.
  Local Lemma tsplit_r Θ : tsplit Θ ∅ Θ.
  Proof. split; [apply map_disjoint_empty_l|by rewrite map_empty_union]. Qed.
  Local Lemma fadd_0_r a : fadd a (Some 0) = a.
  Proof. destruct a as [m|]; [simpl; by rewrite Nat.add_0_r|done]. Qed.
  Local Lemma tseq_tid_r t : tseq t tid = t.
  Proof. destruct t as [[s|] [b|]]; unfold tseq, tid, fmul; simpl; rewrite ?Nat.add_0_r, ?Nat.mul_0_r; done. Qed.
  Local Lemma tseq_tid_l t : tseq tid t = t.
  Proof. destruct t as [[s|] [b|]]; unfold tseq, tid, fmul; simpl; rewrite ?Nat.add_0_r; done. Qed.
  Local Lemma sf_union_nil F : sf_unionb F (tenv_heads ∅ ∪ ∅) false = F.
  Proof.
    destruct F as [X o]. unfold sf_unionb, sf_union. simpl. f_equal.
    apply set_eq. intros y. rewrite elem_of_union, elem_of_union, elem_of_tenv_heads.
    setoid_rewrite lookup_empty. set_solver.
  Qed.

  (** E-Let *)
  Lemma e_let W N Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 a1 T aT c1 t1 c2 t2 :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 a1 c1 t1 →
    thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
    typed W N Θ2' Γ (Some (T1, a1) :: Δ2') F e2 T aT c2 t2 →
    tok t1 t2 →
    typed W N Θ Γ Δ F (ELet e1 e2) T aT (fadd c1 c2) (tseq t1 t2).
  Proof.
    intros Hs Hl H1 Ht Ha H2 Hok. unfold ELet.
    enough (typed W N Θ Γ Δ F (LetP (Pair e1 EUnit) (LetU (Var 0) (rename S e2))) T aT
              (fadd (fadd c1 (Some 0)) (fadd (Some 0) c2)) (tseq (tseq t1 tid) (tseq tid t2))) as H.
    { by rewrite fadd_0_r, fadd_0_l, tseq_tid_r, tseq_tid_l in H. }
    eapply e_letp; [exact Hs|exact Hl| |by rewrite fadd_0_r|by rewrite fadd_0_r| |].
    - eapply e_pair; [apply tsplit_l|apply lsplit_all| |apply thage_nil|apply lage_lnone| |apply tage_0|].
      + by rewrite lheads_lnone, lbot_lnone, sf_union_nil.
      + apply e_unit, lempty_lnone.
      + left. done.
    - rewrite (fadd_0_l a1).
      eapply e_letu; [apply tsplit_r|apply lsplit_l, lsplit_allr| |apply thage_0|apply lage_0| |].
      + apply e_var. split; [done|]. intros y σ' Hy. destruct y.
        * simpl in Hy. by simplify_eq.
        * by destruct (lnone_lookup_S _ _ _ _ Hy).
      + simpl. by apply typed_weaken_head.
      + right. left. done.
    - rewrite tseq_tid_r, tseq_tid_l. exact Hok.
  Qed.

  (** D-Let *)
  Lemma d_let W Θ Θ1 Θ2 Γ Δ Δ1 Δ2 F e1 e2 T1 b1 T :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    dftyped W Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 →
    dftyped W Θ2 Γ (Some (T1, b1) :: Δ2) F e2 T →
    dftyped W Θ Γ Δ F (ELet e1 e2) T.
  Proof.
    intros Hs Hl H1 H2. unfold ELet.
    eapply (d_letp _ _ _ _ _ _ _ _ _ _ _ T1 b1 TUnit None b1 None);
      [exact Hs|exact Hl| |].
    - eapply d_pair; [apply tsplit_l|apply lsplit_all| |].
      + by rewrite lheads_lnone, lbot_lnone, sf_union_nil.
      + apply d_unit, lempty_lnone.
    - eapply d_letu; [apply tsplit_r|apply lsplit_l, lsplit_allr| |].
      + eapply (d_var _ _ _ _ _ _ None). split; [done|]. intros y σ' Hy. destruct y.
        * simpl in Hy. by simplify_eq.
        * by destruct (lnone_lookup_S _ _ _ _ Hy).
      + by apply dftyped_weaken_head.
  Qed.
End let_admissible.
