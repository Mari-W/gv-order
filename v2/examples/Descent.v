(** * A box cannot descend in its own schema (fx-descent, 2026-11-23)

    Proposition 7 of docs/redesign/check-general-new.md and the
    rejection of rx-chain (docs/explorer, example rx-chain).

    - [descent]: a property of points in ranked worlds that always
      reappears at a lower point of an extension holds nowhere. The
      proof is well-founded induction on the rank of a ranked point and
      on the offset of an unranked one, without excluded middle.
    - [prop7]: Proposition 7 in its general form. A box body typed
      under Γb = [hc_open m H Γ0] reaches a context Γc that every model
      of Γb extends to, and there forces the box at an instance xs′
      with H at xs′ and f(xs′) ≺ f(ιs). Then W, Γ0 and H have no common
      ranked model. [prop7_new] discharges the extension for a creation
      at a fresh root under (gen-new), with excluded middle
      ([gen_new_ext]), and [prop7_fld] for a field creation.
    - [rx_chain_rejected]: rx-chain has no typing at any finite N, in
      any context that has a ranked model. [rx_chain_proc_rejected]:
      the process of its one thread is not in the lock-free judgment.
    - [fjr_lf_rejected], [fjr_lf_proc_rejected]: the same for the
      recursive fork-join worker of examples/ForkJoin.v, which
      [fjr_dftyped] types at N = ∞.

    The four rejections take excluded middle, as the lock-free
    fundamental theorem does, because a creation under (gen-new) takes
    it ([gen_new_ext]). They read every derivation. A value of a
    variable is read through its points only ([pval], [PV]): the point
    of an end, the witnesses of an existential with its lower bound,
    and the constraint and parameter of a box. E-Sub, E-Pack and E-Open
    keep [PV] ([PV_tsub], [PV_pack], [spo_sem]), so the argument holds
    whatever existentials the derivation packs or opens, at a fresh
    root or at a field. One round of the box body, read at a model of
    its context ([box_enter]), creates c at a point q, closes c while
    it holds w at s, which asks q ≺ s̄ ([close_PV]), and spawns a child
    that forces the box at an instance where its constraint holds and
    its parameter is the end c′ at q̄ ([child_step]). So the dual of the
    point of the parameter falls in every round ([rc_step], [fj_step]),
    and [descent] applies ([box_P_never]). *)

From GV Require Export static.Inversion examples.Tools static.FundamentalProc.
From GV Require Import static.Skeleton examples.ForkJoin.

(** ** Values read through their points *)

Inductive pval :=
  | PU
  | PF
  | PE (p : point)
  | PP (a b : pval)
  | PI (i : bool) (a : pval)
  | PBox (m : nat) (C : bcs) (U : ty).

(** The heads of a value, the duals of the points of its ends. *)
Fixpoint vheads (v : pval) : gset point :=
  match v with
  | PE p => {[p‾]}
  | PP a b => vheads a ∪ vheads b
  | PI _ a => vheads a
  | _ => ∅
  end.

Definition lb_ok (R : world) (lb : lbound) (v : pval) : Prop :=
  match lb with
  | LBot => True
  | LNone => vheads v = ∅
  | LPt l => ∀ y, y ∈ vheads v → w_le R l y
  end.

(** A type with every session type, cost, credit and ticket erased. *)
Fixpoint erase (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb _ T1 U _ => TLolli ub lb None (erase T1) (erase U) None
  | TProd T1 U => TProd (erase T1) (erase U)
  | TSum T1 U => TSum (erase T1) (erase U)
  | TBox n k C ub _ U => TBox n k C ub None (erase U)
  | TSess _ x _ _ => TSess SEnd x None None
  | TEx lb n C T1 => TEx lb n C (erase T1)
  end.

Fixpoint PV (R : world) (σ : nat → point) (T : ty) (v : pval) : Prop :=
  match T with
  | TUnit => v = PU
  | TLolli _ _ _ _ _ _ => v = PF
  | TProd T1 U => ∃ a b, v = PP a b ∧ PV R σ T1 a ∧ PV R σ U b
  | TSum T1 U => ∃ (i : bool) a, v = PI i a ∧ ((i = false ∧ PV R σ T1 a) ∨ (i = true ∧ PV R σ U a))
  | TBox n _ C _ _ U => v = PBox n (bcs_inst σ C) (erase (pinst_ty (pup n σ) U))
  | TSess _ x _ _ => v = PE (pt_inst σ x)
  | TEx lb n C T1 => ∃ xs, length xs = n ∧ wholds R (bcs_inst σ C) xs ∧
      lb_ok R (lb_map (pt_inst σ) lb) v ∧ PV R (pclose xs n σ) T1 v
  end.

(** The parameter of an arrow. *)
Definition PVpar (R : world) (σ : nat → point) (T : ty) (v : pval) : Prop :=
  match T with TLolli _ _ _ T1 _ _ => PV R σ T1 v | _ => False end.

Definition PΔ (R : world) (σ : nat → point) (Δ : lenv) (γ : nat → pval) : Prop :=
  ∀ i T, Δ !! i = Some (Some T) → PV R σ T (γ i).

(** The value of a box variable. *)
Definition bden (σ : nat → point) (T : ty) : pval :=
  match T with
  | TBox n _ C _ _ U => PBox n (bcs_inst σ C) (erase (pinst_ty (pup n σ) U))
  | _ => PU
  end.

Definition lden (σ : nat → point) (Δ : lenv) : nat → pval :=
  λ j, match Δ !! j with Some (Some T) => bden σ T | _ => PU end.

Lemma pbox_inj m C U m' C' U' : PBox m C U = PBox m' C' U' → m = m' ∧ C = C' ∧ U = U'.
Proof. intros H. by injection H. Qed.

(** ** Erasure *)

Lemma erase_pinst T : ∀ σ, erase (pinst_ty σ T) = pinst_ty σ (erase T).
Proof. induction T; intros σ; simpl; by rewrite ?IHT1, ?IHT2, ?IHT. Qed.

Lemma erase_sinst T : ∀ s, erase (sinst_ty s T) = erase T.
Proof. induction T; intros s; simpl; by rewrite ?IHT1, ?IHT2, ?IHT. Qed.

Lemma erase_idem T : erase (erase T) = erase T.
Proof. induction T; simpl; by rewrite ?IHT1, ?IHT2, ?IHT. Qed.

Lemma eqT_erase ρ T : ∀ U, eqT ρ T U → erase T = erase U.
Proof.
  induction T; intros [] H; simpl in *; try done.
  - destruct H as (-> & -> & -> & -> & H1 & H2). by rewrite (IHT1 _ H1), (IHT2 _ H2).
  - destruct H as [H1 H2]. by rewrite (IHT1 _ H1), (IHT2 _ H2).
  - destruct H as [H1 H2]. by rewrite (IHT1 _ H1), (IHT2 _ H2).
  - destruct H as (-> & -> & -> & -> & -> & H). destruct k0; [by rewrite (IHT _ H)|by subst].
  - by destruct H as (-> & _).
  - destruct H as (-> & -> & -> & H). by rewrite (IHT _ H).
Qed.

Lemma tage_erase c T T' : tage c T T' → erase T = erase T'.
Proof. induction 1; simpl; congruence. Qed.

(** ** The point reading of values *)

Section pv.
  Context (R : world).

  Lemma PV_ext T : ∀ σ τ v, (∀ a, σ a = τ a) → PV R σ T v ↔ PV R τ T v.
  Proof.
    induction T; intros σ τ v H; simpl; try done.
    - setoid_rewrite (IHT1 σ τ _ H). by setoid_rewrite (IHT2 σ τ _ H).
    - setoid_rewrite (IHT1 σ τ _ H). by setoid_rewrite (IHT2 σ τ _ H).
    - rewrite (bcs_inst_ext σ τ), (pinst_ty_ext _ (pup n σ) (pup n τ)); [done| |done].
      intros a. by apply pup_ext.
    - by rewrite (pt_inst_ext σ τ).
    - rewrite (bcs_inst_ext σ τ C H), (lb_map_ext (pt_inst σ) (pt_inst τ)) by (intros; by apply pt_inst_ext).
      split; intros (xs & Hl & Hw & Hb & Hv); exists xs; split_and!; try done;
        (eapply IHT; [|exact Hv]); intros a; unfold pclose; f_equal; apply pup_ext; done.
  Qed.

  Lemma pclose_pup xs m σ τ a :
    pt_inst (pclose xs m σ) (pup m τ a) = pclose xs m (λ b, pt_inst σ (τ b)) a.
  Proof.
    rewrite pclose_pt. unfold pclose. f_equal. rewrite pup_comp. apply pup_ext. done.
  Qed.

  Lemma PV_pinst T : ∀ σ τ v, PV R σ (pinst_ty τ T) v ↔ PV R (λ a, pt_inst σ (τ a)) T v.
  Proof.
    induction T; intros σ τ v; simpl; try done.
    - setoid_rewrite IHT1. by setoid_rewrite IHT2.
    - setoid_rewrite IHT1. by setoid_rewrite IHT2.
    - rewrite bcs_inst_comp, pinst_ty_comp.
      rewrite (pinst_ty_ext _ (pt_inst (pup n σ) ∘ pup n τ) (pup n (λ a, pt_inst σ (τ a)))); [done|].
      intros a. unfold compose. rewrite pup_comp. apply pup_ext. done.
    - by rewrite pt_inst_comp.
    - rewrite bcs_inst_comp, lb_map_comp.
      rewrite (lb_map_ext (pt_inst σ ∘ pt_inst τ) (pt_inst (λ a, pt_inst σ (τ a))))
        by (intros x; unfold compose; by rewrite pt_inst_comp).
      split; intros (xs & Hl & Hw & Hb & Hv); exists xs; split_and!; try done.
      + apply IHT in Hv. refine (proj1 (PV_ext T _ _ v _) Hv). intros a. cbn beta. by rewrite pclose_pup.
      + apply IHT. refine (proj1 (PV_ext T _ _ v _) Hv). intros a. cbn beta. by rewrite pclose_pup.
  Qed.

  Lemma PV_erase T : ∀ U σ v, erase T = erase U → PV R σ T v ↔ PV R σ U v.
  Proof.
    induction T; intros [] σ v H; simpl in *; try done; try discriminate.
    - injection H as H1 H2. setoid_rewrite (IHT1 _ σ _ H1). by setoid_rewrite (IHT2 _ σ _ H2).
    - injection H as H1 H2. setoid_rewrite (IHT1 _ σ _ H1). by setoid_rewrite (IHT2 _ σ _ H2).
    - injection H as -> -> -> -> HU. by rewrite !erase_pinst, HU.
    - by injection H as ->.
    - injection H as -> -> -> HT.
      split; intros (xs & ? & ? & ? & Hv); exists xs; split_and!; try done; by apply (IHT _ _ v HT).
  Qed.

  Lemma PV_sinst T s σ v : PV R σ (sinst_ty s T) v ↔ PV R σ T v.
  Proof. apply PV_erase, erase_sinst. Qed.

  Lemma PV_tage c T T' σ v : tage c T T' → PV R σ T v ↔ PV R σ T' v.
  Proof. intros H. apply PV_erase. by eapply tage_erase. Qed.

  Lemma PVpar_erase T U σ v : erase T = erase U → PVpar R σ T v ↔ PVpar R σ U v.
  Proof. destruct T, U; simpl; try done; try discriminate. intros [= _ _ H _]. by apply PV_erase. Qed.

  Lemma PVpar_pinst T σ τ v : PVpar R σ (pinst_ty τ T) v ↔ PVpar R (λ a, pt_inst σ (τ a)) T v.
  Proof. destruct T; simpl; try done. apply PV_pinst. Qed.

  Lemma PVpar_ext T σ τ v : (∀ a, σ a = τ a) → PVpar R σ T v ↔ PVpar R τ T v.
  Proof. destruct T; simpl; try done. apply PV_ext. Qed.

  Lemma PV_bden σ T : unlimited T → PV R σ T (bden σ T).
  Proof. by destruct T. Qed.

  Lemma PV_box_iff σ n k C ub c U m C' U' :
    PV R σ (TBox n k C ub c U) (PBox m C' U') ↔ m = n ∧ C' = bcs_inst σ C ∧ U' = erase (pinst_ty (pup n σ) U).
  Proof. simpl. split; [intros [= -> -> ->]|intros (-> & -> & ->)]; done. Qed.

  (** The heads of a value lie at or above the heads of its type. *)
  Lemma heads_PV T : ∀ σ v, PV R σ T v → hbot T = false →
    ∀ y, y ∈ vheads v → ∃ h, h ∈ heads T ∧ w_le R (pt_inst σ h) y.
  Proof.
    induction T; intros σ v Hv Hb y Hy; simpl in *.
    - subst. set_solver.
    - subst. set_solver.
    - destruct Hv as (a0 & b & -> & Ha & Hb'). apply orb_false_iff in Hb as [H1 H2].
      simpl in Hy. apply elem_of_union in Hy as [Hy|Hy].
      + destruct (IHT1 _ _ Ha H1 y Hy) as (h & Hh & Hle). exists h. set_solver.
      + destruct (IHT2 _ _ Hb' H2 y Hy) as (h & Hh & Hle). exists h. set_solver.
    - destruct Hv as (i & a0 & -> & [[-> Ha]|[-> Ha]]); apply orb_false_iff in Hb as [H1 H2]; simpl in Hy.
      + destruct (IHT1 _ _ Ha H1 y Hy) as (h & Hh & Hle). exists h. set_solver.
      + destruct (IHT2 _ _ Ha H2 y Hy) as (h & Hh & Hle). exists h. set_solver.
    - subst. set_solver.
    - subst. simpl in Hy. apply elem_of_singleton in Hy as ->. exists x‾. split; [set_solver|].
      left. by rewrite pt_inst_dual.
    - destruct Hv as (xs & _ & _ & Hlb & _). destruct lb as [| |l]; simpl in Hlb, Hb |- *.
      + rewrite Hlb in Hy. set_solver.
      + done.
      + exists l. split; [set_solver|]. by apply Hlb.
  Qed.

  Lemma vheads_empty T σ v : PV R σ T v → hbot T = false → heads T = ∅ → vheads v = ∅.
  Proof.
    intros Hv Hb Hh. apply set_eq. intros y. split; [|set_solver]. intros Hy.
    destruct (heads_PV T σ v Hv Hb y Hy) as (h & Hh' & _). set_solver.
  Qed.
End pv.

Lemma lb_ok_mono R R' lb v : R ⊑ R' → lb_ok R lb v → lb_ok R' lb v.
Proof. intros HR. destruct lb; simpl; try done. intros H y Hy. eapply w_le_mono; [exact HR|]. by apply H. Qed.

Lemma wholds_mono R R' C xs : R ⊑ R' → wholds R C xs → wholds R' C xs.
Proof. intros HR H x y Hf. eapply w_lt_mono; [exact HR|]. by apply H. Qed.

Lemma PV_mono R R' T : R ⊑ R' → ∀ σ v, PV R σ T v → PV R' σ T v.
Proof.
  intros HR. induction T; intros σ v; simpl; try done.
  - intros (a & b & -> & H1 & H2). eauto 10.
  - intros (i & a & -> & [[-> H]|[-> H]]); eauto 10.
  - intros (xs & Hl & Hw & Hb & Hv). exists xs. split_and!; [done|by eapply wholds_mono|by eapply lb_ok_mono|eauto].
Qed.

Lemma PΔ_mono R R' σ Δ γ : R ⊑ R' → PΔ R σ Δ γ → PΔ R' σ Δ γ.
Proof. intros HR H i T Hi. eapply PV_mono; [exact HR|]. by apply H. Qed.

Lemma PΔ_ext R σ τ Δ γ : (∀ a, σ a = τ a) → PΔ R σ Δ γ → PΔ R τ Δ γ.
Proof. intros Hs H i T Hi. apply (PV_ext R T σ τ); [done|]. by apply H. Qed.

Lemma PΔ_pinst R σ τ Δ γ : PΔ R σ (lenv_pinst τ Δ) γ ↔ PΔ R (λ a, pt_inst σ (τ a)) Δ γ.
Proof.
  split; intros H i T Hi.
  - apply PV_pinst, H. rewrite lenv_pinst_lookup, Hi. done.
  - rewrite lenv_pinst_lookup in Hi. destruct (Δ !! i) as [[T0|]|] eqn:E; simplify_eq/=.
    apply PV_pinst. by apply H.
Qed.

Lemma PΔ_split_l R σ Δ Δ1 Δ2 γ : lenv_split Δ Δ1 Δ2 → PΔ R σ Δ γ → PΔ R σ Δ1 γ.
Proof. intros Hs H i T Hi. apply H. by eapply lenv_split_sub_l. Qed.

Lemma PΔ_split_r R σ Δ Δ1 Δ2 γ : lenv_split Δ Δ1 Δ2 → PΔ R σ Δ γ → PΔ R σ Δ2 γ.
Proof. intros Hs H i T Hi. apply H. by eapply lenv_split_sub_r. Qed.

Lemma lage_lookup c Δ Δ' : lage c Δ Δ' → ∀ i T', Δ' !! i = Some (Some T') →
  ∃ T, Δ !! i = Some (Some T) ∧ tage c T T'.
Proof.
  induction 1 as [|Δ Δ' _ IH|T0 T0' Δ Δ' Ht _ IH]; intros [|i] T' Hi; simpl in *; try done; eauto.
  injection Hi as ->. eauto.
Qed.

Lemma PΔ_lage R σ c Δ Δ' γ : lage c Δ Δ' → PΔ R σ Δ γ → PΔ R σ Δ' γ.
Proof.
  intros Hl H i T' Hi. destruct (lage_lookup _ _ _ Hl i T' Hi) as (T & HT & Ha).
  apply (PV_tage R c T T'); [done|]. by apply H.
Qed.

Lemma PΔ_cons R σ T Δ v γ : PV R σ T v → PΔ R σ Δ γ → PΔ R σ (Some T :: Δ) (v .: γ).
Proof. intros Hv H [|i] T' Hi; simpl in *; [by injection Hi as <-|by apply H]. Qed.

Lemma PΔ_lden R σ Δ : lenv_unl Δ → PΔ R σ Δ (lden σ Δ).
Proof.
  intros Hu i T Hi. unfold lden. rewrite Hi. apply PV_bden.
  destruct (Hu (Some T)) as [?|(U & [= <-] & HU)]; [by eapply list_elem_of_lookup_2|done|done].
Qed.

Lemma PΔ_nil R σ γ : PΔ R σ [] γ.
Proof. intros i T Hi. by rewrite lookup_nil in Hi. Qed.

(** ** Instances *)

Lemma pclose_lt xs m σ a : a < m → length xs = m → pclose xs m σ a = plist xs a.
Proof. intros Ha Hl. unfold pclose, pup. rewrite decide_True by done. by rewrite pt_inst_pvar_at. Qed.

Lemma pclose_ge xs m σ a : m ≤ a → length xs = m → pclose xs m σ a = σ (a - m).
Proof.
  intros Ha Hl. unfold pclose, pup. rewrite decide_False by lia. rewrite pt_inst_comp.
  rewrite (pt_inst_ext _ pvar); [apply pt_inst_pvar|]. intros b. unfold compose.
  rewrite pt_inst_pvar_at. by apply plist_shift.
Qed.

Lemma pclose_add xs m σ a : length xs = m → pclose xs m σ (a + m) = σ a.
Proof. intros Hl. rewrite pclose_ge by lia. f_equal. lia. Qed.

Lemma plist_fmap_lt σ xs a : a < length xs → pt_inst σ (plist xs a) = plist (pt_inst σ <$> xs) a.
Proof.
  intros Ha. unfold plist. rewrite list_lookup_fmap.
  destruct (xs !! a) eqn:E; [done|]. apply lookup_ge_None in E. lia.
Qed.

Lemma pclose_plist σ xs m a : length xs = m →
  pt_inst σ (plist xs a) = pclose (pt_inst σ <$> xs) m σ a.
Proof.
  intros Hl. destruct (decide (a < m)) as [Ha|Ha].
  - rewrite pclose_lt by (try done; by rewrite length_fmap). apply plist_fmap_lt. lia.
  - rewrite pclose_ge by (try lia; by rewrite length_fmap). unfold plist.
    destruct (xs !! a) eqn:E; [apply lookup_lt_Some in E; lia|]. rewrite pt_inst_pvar_at. by subst.
Qed.

Lemma PV_ty_inst R σ xs T v : PV R σ (ty_inst xs T) v ↔ PV R (pclose (pt_inst σ <$> xs) (length xs) σ) T v.
Proof. unfold ty_inst. rewrite PV_pinst. apply PV_ext. intros a. by apply pclose_plist. Qed.

Lemma PVpar_ty_inst R σ xs T v : PVpar R σ (ty_inst xs T) v ↔ PVpar R (pclose (pt_inst σ <$> xs) (length xs) σ) T v.
Proof. destruct T; simpl; try done. apply PV_ty_inst. Qed.

(** The parameter of a box type at an instance, as it is read from
    the value of the box. *)
Lemma PVpar_box_inst R σ xs m U v :
  PVpar R (plist xs) (erase (pinst_ty (pup m σ) U)) v ↔ PVpar R (pclose xs m σ) U v.
Proof.
  rewrite (PVpar_erase R _ (pinst_ty (pup m σ) U)) by apply erase_idem.
  rewrite PVpar_pinst. apply PVpar_ext. done.
Qed.

(** ** Facts of contexts read at a model *)

Section sem.
  Context (W : sworld) (Hwf : sworld_wf W).

  Lemma w_lt_le R x y z : R ⊢ x ≺ y → w_le R y z → R ⊢ x ≺ z.
  Proof. intros H [<-|H']; [done|by eapply w_lt_trans]. Qed.

  Lemma PV_pack R σ Γ lb m C T xs v :
    wmodels R W → hsat R σ Γ → length xs = m → hold_at W Γ C xs →
    lbx_below_h W Γ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
    PV R σ (ty_inst xs T) v → PV R σ (TEx lb m C T) v.
  Proof.
    intros HW Hs Hl HC Hlb Hv. simpl. exists (pt_inst σ <$> xs). split_and!.
    - by rewrite length_fmap.
    - by eapply hold_sem.
    - destruct lb as [| |l]; simpl in Hlb |- *; [|done|].
      + destruct Hlb as [Hh Hb]. by eapply vheads_empty.
      + destruct Hlb as [Hh Hb]. intros y Hy.
        destruct (heads_PV R _ σ v Hv Hb y Hy) as (h & Hh' & Hle).
        eapply w_le_trans; [|exact Hle]. eapply sle_sem; [done|done|done|]. by apply Hh.
    - apply PV_ty_inst in Hv. by rewrite Hl in Hv.
  Qed.

  Lemma PV_tsub Γ T T' : tsub W Γ T T' → ∀ R σ v, wmodels R W → hsat R σ Γ →
    PV R σ T v → PV R σ T' v.
  Proof.
    induction 1 as [Γ|Γ ub lb c T1 U a c' T1' U' a' _ _ _ _ _ _|Γ T1 U T1' U' _ IH1 _ IH2
      |Γ T1 U T1' U' _ IH1 _ IH2|Γ n k C ub c U U' c' _ HU|Γ s s' x a a' mt _ _
      |Γ lb lb' n C C' T T' HC Hlb _ IH];
      intros R σ v HW Hs; simpl; try done.
    - intros (a0 & b & -> & H1 & H2). eauto 10.
    - intros (i & a0 & -> & [[-> H]|[-> H]]); eauto 10.
    - intros ->. f_equal. rewrite !erase_pinst. f_equal.
      destruct k as [|k]; [by eapply eqT_erase|]. destruct HU as [->|(HU & _)]; [done|by eapply eqT_erase].
    - intros (xs & Hl & Hw & Hb & Hv). exists xs.
      assert (hsat R (pclose xs n σ) (hc_open n C Γ)) as Hs' by (by apply hsat_open).
      split_and!; [done| | |by eapply IH].
      + pose proof (hold_sem W R Hwf HW _ _ _ _ Hs' HC) as H.
        rewrite bcs_inst_comp, pclose_ids in H by done.
        erewrite bcs_inst_ext; [exact H|]. intros a. unfold compose. symmetry. by apply pclose_shift.
      + destruct Hlb as [->|Hlb]; [done|]. destruct lb' as [| |l]; simpl in Hlb |- *; [|done|].
        * destruct Hlb as [Hh Hb']. by eapply vheads_empty.
        * destruct Hlb as [Hh Hb']. intros y Hy.
          destruct (heads_PV R _ _ v Hv Hb' y Hy) as (h & Hh' & Hle).
          eapply w_le_trans; [|exact Hle].
          pose proof (sle_sem W R Hwf HW _ _ _ _ Hs' (Hh h Hh')) as H.
          by rewrite (pt_unshift _ σ n (pclose_shift xs n σ Hl)) in H.
  Qed.

  Lemma PVpar_tsub Γ T T' R σ v : tsub W Γ T T' → wmodels R W → hsat R σ Γ →
    PVpar R σ T' v → PVpar R σ T v.
  Proof. intros Hsub HW Hs. destruct Hsub; simpl; try done. intros Hv. eapply PV_tsub; [eassumption|done|done|done]. Qed.
End sem.

(** ** Derivations up to E-Sub, E-Pack and E-Open

    [spo W Q] closes a property Q of a context and a type under the
    three rules that apply to every term. A derivation of a term of a
    given form is the rule of that form under such a stack
    ([spo_close], …, [spo_box]). [spo_sem] reads the stack at a model:
    each opening takes the witnesses that the value of the opened
    variable carries, so a model of the given context gives a model of
    the context of the rule, the value of the conclusion reads back at
    the given type, and the parameter of an arrow reads forward. *)

Inductive spo (W : sworld) (Q : tenv → hctx → lenv → sfuture → ty → Prop) :
    tenv → hctx → lenv → sfuture → ty → Prop :=
  | spo_base Θ Γ Δ F T : Q Θ Γ Δ F T → spo W Q Θ Γ Δ F T
  | spo_sub Θ Γ Δ F T T' : spo W Q Θ Γ Δ F T → tsub W Γ T T' → spo W Q Θ Γ Δ F T'
  | spo_pack Θ Γ Δ F lb m C T xs :
      length xs = m → hold_at W Γ C xs → lbx_below_h W Γ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
      spo W Q Θ Γ Δ F (ty_inst xs T) → spo W Q Θ Γ Δ F (TEx lb m C T)
  | spo_open Θ Γ Δ F i lb m C T U :
      Δ !! i = Some (Some (TEx lb m C T)) →
      spo W Q (tenv_pinst (pshift m) Θ) (hc_open m C Γ) (<[i := Some T]> (lenv_pinst (pshift m) Δ))
        (sf_pinst (pshift m) F) (pinst_ty (pshift m) U) →
      spo W Q Θ Γ Δ F U.

Local Ltac spo_tac IH :=
  first
    [ eapply spo_sub; [by apply IH|eassumption]
    | eapply spo_pack; [eassumption|eassumption|eassumption|by apply IH]
    | eapply spo_open; [eassumption|by apply IH] ].

Section spo_forms.
  Context (W : sworld) (N : fuel).

  Lemma spo_var Θ Γ Δ F i T c : typed W N Θ Γ Δ F (Var i) T c →
    spo W (λ Θ Γ Δ F T, lenv_only Δ i T) Θ Γ Δ F T.
  Proof.
    remember (Var i) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <-. by apply spo_base.
  Qed.

  Lemma spo_unit Θ Γ Δ F T c : typed W N Θ Γ Δ F EUnit T c →
    spo W (λ _ _ _ _ T, T = TUnit) Θ Γ Δ F T.
  Proof.
    remember EUnit as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    by apply spo_base.
  Qed.

  Lemma spo_new Θ Γ Δ F T c : typed W N Θ Γ Δ F ENew T c →
    spo W (λ Θ Γ Δ F T,
      (∃ C S m1 m2, new_ok N W Γ C ∧
         T = TEx LBot 1 C (TProd (TSess S (pvar 0) m1 m1) (TSess (dual S) (pvar 0)‾ m2 m2))) ∨
      (∃ x κ S m1 m2, T = TProd (TSess S (x·κ) m1 m1) (TSess (dual S) (x·κ)‾ m2 m2))) Θ Γ Δ F T.
  Proof.
    remember ENew as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped; apply spo_base.
    - left. do 4 eexists. split; [eassumption|reflexivity].
    - right. do 5 eexists. reflexivity.
  Qed.

  Lemma spo_pair Θ Γ Δ F e1 e2 T c : typed W N Θ Γ Δ F (Pair e1 e2) T c →
    spo W (λ Θ Γ Δ F T, ∃ Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' T1 T1' T2 c1 c2,
      lenv_split Δ Δ1 Δ2 ∧
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 c1 ∧
      lage c1 Δ2 Δ2' ∧ typed W N Θ2' Γ Δ2' (sf_unionb F (heads T1) (hbot T1)) e2 T2 c2 ∧
      tage c2 T1 T1' ∧ T = TProd T1' T2) Θ Γ Δ F T.
  Proof.
    remember (Pair e1 e2) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <- <-. apply spo_base. do 11 eexists. split_and!; eauto.
  Qed.

  Lemma spo_letu Θ Γ Δ F e1 e2 T c : typed W N Θ Γ Δ F (LetU e1 e2) T c →
    spo W (λ Θ Γ Δ F T, ∃ Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' c1 c2,
      lenv_split Δ Δ1 Δ2 ∧
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit c1 ∧
      lage c1 Δ2 Δ2' ∧ typed W N Θ2' Γ Δ2' F e2 T c2) Θ Γ Δ F T.
  Proof.
    remember (LetU e1 e2) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <- <-. apply spo_base. do 8 eexists. split_and!; eauto.
  Qed.

  Lemma spo_letp Θ Γ Δ F e1 e2 T c : typed W N Θ Γ Δ F (LetP e1 e2) T c →
    spo W (λ Θ Γ Δ F T, ∃ Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' T1 T2 c1 c2,
      lenv_split Δ Δ1 Δ2 ∧
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) c1 ∧
      lage c1 Δ2 Δ2' ∧ typed W N Θ2' Γ (Some T2 :: Some T1 :: Δ2') F e2 T c2) Θ Γ Δ F T.
  Proof.
    remember (LetP e1 e2) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <- <-. apply spo_base. do 10 eexists. split_and!; eauto.
  Qed.

  Lemma spo_abs Θ Γ Δ F e T c : typed W N Θ Γ Δ F (Lam e) T c →
    spo W (λ Θ Γ Δ F T, ∃ Θh Δh T1 U ub lb c a,
      lage a Δ Δh ∧ T = TLolli ub lb c T1 U a ∧
      typed W N Θh Γ (Some T1 :: Δh) (abs_fut ub) e U c) Θ Γ Δ F T.
  Proof.
    remember (Lam e) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <-. apply spo_base. do 8 eexists. split_and!; eauto.
  Qed.

  Lemma spo_app Θ Γ Δ F e1 e2 T c : typed W N Θ Γ Δ F (App e1 e2) T c →
    spo W (λ Θ Γ Δ F T, ∃ Θ1 Θ2' Δ1 Δ2 Δ2' F1 F2 ub lb c0 T1 a1 c1 c2,
      lenv_split Δ Δ1 Δ2 ∧ lage c1 Δ2 Δ2' ∧
      typed W N Θ1 Γ Δ1 F1 e1 (TLolli ub lb c0 T1 T a1) c1 ∧
      typed W N Θ2' Γ Δ2' F2 e2 T1 c2) Θ Γ Δ F T.
  Proof.
    remember (App e1 e2) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <- <-. apply spo_base. do 14 eexists. split_and!; eauto.
  Qed.

  Lemma spo_spawn Θ Γ Δ F e T c : typed W N Θ Γ Δ F (ESpawn e) T c →
    spo W (λ Θ Γ Δ F T, ∃ ub lb c' a c0,
      typed W N Θ Γ Δ F e (TLolli ub lb c' TUnit TUnit a) c0) Θ Γ Δ F T.
  Proof.
    remember (ESpawn e) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <-. apply spo_base. do 5 eexists. eauto.
  Qed.

  Lemma spo_force Θ Γ Δ F e T c : typed W N Θ Γ Δ F (EForce e) T c →
    spo W (λ Θ Γ Δ F T, ∃ m k C ub cb U xs ss c0,
      length xs = m ∧ hold_at W Γ C xs ∧ typed W N Θ Γ Δ F e (TBox m k C ub cb U) c0 ∧
      T = sinst_ty (slist ss) (ty_inst xs U)) Θ Γ Δ F T.
  Proof.
    remember (EForce e) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <-. apply spo_base. do 9 eexists. split_and!; eauto.
  Qed.

  Lemma spo_box Θ Γ Δ F e T c : typed W N Θ Γ Δ F (EBox e) T c →
    spo W (λ Θ Γ Δ F T, ∃ m k C ub cb U, Θ = ∅ ∧ lenv_unl Δ ∧ T = TBox m k C ub cb U ∧
      ∀ ss, length ss = k → sinsts N ss →
        typed W N ∅ (hc_open m C Γ) (lenv_pinst (pshift m) (Some (TBox m k C ub cb U) :: Δ))
          (∅, Some (rest_of ub)) e (sinst_ty (slist ss) U) cb) Θ Γ Δ F T.
  Proof.
    remember (EBox e) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <-. apply spo_base. do 6 eexists. split_and!; eauto.
  Qed.

  Lemma spo_close Θ Γ Δ F e T c : typed W N Θ Γ Δ F (EClose e) T c →
    spo W (λ Θ Γ Δ F T, ∃ S0 x a mS c0, T = TUnit ∧ ub_below_s W Γ (Some x) F ∧
      typed W N Θ Γ Δ F e (TSess S0 x a mS) c0) Θ Γ Δ F T.
  Proof.
    remember (EClose e) as e0 eqn:He. induction 1; try discriminate; try spo_tac IHtyped.
    injection He as <-. apply spo_base. do 5 eexists. split_and!; eauto.
  Qed.
End spo_forms.

Section spo_sem.
  Context (W : sworld) (Hwf : sworld_wf W).

  Lemma spo_sem Q Θ Γ Δ F T : spo W Q Θ Γ Δ F T →
    ∀ R σ γ, wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ Θ' Γ' Δ' F' T0 σ' τ, Q Θ' Γ' Δ' F' T0 ∧ hsat R σ' Γ' ∧ PΔ R σ' Δ' γ ∧
      (∀ y, y ∈ F.1 → pt_inst τ y ∈ F'.1) ∧ (F.2 = Some RAll → F'.2 = Some RAll) ∧
      (∀ y, pt_inst σ' (pt_inst τ y) = pt_inst σ y) ∧
      (∀ R' v, R ⊑ R' → PV R' σ' T0 v → PV R' σ T v) ∧
      (∀ R' v, R ⊑ R' → PVpar R' σ T v → PVpar R' σ' T0 v).
  Proof.
    induction 1 as [Θ Γ Δ F T HQ|Θ Γ Δ F T T' _ IH Hsub|Θ Γ Δ F lb m C T xs Hl HC Hlb _ IH
      |Θ Γ Δ F i lb m C T U Hi _ IH]; intros R σ γ HW Hs HΔ.
    - exists Θ, Γ, Δ, F, T, σ, pvar. split_and!; try done.
      + intros y Hy. by rewrite pt_inst_pvar.
      + intros y. by rewrite pt_inst_pvar.
    - destruct (IH R σ γ HW Hs HΔ) as (Θ' & Γ' & Δ' & F' & T0 & σ' & τ & HQ & Hs' & HΔ' & HF1 & HF2 & Hag & Hc & Hp).
      exists Θ', Γ', Δ', F', T0, σ', τ. split_and!; try done.
      + intros R' v HR Hv. eapply PV_tsub; [done|exact Hsub|by eapply wmodels_mono|by eapply hsat_mono|by apply Hc].
      + intros R' v HR Hv. apply Hp; [done|].
        eapply PVpar_tsub; [done|exact Hsub|by eapply wmodels_mono|by eapply hsat_mono|done].
    - destruct (IH R σ γ HW Hs HΔ) as (Θ' & Γ' & Δ' & F' & T0 & σ' & τ & HQ & Hs' & HΔ' & HF1 & HF2 & Hag & Hc & Hp).
      exists Θ', Γ', Δ', F', T0, σ', τ. split_and!; try done.
      + intros R' v HR Hv. eapply PV_pack; [done|by eapply wmodels_mono|by eapply hsat_mono|done|done|done|by apply Hc].
    - destruct (HΔ i _ Hi) as (xs & Hl & Hw & Hb & Hv).
      assert (hsat R (pclose xs m σ) (hc_open m C Γ)) as Hs1 by (by apply hsat_open).
      assert (PΔ R (pclose xs m σ) (<[i := Some T]> (lenv_pinst (pshift m) Δ)) γ) as HΔ1.
      { intros j T' Hj. apply list_lookup_insert_Some in Hj as [(<- & [= <-] & _)|(Hne & Hj)]; [done|].
        rewrite lenv_pinst_lookup in Hj. destruct (Δ !! j) as [[T0|]|] eqn:E; simplify_eq/=.
        apply PV_pinst. apply (PV_ext R T0 σ); [intros a; symmetry; by apply pclose_shift|by apply HΔ]. }
      destruct (IH R _ γ HW Hs1 HΔ1) as (Θ' & Γ' & Δ' & F' & T0 & σ' & τ & HQ & Hs' & HΔ' & HF1 & HF2 & Hag & Hc & Hp).
      exists Θ', Γ', Δ', F', T0, σ', (pt_inst τ ∘ pshift m). split_and!; try done.
      + intros y Hy. rewrite <-pt_inst_comp. apply HF1. unfold sf_pinst. simpl. by apply elem_of_map_2.
      + intros H2. apply HF2. unfold sf_pinst. simpl. by rewrite H2.
      + intros y. rewrite <-pt_inst_comp, Hag. by apply (pt_unshift _ σ m (pclose_shift xs m σ Hl)).
      + intros R' v HR Hv'. apply Hc in Hv'; [|done].
        apply (proj1 (PV_pinst R' U (pclose xs m σ) (pshift m) v)) in Hv'.
        refine (proj1 (PV_ext R' U _ _ v _) Hv'). intros a. cbn beta. by apply pclose_shift.
      + intros R' v HR Hv'. apply Hp; [done|]. apply (proj2 (PVpar_pinst R' U (pclose xs m σ) (pshift m) v)).
        refine (proj1 (PVpar_ext R' U _ _ v _) Hv'). intros a. cbn beta. symmetry. by apply pclose_shift.
  Qed.
End spo_sem.

(** ** A creation at a fresh root under (gen-new)

    The world construction of [Erel_new] (compat/Redex.v): every ranked
    world W1 with the semantic (gen-new) of C grows to a world that
    holds C at a fresh point. It takes excluded middle for the largest
    rank of a finite set ([list_max_rank]). *)
Lemma gen_new_ext (EM : excluded_middle) W1 C :
  wranked W1 → gen_new_sem W1 C → ∃ π W', W1 ⊑ W' ∧ wholds W' C [π].
Proof.
  intros HR1 (Hwf & Hcc & Sr & HnT & Hex & Hstp & Hen).
  destruct (fresh_const W1 (bc_env C)) as (a & Ha1 & Ha2).
  set (π := MkPt (NConst a) true 0).
  set (σ := plist (π :: bc_env C)).
  assert (σ 0 = MkPt (NConst a) true 0) as Hσ by done.
  set (rk0 := wgrow_rank W1 (λ y, onat (pt_off y))).
  assert (∀ x y, W1 ⊢ x ≺ y → olt (rk0 x) (rk0 y)) as Hrk0.
  { intros x y. unfold rk0, wgrow_rank. intros [Hp|(Hx & Hy & Hlt)].
    - pose proof (rin_po W1 x y Hp) as Hr. destruct (po_root x y Hp) as [_ Ho].
      destruct (decide (rin W1 x)) as [Hx|Hx].
      + rewrite decide_True by tauto. by apply rank_po.
      + rewrite decide_False by tauto. by apply onat_lt.
    - rewrite !decide_True by done. by apply w_ord_rank. }
  set (b0 := λ u0 : point, olim (λ s : {y : point | pt_root y ≠ NConst a ∧ bcs_at C [π] (FLt y (pt_inst σ u0))},
               osucc (rk0 (proj1_sig s)))).
  set (ρ := λ x, if decide (pt_root x = NConst a) then rank_base (new_step C) b0 Hwf (pt_unroot a x)
                 else onat (pt_off x)).
  set (B := {[NConst a]} ∪ (list_to_set (pt_root <$> bc_env C) : gset pname)).
  assert (ranks_po B ρ) as Hρ.
  { intros x _. unfold ρ. change (pt_root x⁺) with (pt_root x). change (pt_root x‾⁺) with (pt_root x).
    destruct (decide (pt_root x = NConst a)) as [Hx|Hx].
    - pose proof (pt_root_unroot a x Hx) as H0.
      split; apply rank_base_lt; (split; [done|split; [done|right]]);
        [left|right]; done.
    - split; apply onat_lt; simpl; lia. }
  set (W' := wgrow W1 HR1 B ρ Hρ).
  assert (∀ x y, rin W' x → rin W' y → olt (w_rank W' x) (w_rank W' y) → W' ⊢ x ≺ y) as HltW.
  { intros x y Hx Hy H. right. split_and!; [done|done|]. apply w_ord_rank; [apply wgrow_ranked|done|done|done]. }
  assert (∀ x, pt_root x = NConst a → w_rank W' x = rank_base (new_step C) b0 Hwf (pt_unroot a x)) as Hra.
  { intros x Hx. unfold W'. rewrite wgrow_rank_new; [unfold ρ; by rewrite decide_True|]. unfold rin. rewrite Hx. done. }
  assert (∀ x, pt_root x ≠ NConst a → w_rank W' x = rk0 x) as Hro.
  { intros x Hx. unfold W'. change (w_rank (wgrow W1 HR1 B ρ Hρ) x) with (wgrow_rank W1 ρ x).
    unfold rk0, wgrow_rank. case_decide; [done|].
    unfold ρ. by rewrite decide_False. }
  (* the instance of a point of the tree of 0, and of a context point *)
  assert (∀ p, in_tree0 p → pt_root (pt_inst σ p) = NConst a ∧ rin W' (pt_inst σ p) ∧
            w_rank W' (pt_inst σ p) = rank_base (new_step C) b0 Hwf p) as Htr.
  { intros p Hp. assert (pt_root (pt_inst σ p) = NConst a) as Hr by (rewrite pt_root_inst_var, Hp; done).
    split_and!; [done|apply wgrow_rin; rewrite Hr; set_solver|].
    by rewrite (Hra _ Hr), (pt_unroot_inst a σ Hσ p Hp). }
  assert (∀ p, pn_vb (1 + length (bc_env C)) (pt_name p) → ¬ in_tree0 p →
            pt_inst σ p = ctx_pt C p ∧ pt_root (pt_inst σ p) ≠ NConst a ∧ rin W' (pt_inst σ p)) as Hout.
  { intros p Hsp Hp. apply pn_vb_root in Hsp as ([|j] & Hj & Hjl); [by destruct Hp|].
    simpl in Hjl. destruct (lookup_lt_is_Some_2 (bc_env C) j ltac:(lia)) as [yj Hyj].
    assert (pt_root (pt_inst σ p) = pt_root yj) as Hr.
    { rewrite pt_root_inst_var. change (pt_root p) with (pn_root (pt_name p)). rewrite Hj.
      simpl. unfold σ, plist. simpl. by rewrite Hyj. }
    split_and!.
    - unfold ctx_pt. apply pt_inst_ext_root. intros b Hb. change (pt_root p) with (pn_root (pt_name p)) in Hb.
      rewrite Hj in Hb. injection Hb as <-. done.
    - rewrite Hr. apply Ha2. by eapply list_elem_of_lookup_2.
    - apply wgrow_rin. rewrite Hr. apply elem_of_union_r, elem_of_list_to_set.
      apply list_elem_of_fmap. exists yj. split; [done|]. by eapply list_elem_of_lookup_2. }
  (* a point paired with T lies at or below the rank of some t ∈ T *)
  assert (∀ s, in_tree0 s → ∀ T, Sr s T → ∃ t, t ∈ T ∧ ole (rank_base (new_step C) b0 Hwf s) (rk0 t)) as Hinv.
  { intros s. induction (Hwf s) as [s _ IH]. intros Hsin T HT.
    destruct (list_max_rank EM rk0 T (HnT s T HT)) as (tm & Htm & Hmax).
    exists tm. split; [done|]. apply rank_base_le.
    - unfold b0. apply ole_lim_l. intros [y [Hyr Hy]]. cbn [proj1_sig].
      apply bcs_at_iff in Hy as ([z0 s0] & Hf & Hsc & Heq). simpl in Heq. injection Heq as Ey Es.
      try change (plist ([π] ++ bc_env C)) with σ in Ey, Es. try change (plist (π :: bc_env C)) with σ in Ey, Es.
      assert (in_tree0 s0) as Hs0.
      { destruct (decide (in_tree0 s0)) as [?|Hn]; [done|]. exfalso.
        destruct Hsc as [_ Hsc]. destruct (Hout s0 Hsc Hn) as (_ & Hne & _).
        apply Hne. rewrite <-Es. by apply Htr. }
      assert (s0 = s) as ->.
      { rewrite <-(pt_unroot_inst a σ Hσ s0 Hs0), <-(pt_unroot_inst a σ Hσ s Hsin). by rewrite Es. }
      assert (¬ in_tree0 z0) as Hz0.
      { intros Hz. apply Hyr. rewrite Ey. by apply Htr. }
      destruct Hsc as [Hsz Hss]. destruct (Hout z0 Hsz Hz0) as (Ez & _ & _). rewrite Ey, Ez.
      destruct (Hen s T z0 HT) as (t & Ht & Hlt); [split; [done|split; done]|done|].
      eapply olt_trans_le; [apply Hrk0, Hlt|apply Hmax, Ht].
    - intros s' Hs'. destruct (Hstp s T s' HT Hs') as (T' & HT' & Hlt).
      destruct (IH s' Hs' (proj1 Hs') T' HT') as (t' & Ht' & Hle).
      destruct (Hlt t' Ht') as (t & Ht & Hlt').
      eapply ole_trans_lt; [exact Hle|]. eapply olt_trans_le; [apply Hrk0, Hlt'|apply Hmax, Ht]. }
  exists π, W'. split; [apply wgrow_ext|].
  intros x y Hf. pose proof Hf as Hf0.
    apply bcs_at_iff in Hf as ([x0 y0] & Hf & Hsc & Heq). simpl in Heq. injection Heq as -> ->.
    try change (plist ([π] ++ bc_env C)) with σ in Hf0 |- *. try change (plist (π :: bc_env C)) with σ in Hf0 |- *.
    assert (cfact C x0 y0) as Hcf by (split; [done|exact Hsc]).
    destruct Hsc as [Hsx Hsy].
    destruct (decide (in_tree0 y0)) as [Hy0|Hy0], (decide (in_tree0 x0)) as [Hx0|Hx0].
    * destruct (Htr y0 Hy0) as (_ & Hry & Ey). destruct (Htr x0 Hx0) as (_ & Hrx & Ex).
      apply HltW; [done|done|]. rewrite Ex, Ey. apply rank_base_lt.
      split; [done|split; [done|left; exact Hcf]].
    * destruct (Htr y0 Hy0) as (_ & Hry & Ey). destruct (Hout x0 Hsx Hx0) as (_ & Hx & Hrx).
      apply HltW; [done|done|]. rewrite (Hro _ Hx), Ey.
      eapply olt_trans_le; [|apply rank_base_ge].
      unfold b0, olt. apply (ole_lim_r _ _ (exist _ (pt_inst σ x0) (conj Hx Hf0))). apply ole_refl.
    * destruct (Htr x0 Hx0) as (_ & Hrx & Ex). destruct (Hout y0 Hsy Hy0) as (Ey & Hy & Hry).
      destruct (Hex x0 y0 Hcf Hx0 Hy0) as (T & HT & Hlt).
      destruct (Hinv x0 Hx0 T HT) as (t & Ht & Hle).
      apply HltW; [done|done|]. rewrite Ex, (Hro _ Hy), Ey.
      eapply ole_trans_lt; [exact Hle|]. by apply Hrk0, Hlt.
    * destruct (Hout x0 Hsx Hx0) as (Ex & _ & _). destruct (Hout y0 Hsy Hy0) as (Ey & _ & _).
      rewrite Ex, Ey. eapply w_lt_mono; [apply wgrow_ext|]. by apply Hcc.
Qed.

(** ** Values and contexts along a derivation *)

Lemma lenv_heads_lookup Δ j T : Δ !! j = Some (Some T) → heads T ⊆ lenv_heads Δ.
Proof.
  revert j. induction Δ as [|[T'|] Δ IH]; intros [|j] Hj; simpl in *; try done.
  - injection Hj as ->. set_solver.
  - specialize (IH j Hj). set_solver.
  - by apply (IH j).
Qed.

Lemma lenv_bot_lookup Δ j T : Δ !! j = Some (Some T) → hbot T = true → lenv_bot Δ = true.
Proof.
  revert j. induction Δ as [|[T'|] Δ IH]; intros [|j] Hj Hb; simpl in *; try done.
  - injection Hj as ->. by rewrite Hb.
  - rewrite (IH j Hj Hb). apply orb_true_r.
  - by apply (IH j).
Qed.

Lemma sf_unionb_fst' F X b : (sf_unionb F X b).1 = F.1 ∪ X.
Proof. by destruct b. Qed.

Section values.
  Context (W : sworld) (Hwf : sworld_wf W).

  Lemma var_PV N Θ Γ Δ F i T c R σ γ : typed W N Θ Γ Δ F (Var i) T c →
    wmodels R W → hsat R σ Γ → PΔ R σ Δ γ → PV R σ T (γ i).
  Proof.
    intros Ht HW Hs HΔ. apply spo_var in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ' & Γ' & Δ' & F' & T0 & σ' & τ & [Hi _] & Hs' & HΔ' & _ & _ & _ & Hc & _).
    apply (Hc R); [apply wext_refl|]. by apply HΔ'.
  Qed.

  Lemma unit_PV N Θ Γ Δ F T c R σ γ : typed W N Θ Γ Δ F EUnit T c →
    wmodels R W → hsat R σ Γ → PΔ R σ Δ γ → PV R σ T PU.
  Proof.
    intros Ht HW Hs HΔ. apply spo_unit in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ' & Γ' & Δ' & F' & T0 & σ' & τ & -> & Hs' & HΔ' & _ & _ & _ & Hc & _).
    by apply (Hc R); [apply wext_refl|].
  Qed.

  (** A creation, at a fresh root or at a field, yields the two ends of
      a channel at q and q̄, in a world that may grow. *)
  Lemma new_PV (EM : excluded_middle) n Θ Γ Δ F T c R σ γ : typed W (Some n) Θ Γ Δ F ENew T c →
    wranked R → wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ R' q, R ⊑ R' ∧ PV R' σ T (PP (PE q) (PE q‾)).
  Proof.
    intros Ht HR HW Hs HΔ. apply spo_new in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ' & Γ' & Δ' & F' & T0 & σ' & τ & HQ & Hs' & _ & _ & _ & _ & Hc & _).
    destruct HQ as [(C & S & m1 & m2 & Hok & ->)|(x & κ & S & m1 & m2 & ->)].
    - pose proof (gen_new_sem_of W R Γ' σ' C Hwf HW Hs' (new_ok_gen (Some n) W Γ' C ltac:(done) Hok)) as HG.
      destruct (gen_new_ext EM R _ HR HG) as (π & R' & HRR & Hw).
      exists R', π. split; [done|]. apply (Hc R' _ HRR). simpl.
      exists [π]. split_and!; [done|exact Hw|done|].
      exists (PE π), (PE π‾). split_and!; [done| |].
      + rewrite pt_inst_pvar_at, (pclose_lt [π] 1 σ' 0) by (simpl; lia). done.
      + rewrite pt_inst_dual, pt_inst_pvar_at, (pclose_lt [π] 1 σ' 0) by (simpl; lia). done.
    - exists R, (pt_inst σ' (x·κ)). split; [apply wext_refl|]. apply (Hc R _ (wext_refl R)). simpl.
      exists (PE (pt_inst σ' (x·κ))), (PE (pt_inst σ' (x·κ))‾). split_and!; [done|done|by rewrite pt_inst_dual].
  Qed.

  Lemma pair_new_PV (EM : excluded_middle) n Θ Γ Δ F T c R σ γ :
    typed W (Some n) Θ Γ Δ F (Pair ENew EUnit) T c →
    wranked R → wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ R' q, R ⊑ R' ∧ PV R' σ T (PP (PP (PE q) (PE q‾)) PU).
  Proof.
    intros Ht HR HW Hs HΔ. apply spo_pair in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ' & Γ' & Δ' & F' & T0 & σ' & τ & (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T1' & T2 & c1 & c2
        & Hls & H1 & Hla & H2 & Hag & ->) & Hs' & HΔ' & _ & _ & _ & Hc & _).
    destruct (new_PV EM n _ _ _ _ _ _ _ _ _ H1 HR HW Hs' (PΔ_split_l _ _ _ _ _ _ Hls HΔ'))
      as (R' & q & HRR & Hv1).
    assert (PV R' σ' T2 PU) as Hv2.
    { eapply unit_PV; [exact H2|by eapply wmodels_mono|by eapply hsat_mono|].
      eapply PΔ_lage; [exact Hla|]. eapply PΔ_mono; [exact HRR|]. by eapply PΔ_split_r. }
    exists R', q. split; [done|]. apply (Hc R' _ HRR). simpl. do 2 eexists.
    split_and!; [done| |done]. by apply (PV_tage R' c2 T1 T1').
  Qed.

  (** let ⟨c, c′⟩ = new in e: e is typed at a model of a context that
      holds the two ends at q and q̄. *)
  Lemma letnew_step (EM : excluded_middle) n Θ Γ Δ F e T c R σ γ :
    typed W (Some n) Θ Γ Δ F (LetP (Pair ENew EUnit) (LetU (Var 0) (LetP (Var 1) e))) T c →
    wranked R → wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ R' q Θ' Γ' Δ' F' T' c' σ', R ⊑ R' ∧ typed W (Some n) Θ' Γ' Δ' F' e T' c' ∧ hsat R' σ' Γ' ∧
      PΔ R' σ' Δ' (PE q‾ .: PE q .: PU .: PP (PE q) (PE q‾) .: γ).
  Proof.
    intros Ht HR HW Hs HΔ. apply spo_letp in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ0 & Γ0 & Δ0 & F0 & T0 & σ0 & τ0 & (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & c1 & c2
        & Hls & H1 & Hla & H2) & Hs0 & HΔ0 & _).
    destruct (pair_new_PV EM n _ _ _ _ _ _ _ _ _ H1 HR HW Hs0 (PΔ_split_l _ _ _ _ _ _ Hls HΔ0))
      as (R1 & q & HR1 & Hv).
    destruct Hv as (a & b & [= <- <-] & Ha & Hb).
    assert (wmodels R1 W) as HW1 by (by eapply wmodels_mono).
    assert (PΔ R1 σ0 (Some T2 :: Some T1 :: Δ2') (PU .: PP (PE q) (PE q‾) .: γ)) as HΔ1.
    { apply PΔ_cons; [done|]. apply PΔ_cons; [done|].
      eapply PΔ_lage; [exact Hla|]. eapply PΔ_mono; [exact HR1|]. by eapply PΔ_split_r. }
    apply spo_letu in H2.
    destruct (spo_sem W Hwf _ _ _ _ _ _ H2 R1 σ0 _ HW1 (hsat_mono _ _ _ _ HR1 Hs0) HΔ1)
      as (Θ3 & Γ3 & Δ3 & F3 & T3 & σ3 & τ3 & (Θ4 & Θ5 & Θ5' & Δ4 & Δ5 & Δ5' & c4 & c5
        & Hls2 & _ & Hla2 & H3) & Hs3 & HΔ3 & _).
    apply spo_letp in H3.
    destruct (spo_sem W Hwf _ _ _ _ _ _ H3 R1 σ3 _ HW1 Hs3 (PΔ_lage _ _ _ _ _ _ Hla2 (PΔ_split_r _ _ _ _ _ _ Hls2 HΔ3)))
      as (Θ6 & Γ6 & Δ6 & F6 & T6 & σ6 & τ6 & (Θ7 & Θ8 & Θ8' & Δ7 & Δ8 & Δ8' & A & B & c7 & c8
        & Hls3 & Hv1 & Hla3 & He) & Hs6 & HΔ6 & _).
    pose proof (var_PV _ _ _ _ _ _ _ _ _ _ _ Hv1 HW1 Hs6 (PΔ_split_l _ _ _ _ _ _ Hls3 HΔ6)) as Hx.
    simpl in Hx. destruct Hx as (a' & b' & [= <- <-] & Ha' & Hb').
    exists R1, q, Θ8', Γ6, (Some B :: Some A :: Δ8'), F6, T6, c8, σ6. split_and!; [done|exact He|done|].
    apply PΔ_cons; [done|]. apply PΔ_cons; [done|]. eapply PΔ_lage; [exact Hla3|]. by eapply PΔ_split_r.
  Qed.

  Lemma letu_split N Θ Γ Δ F e1 e2 T c R σ γ : typed W N Θ Γ Δ F (LetU e1 e2) T c →
    wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ Θ1 Γ' Δ1 F1 c1 Θ2' Δ2' F' T' c2 σ', typed W N Θ1 Γ' Δ1 F1 e1 TUnit c1 ∧
      typed W N Θ2' Γ' Δ2' F' e2 T' c2 ∧ hsat R σ' Γ' ∧ PΔ R σ' Δ1 γ ∧ PΔ R σ' Δ2' γ.
  Proof.
    intros Ht HW Hs HΔ. apply spo_letu in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ0 & Γ0 & Δ0 & F0 & T0 & σ0 & τ0 & (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & c1 & c2
        & Hls & H1 & Hla & H2) & Hs0 & HΔ0 & _).
    do 11 eexists. split_and!; [exact H1|exact H2|exact Hs0|by eapply PΔ_split_l|].
    eapply PΔ_lage; [exact Hla|]. by eapply PΔ_split_r.
  Qed.

  Lemma spawn_lam_step N Θ Γ Δ F e T c R σ γ : typed W N Θ Γ Δ F (ESpawn (Lam e)) T c →
    wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ Θ' Γ' Δ' F' U' c' σ', typed W N Θ' Γ' Δ' F' e U' c' ∧ hsat R σ' Γ' ∧ PΔ R σ' Δ' (PU .: γ).
  Proof.
    intros Ht HW Hs HΔ. apply spo_spawn in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ0 & Γ0 & Δ0 & F0 & T0 & σ0 & τ0 & (ub & lb & c' & a & c0 & Hl) & Hs0 & HΔ0 & _).
    apply spo_abs in Hl.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Hl R σ0 γ HW Hs0 HΔ0)
      as (Θ1 & Γ1 & Δ1 & F1 & T1 & σ1 & τ1 & (Θh & Δh & A & U & ub' & lb' & c'' & a' & Hla & -> & He)
        & Hs1 & HΔ1 & _ & _ & _ & _ & Hp).
    pose proof (Hp R PU (wext_refl R) eq_refl) as HA. simpl in HA.
    do 7 eexists. split_and!; [exact He|exact Hs1|]. apply PΔ_cons; [done|]. by eapply PΔ_lage.
  Qed.

  (** force e at an arrow whose parameter holds v: e is a box whose
      constraint holds at an instance where the parameter of the box
      holds v. *)
  Lemma force_step N Θ Γ Δ F e ub lb c0 T1 U a c R σ γ v :
    typed W N Θ Γ Δ F (EForce e) (TLolli ub lb c0 T1 U a) c →
    wmodels R W → hsat R σ Γ → PΔ R σ Δ γ → PV R σ T1 v →
    ∃ Θ' Γ' Δ' F' m k C ub' cb U' xs c' σ', typed W N Θ' Γ' Δ' F' e (TBox m k C ub' cb U') c' ∧
      hsat R σ' Γ' ∧ PΔ R σ' Δ' γ ∧ length xs = m ∧ wholds R (bcs_inst σ' C) xs ∧
      PVpar R (plist xs) (erase (pinst_ty (pup m σ') U')) v.
  Proof.
    intros Ht HW Hs HΔ Hv. apply spo_force in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ0 & Γ0 & Δ0 & F0 & T0 & σ0 & τ0 & (m & k & C & ub' & cb & U' & xs0 & ss & c0' & Hl & HC & He & ->)
        & Hs0 & HΔ0 & _ & _ & _ & _ & Hp).
    pose proof (Hp R v (wext_refl R) Hv) as Hpv.
    exists Θ0, Γ0, Δ0, F0, m, k, C, ub', cb, U', (pt_inst σ0 <$> xs0), c0', σ0.
    split_and!; [exact He|done|done|by rewrite length_fmap|by eapply hold_sem|].
    apply PVpar_box_inst. rewrite <-Hl. apply PVpar_ty_inst.
    exact (proj1 (PVpar_erase R _ _ σ0 v (erase_sinst _ _)) Hpv).
  Qed.

  (** close c in e2, where e2 uses the end w at s: the point of c lies
      below s̄, through any openings. *)
  Lemma close_PV N Θ Γ Δ F i j e2 T c R σ γ s :
    typed W N Θ Γ Δ F (LetU (EClose (Var i)) e2) T c → freevar j e2 → γ j = PE s →
    wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ q, γ i = PE q ∧ R ⊢ q ≺ s‾.
  Proof.
    intros Ht Hfj Hj HW Hs HΔ. apply spo_letu in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ0 & Γ1 & Δ0 & F0 & T0 & σ1 & τ1 & (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & c1 & c2
        & Hls & H1 & Hla & H2) & Hs1 & HΔ1 & _).
    apply spo_close in H1.
    destruct (spo_sem W Hwf _ _ _ _ _ _ H1 R σ1 γ HW Hs1 (PΔ_split_l _ _ _ _ _ _ Hls HΔ1))
      as (Θ4 & Γ2 & Δ4 & F2 & T2 & σ2 & τ2 & (S2 & x2 & a2 & m2 & c2' & _ & Hub & Hv2)
        & Hs2 & HΔ2 & HF1 & HF2 & Hag & _).
    pose proof (var_PV _ _ _ _ _ _ _ _ _ _ _ Hv2 HW Hs2 HΔ2) as Hi. simpl in Hi.
    exists (pt_inst σ2 x2). split; [done|].
    destruct (typed_tfacts _ _ _ _ _ _ _ _ _ H2) as [_ [Hfv _]].
    destruct (Hfv j Hfj) as [Tw' Hw'].
    destruct (lage_lookup _ _ _ Hla j Tw' Hw') as (Tw & HTw & _).
    pose proof (PΔ_split_r _ _ _ _ _ _ Hls HΔ1 j Tw HTw) as HPw. rewrite Hj in HPw.
    destruct (hbot Tw) eqn:Hb.
    - exfalso. destruct Hub as [_ Hub].
      apply (Hub RAll). apply HF2. simpl. by rewrite (lenv_bot_lookup _ _ _ HTw Hb).
    - destruct (heads_PV R Tw σ1 _ HPw Hb s‾ ltac:(simpl; set_solver)) as (h & Hh & Hle).
      assert (pt_inst τ2 h ∈ F2.1) as HhF.
      { apply HF1. rewrite sf_unionb_fst'. apply elem_of_union_r, elem_of_union_r.
        by apply (lenv_heads_lookup _ _ _ HTw). }
      destruct Hub as [Hub _]. pose proof (slt_sem W R Hwf HW σ2 Γ2 _ _ Hs2 (Hub _ HhF)) as Hlt.
      rewrite Hag in Hlt. eapply w_lt_le; [exact Hlt|exact Hle].
  Qed.

  (** let ⟨c, c′⟩ = new in e, with the pair bound directly: the
      creation is at a field. *)
  Lemma letp_new_step (EM : excluded_middle) n Θ Γ Δ F e T c R σ γ :
    typed W (Some n) Θ Γ Δ F (LetP ENew e) T c →
    wranked R → wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ R' q Θ' Γ' Δ' F' T' c' σ', R ⊑ R' ∧ typed W (Some n) Θ' Γ' Δ' F' e T' c' ∧ hsat R' σ' Γ' ∧
      PΔ R' σ' Δ' (PE q‾ .: PE q .: γ).
  Proof.
    intros Ht HR HW Hs HΔ. apply spo_letp in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θ0 & Γ0 & Δ0 & F0 & T0 & σ0 & τ0 & (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & c1 & c2
        & Hls & H1 & Hla & H2) & Hs0 & HΔ0 & _).
    destruct (new_PV EM n _ _ _ _ _ _ _ _ _ H1 HR HW Hs0 (PΔ_split_l _ _ _ _ _ _ Hls HΔ0))
      as (R1 & q & HR1 & Hv).
    destruct Hv as (a & b & [= <- <-] & Ha & Hb).
    exists R1, q, Θ2', Γ0, (Some T2 :: Some T1 :: Δ2'), F0, T0, c2, σ0.
    split_and!; [done|exact H2|by eapply hsat_mono|].
    apply PΔ_cons; [done|]. apply PΔ_cons; [done|].
    eapply PΔ_lage; [exact Hla|]. eapply PΔ_mono; [exact HR1|]. by eapply PΔ_split_r.
  Qed.

  (** spawn (λ_. (force f) c): f is a box, and its constraint holds at
      an instance where its parameter holds the value of c. *)
  Lemma child_step N Θ Γ Δ F f i T c R σ γ m C U :
    typed W N Θ Γ Δ F (ESpawn (Lam (LetU (Var 0) (App (EForce (Var (S f))) (Var (S i)))))) T c →
    wmodels R W → hsat R σ Γ → PΔ R σ Δ γ → γ f = PBox m C U →
    ∃ xs, length xs = m ∧ wholds R C xs ∧ PVpar R (plist xs) U (γ i).
  Proof.
    intros Ht HW Hs HΔ Hf.
    destruct (spawn_lam_step _ _ _ _ _ _ _ _ _ _ _ Ht HW Hs HΔ)
      as (Θ8 & Γ8 & Δ8 & F8 & U8 & c8 & σ8 & Hc8 & Hs8 & HΔ8).
    destruct (letu_split _ _ _ _ _ _ _ _ _ _ _ _ Hc8 HW Hs8 HΔ8)
      as (_ & Γ9 & _ & _ & _ & Θ9 & Δ9 & F9 & T9 & c9 & σ9 & _ & Hap & Hs9 & _ & HΔ9).
    apply spo_app in Hap.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Hap R σ9 _ HW Hs9 HΔ9)
      as (Θa & Γa & Δa & Fa & Ta & σa & τa & (Θa1 & Θa2' & Δa1 & Δa2 & Δa2' & Fa1 & Fa2 & uba & lba & ca0
        & Targ & aa1 & ca1 & ca2 & Hlsa & Hlaa & Hfa & Hv) & Hsa & HΔa & _).
    pose proof (var_PV _ _ _ _ _ _ _ _ _ _ _ Hv HW Hsa
      (PΔ_lage _ _ _ _ _ _ Hlaa (PΔ_split_r _ _ _ _ _ _ Hlsa HΔa))) as Hcv. simpl in Hcv.
    destruct (force_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfa HW Hsa (PΔ_split_l _ _ _ _ _ _ Hlsa HΔa) Hcv)
      as (Θb & Γb & Δb & Fb & m' & k' & C' & ub' & cb' & U' & xs & cb'' & σb & Hfv & Hsb & HΔb & Hl & Hw & Hp).
    pose proof (var_PV _ _ _ _ _ _ _ _ _ _ _ Hfv HW Hsb HΔb) as Hbox. simpl in Hbox.
    rewrite Hf in Hbox. apply pbox_inj in Hbox as (-> & -> & ->).
    by exists xs.
  Qed.

  (** (force !b) w: the box !b is typed by E-Box in a context with a
      model, and its constraint holds at an instance where its parameter
      holds the value of w. *)
  Lemma main_force_step N Θ Γ Δ F b j T c R σ γ :
    typed W N Θ Γ Δ F (App (EForce (EBox b)) (Var j)) T c →
    wmodels R W → hsat R σ Γ → PΔ R σ Δ γ →
    ∃ Γ0 Δ0 m k C ub cb U σ0 xs, lenv_unl Δ0 ∧
      (∀ ss, length ss = k → sinsts N ss →
         typed W N ∅ (hc_open m C Γ0) (lenv_pinst (pshift m) (Some (TBox m k C ub cb U) :: Δ0))
           (∅, Some (rest_of ub)) b (sinst_ty (slist ss) U) cb) ∧
      hsat R σ0 Γ0 ∧ length xs = m ∧ wholds R (bcs_inst σ0 C) xs ∧
      PVpar R (plist xs) (erase (pinst_ty (pup m σ0) U)) (γ j).
  Proof.
    intros Ht HW Hs HΔ. apply spo_app in Ht.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Ht R σ γ HW Hs HΔ)
      as (Θa & Γa & Δa & Fa & Ta & σa & τa & (Θa1 & Θa2' & Δa1 & Δa2 & Δa2' & Fa1 & Fa2 & uba & lba & ca0
        & Targ & aa1 & ca1 & ca2 & Hlsa & Hlaa & Hf & Hv) & Hsa & HΔa & _).
    pose proof (var_PV _ _ _ _ _ _ _ _ _ _ _ Hv HW Hsa
      (PΔ_lage _ _ _ _ _ _ Hlaa (PΔ_split_r _ _ _ _ _ _ Hlsa HΔa))) as Hwv.
    destruct (force_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hf HW Hsa (PΔ_split_l _ _ _ _ _ _ Hlsa HΔa) Hwv)
      as (Θb & Γb & Δb & Fb & m' & k' & C' & ub' & cb' & U' & xs & cb'' & σb & Hg & Hsb & HΔb & Hl & Hw & Hp).
    apply spo_box in Hg.
    destruct (spo_sem W Hwf _ _ _ _ _ _ Hg R σb _ HW Hsb HΔb)
      as (Θ0 & Γ0 & Δ0 & F0 & T0 & σ0 & τ0 & (m & k & C & ub & cb & U & _ & Hunl0 & -> & Hbody)
        & Hs0 & _ & _ & _ & _ & Hc & _).
    pose proof (Hc R _ (wext_refl R) (PV_bden R σ0 (TBox m k C ub cb U) I)) as Hbox. simpl in Hbox.
    apply pbox_inj in Hbox as (-> & HC & HU).
    exists Γ0, Δ0, m', k, C, ub, cb, U, σ0, xs. split_and!; try done.
    - by rewrite HC.
    - by rewrite HU.
  Qed.
End values.

(** ** Descent

    A property of points in ranked worlds that reappears at a lower
    point of an extension holds nowhere. A ranked point keeps its rank
    in every extension ([wext_rank]), so the rank falls. A point that
    is not ranked lies above the next one by program order, so its
    offset falls, until the next point is ranked. *)
Lemma descent (P : world → point → Prop) :
  (∀ R t, P R t → wranked R ∧ ∃ R' t', R ⊑ R' ∧ P R' t' ∧ R' ⊢ t' ≺ t) → ∀ R t, ¬ P R t.
Proof.
  intros Hs.
  assert (∀ α R t, w_rank R t = α → rin R t → ¬ P R t) as Hr.
  { intros α. induction α as [α IH] using oind. intros R t <- Hin HP.
    destruct (Hs R t HP) as (HR & R' & t' & HRR & HP' & Hlt).
    pose proof (wext_rank R R' t HRR HR Hin) as Er.
    assert (rin R' t) as Hin' by (by eapply rin_mono).
    assert (wranked R') as HR' by (by apply (wext_ranked R R')).
    destruct Hlt as [Hpo|(Ht' & _ & Hord)].
    - assert (rin R' t') as Ht' by (by apply (rin_po R' t' t Hpo)).
      refine (IH (w_rank R' t') _ R' t' eq_refl Ht' HP'). rewrite <-Er. by apply rank_po.
    - refine (IH (w_rank R' t') _ R' t' eq_refl Ht' HP'). rewrite <-Er. by apply w_ord_rank. }
  assert (∀ k R t, pt_off t = k → ¬ rin R t → ¬ P R t) as Hu.
  { intros k. induction k as [k IH] using lt_wf_ind. intros R t <- Hn HP.
    destruct (Hs R t HP) as (HR & R' & t' & HRR & HP' & Hlt).
    destruct (decide (rin R' t')) as [Ht'|Ht']; [exact (Hr _ R' t' eq_refl Ht' HP')|].
    destruct Hlt as [Hpo|(Hin' & _ & _)]; [|done].
    destruct (po_root t' t Hpo) as [_ Ho].
    exact (IH (pt_off t') Ho R' t' eq_refl Ht' HP'). }
  intros R t HP. destruct (decide (rin R t)) as [Hin|Hn];
    [exact (Hr _ R t eq_refl Hin HP)|exact (Hu _ R t eq_refl Hn HP)].
Qed.

(** ** Proposition 7

    A box □∀ιs. H. U has its body typed under Γb = [hc_open m H Γ0]. A
    branch of the body reaches the context Γc, and the points of Γb
    stand in Γc for their instances by τ. Every ranked model of W and
    Γb extends to a model of Γc that agrees with it through τ: this is
    the soundness of the creations of the branch, whatever their
    premise. In Γc the branch forces the box at xs′ with H at xs′
    ([hold_at]) and f(xs′) ≺ f(ιs) for a point f of Γb, where f(xs′)
    reads the box variables at xs′. Then W, Γ0 and H have no common
    ranked model. The model with the least rank at f(xs) has no model
    below it, which [descent] states without excluded middle. *)
Section prop7.
  Context (W : sworld) (Hwf : sworld_wf W).

  Theorem prop7 Γ0 m H Γc (τ : nat → point) xs' f :
    (∀ R σ, wranked R → wmodels R W → hsat R σ (hc_open m H Γ0) →
       ∃ R' σ', R ⊑ R' ∧ hsat R' σ' Γc ∧ ∀ a, pt_inst σ' (τ a) = σ a) →
    length xs' = m →
    hold_at W Γc (bcs_inst (λ a, τ (a + m)) H) xs' →
    slt W Γc (pt_inst (λ a, if decide (a < m) then plist xs' a else τ a) f) (pt_inst τ f) →
    ∀ R σ0 xs, wranked R → wmodels R W → hsat R σ0 Γ0 → length xs = m →
      wholds R (bcs_inst σ0 H) xs → False.
  Proof.
    intros Hext Hl' HC Hd R σ0 xs HR HW Hs Hl Hw.
    set (P := λ R t, ∃ σ0 xs, wranked R ∧ wmodels R W ∧ hsat R σ0 Γ0 ∧ length xs = m ∧
                wholds R (bcs_inst σ0 H) xs ∧ t = pt_inst (pclose xs m σ0) f).
    refine (descent P _ R (pt_inst (pclose xs m σ0) f) _); [|by exists σ0, xs].
    intros R1 t (σ1 & xs1 & HR1 & HW1 & Hs1 & Hl1 & Hw1 & ->). split; [done|].
    destruct (Hext R1 (pclose xs1 m σ1) HR1 HW1 (hsat_open _ _ _ _ _ _ Hl1 Hs1 Hw1))
      as (R2 & σ2 & HR12 & Hs2 & Hag).
    assert (wmodels R2 W) as HW2 by (by eapply wmodels_mono).
    exists R2, (pt_inst (pclose (pt_inst σ2 <$> xs') m σ1) f). split_and!; [done| |].
    - exists σ1, (pt_inst σ2 <$> xs'). split_and!; [by apply (wext_ranked R1 R2)|done|by eapply hsat_mono
        |by rewrite length_fmap| |done].
      pose proof (hold_sem W R2 Hwf HW2 _ _ _ _ Hs2 HC) as Hw2.
      rewrite bcs_inst_comp in Hw2. erewrite bcs_inst_ext; [exact Hw2|].
      intros a. unfold compose. rewrite Hag. symmetry. by apply pclose_add.
    - pose proof (slt_sem W R2 Hwf HW2 σ2 Γc _ _ Hs2 Hd) as Hlt.
      assert (pt_inst σ2 (pt_inst τ f) = pt_inst (pclose xs1 m σ1) f) as E1.
      { rewrite pt_inst_comp. apply pt_inst_ext. intros a. exact (Hag a). }
      assert (pt_inst σ2 (pt_inst (λ a, if decide (a < m) then plist xs' a else τ a) f) =
              pt_inst (pclose (pt_inst σ2 <$> xs') m σ1) f) as E2.
      { rewrite pt_inst_comp. apply pt_inst_ext. intros a. unfold compose.
        destruct (decide (a < m)) as [Ha|Ha].
        - rewrite (pclose_lt _ m σ1 a Ha) by (by rewrite length_fmap). apply plist_fmap_lt. lia.
        - rewrite Hag, !pclose_ge by (try lia; try done; by rewrite length_fmap). done. }
      by rewrite E1, E2 in Hlt.
  Qed.

  (** The branch creates at a fresh root under (gen-new). E-Open adds
      the constraint C of the creation, and every model extends by
      [gen_new_ext]. *)
  Corollary prop7_new (EM : excluded_middle) Γ0 m H C xs' f :
    gen_new W (hc_open m H Γ0) C → length xs' = m →
    hold_at W (hc_open 1 C (hc_open m H Γ0)) (bcs_inst (λ a, pvar (a + m + 1)) H) xs' →
    slt W (hc_open 1 C (hc_open m H Γ0))
      (pt_inst (λ a, if decide (a < m) then plist xs' a else pvar (a + 1)) f) (pt_inst (pshift 1) f) →
    ∀ R σ0 xs, wranked R → wmodels R W → hsat R σ0 Γ0 → length xs = m →
      wholds R (bcs_inst σ0 H) xs → False.
  Proof.
    intros HG. apply (prop7 Γ0 m H _ (pshift 1)).
    intros R σ HR HW Hs.
    destruct (gen_new_ext EM R _ HR (gen_new_sem_of W R _ σ C Hwf HW Hs HG)) as (π & R' & HRR & Hw).
    exists R', (pclose [π] 1 σ). split_and!; [done| |].
    - apply hsat_open; [done|by eapply hsat_mono|done].
    - intros a. by apply pclose_shift.
  Qed.

  (** The branch creates at a field: the context stays. *)
  Corollary prop7_fld Γ0 m H xs' f :
    length xs' = m →
    hold_at W (hc_open m H Γ0) (bcs_inst (λ a, pvar (a + m)) H) xs' →
    slt W (hc_open m H Γ0) (pt_inst (λ a, if decide (a < m) then plist xs' a else pvar a) f) f →
    ∀ R σ0 xs, wranked R → wmodels R W → hsat R σ0 Γ0 → length xs = m →
      wholds R (bcs_inst σ0 H) xs → False.
  Proof.
    intros Hl HC Hd. apply (prop7 Γ0 m H (hc_open m H Γ0) pvar xs' f); [|done|done|by rewrite pt_inst_pvar].
    intros R σ HR HW Hs. exists R, σ. split_and!; [apply wext_refl|done|]. intros a. by rewrite pt_inst_pvar_at.
  Qed.
End prop7.

(** ** rx-chain

      grow = !(f = λw. let ⟨c, c′⟩ = new in
                       let ⟨d, d′⟩ = new in let ∗ = spawn (λ_. recvclose d′) in
                       let ∗ = close (send ⟨∗, d⟩) in
                       let ∗ = spawn (λ_. (force f) c′) in
                       let ∗ = close c in close w)
      main = let ⟨w, w′⟩ = new in let ∗ = spawn (λ_. close w′) in (force grow) w

    Each new is plain, so a derivation may create at a fresh root or at
    a field. *)

Definition rc_body : expr :=
  let_new (let_new
    (LetU (ESpawn (Lam (LetU (Var 0) (LetP (ERecv (Var 1)) (LetU (Var 1) (EClose (Var 0)))))))
    (LetU (EClose (ESend (Pair EUnit (Var 1))))
    (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 8)) (Var 4)))))
    (LetU (EClose (Var 4)) (EClose (Var 6))))))).

Definition rc_grow : expr := EBox (Lam rc_body).

Definition rc_main : expr :=
  let_new (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) (App (EForce rc_grow) (Var 1))).

(** ** A box called at a model

    A box typed under Γb0 with the constraint C and the parameter of U
    can be called at R when R models W and Γb0, C holds at an instance
    xs, and the parameter at xs holds an end at s ([box_P]). If every
    such call leads to a call at an extension whose end has its dual
    below s̄, no call exists ([box_P_never]). *)
Definition box_P (W : sworld) (Γb0 : hctx) (m : nat) (C : bcs) (U : ty) (R : world) (s : point) : Prop :=
  ∃ σ0 xs, wranked R ∧ wmodels R W ∧ hsat R σ0 Γb0 ∧ length xs = m ∧
    wholds R (bcs_inst σ0 C) xs ∧ PVpar R (plist xs) (erase (pinst_ty (pup m σ0) U)) (PE s).

Lemma box_P_never W Γb0 m C U :
  (∀ R s, box_P W Γb0 m C U R s → ∃ R' s', R ⊑ R' ∧ box_P W Γb0 m C U R' s' ∧ R' ⊢ s'‾ ≺ s‾) →
  ∀ R s, ¬ box_P W Γb0 m C U R s.
Proof.
  intros Hstep R s HP. refine (descent (λ R t, box_P W Γb0 m C U R t‾) _ R s‾ _); [|by rewrite pt_dual_dual].
  intros R1 t HP1. split; [by destruct HP1 as (? & ? & ? & _)|].
  destruct (Hstep R1 t‾ HP1) as (R2 & s2 & H12 & HP2 & Hlt).
  exists R2, s2‾. rewrite !pt_dual_dual in Hlt |- *. split_and!; done.
Qed.

(** The body of a box called at a model is typed at a model of its
    context, with the parameter at s and the box variable at the value
    of the box. *)
Lemma box_enter W N Γb0 Δ0 m k C ub cb U b R σ0 xs s : sworld_wf W → lenv_unl Δ0 →
  (∀ ss, length ss = k → sinsts N ss →
     typed W N ∅ (hc_open m C Γb0) (lenv_pinst (pshift m) (Some (TBox m k C ub cb U) :: Δ0))
       (∅, Some (rest_of ub)) (Lam b) (sinst_ty (slist ss) U) cb) →
  wmodels R W → hsat R σ0 Γb0 → length xs = m → wholds R (bcs_inst σ0 C) xs →
  PVpar R (plist xs) (erase (pinst_ty (pup m σ0) U)) (PE s) →
  ∃ Θ' Γ' Δ' F' T' c' σ', typed W N Θ' Γ' Δ' F' b T' c' ∧ hsat R σ' Γ' ∧
    PΔ R σ' Δ' (PE s .: bden σ0 (TBox m k C ub cb U) .: lden σ0 Δ0).
Proof.
  intros Hwf Hunl Hbody HW Hs Hl Hw Hp.
  pose proof (Hbody (repeat SEnd k) (repeat_length _ _) (sinsts_repeat_end _ _)) as Hb.
  assert (hsat R (pclose xs m σ0) (hc_open m C Γb0)) as Hsb by (by apply hsat_open).
  assert (PΔ R (pclose xs m σ0) (lenv_pinst (pshift m) (Some (TBox m k C ub cb U) :: Δ0))
    (bden σ0 (TBox m k C ub cb U) .: lden σ0 Δ0)) as HΔb.
  { apply PΔ_pinst. apply (PΔ_ext R σ0); [intros a; symmetry; apply (pclose_shift xs m σ0 Hl)|].
    apply PΔ_cons; [by apply PV_bden|]. by apply PΔ_lden. }
  assert (PVpar R (pclose xs m σ0) (sinst_ty (slist (repeat SEnd k)) U) (PE s)) as Hpar.
  { apply (PVpar_erase R _ U _ _ (erase_sinst _ _)). by apply PVpar_box_inst. }
  apply spo_abs in Hb.
  destruct (spo_sem W Hwf _ _ _ _ _ _ Hb R _ _ HW Hsb HΔb)
    as (Θ1 & Γ1 & Δ1 & F1 & T1 & σ1 & τ1 & (Θh & Δh & Tw & U1 & ub1 & lb1 & c1 & a1 & Hla & -> & He)
      & Hs1 & HΔ1 & _ & _ & _ & _ & Hp1).
  pose proof (Hp1 R (PE s) (wext_refl R) Hpar) as Hw1. simpl in Hw1.
  do 7 eexists. split_and!; [exact He|exact Hs1|]. apply PΔ_cons; [done|by eapply PΔ_lage].
Qed.

(** A closed term has only unlimited entries in its context. *)
Lemma closed_unl W N Θ Γ Δ F e T c : (∀ x, ¬ freevar x e) → typed W N Θ Γ Δ F e T c → lenv_unl Δ.
Proof.
  intros Hcl Ht. destruct (typed_tfacts _ _ _ _ _ _ _ _ _ Ht) as [_ [_ Hfv]].
  intros o Ho. apply list_elem_of_lookup in Ho as [j Hj].
  destruct o as [U|]; [|by left]. right. exists U. split; [done|].
  destruct (decide (unlimited U)) as [?|Hu]; [done|]. exfalso. exact (Hcl j (Hfv j U Hj Hu)).
Qed.

(** One round of grow. The body creates c at q and closes c while it
    holds w, which asks q ≺ s̄ ([close_PV]). Its child calls the box with
    c′ at q̄ ([child_step]). *)
Section rc.
  Context (W : sworld) (Hwf : sworld_wf W) (EM : excluded_middle) (n : nat).
  Context (Γb0 : hctx) (Δ0 : lenv) (m k : nat) (C : bcs) (ub : option point) (cb : fuel) (U : ty).
  Context (Hunl : lenv_unl Δ0).
  Context (Hbody : ∀ ss, length ss = k → sinsts (Some n) ss →
    typed W (Some n) ∅ (hc_open m C Γb0) (lenv_pinst (pshift m) (Some (TBox m k C ub cb U) :: Δ0))
      (∅, Some (rest_of ub)) (Lam rc_body) (sinst_ty (slist ss) U) cb).

  Lemma rc_step R s : box_P W Γb0 m C U R s →
    ∃ R' s', R ⊑ R' ∧ box_P W Γb0 m C U R' s' ∧ R' ⊢ s'‾ ≺ s‾.
  Proof.
    intros (σ0 & xs & HR & HW & Hs & Hl & Hw & Hp).
    destruct (box_enter W (Some n) Γb0 Δ0 m k C ub cb U _ R σ0 xs s Hwf Hunl Hbody HW Hs Hl Hw Hp)
      as (Θ1 & Γ1 & Δ1 & F1 & T1 & c1 & σ1 & He & Hs1 & HΔ1).
    unfold rc_body, let_new, ELet in He. simpl in He.
    destruct (letnew_step W Hwf EM n _ _ _ _ _ _ _ _ _ _ He HR HW Hs1 HΔ1)
      as (R1 & q & Θ2 & Γ2 & Δ2 & F2 & T2 & c2 & σ2 & HR1 & He2 & Hs2 & HΔ2).
    assert (wranked R1) as HR1' by (by apply (wext_ranked R R1)).
    assert (wmodels R1 W) as HW1 by (by eapply wmodels_mono).
    destruct (letnew_step W Hwf EM n _ _ _ _ _ _ _ _ _ _ He2 HR1' HW1 Hs2 HΔ2)
      as (R2 & r & Θ3 & Γ3 & Δ3 & F3 & T3 & c3 & σ3 & HR2 & He3 & Hs3 & HΔ3).
    assert (wmodels R2 W) as HW2 by (by eapply wmodels_mono).
    destruct (letu_split W Hwf _ _ _ _ _ _ _ _ _ _ _ _ He3 HW2 Hs3 HΔ3)
      as (_ & Γ4 & _ & _ & _ & Θ4 & Δ4 & F4 & T4 & c4 & σ4 & _ & He4 & Hs4 & _ & HΔ4).
    destruct (letu_split W Hwf _ _ _ _ _ _ _ _ _ _ _ _ He4 HW2 Hs4 HΔ4)
      as (_ & Γ5 & _ & _ & _ & Θ5 & Δ5 & F5 & T5 & c5 & σ5 & _ & He5 & Hs5 & _ & HΔ5).
    destruct (letu_split W Hwf _ _ _ _ _ _ _ _ _ _ _ _ He5 HW2 Hs5 HΔ5)
      as (Θ6 & Γ6 & Δ6 & F6 & c6 & Θ7 & Δ7 & F7 & T7 & c7 & σ6 & Hch & Hrd & Hs6 & HΔ6 & HΔ7).
    destruct (close_PV W Hwf _ _ _ _ _ 5 8 _ _ _ _ _ _ s Hrd ltac:(simpl; done) eq_refl HW2 Hs6 HΔ7)
      as (q' & Eq & Hqs). simpl in Eq. injection Eq as <-.
    destruct (child_step W Hwf _ _ _ _ _ 9 4 _ _ _ _ _ _ _ _ Hch HW2 Hs6 HΔ6 eq_refl) as (xs' & Hl' & Hw' & Hp').
    assert (R ⊑ R2) as HRR2 by (by eapply wext_trans).
    exists R2, q‾. split_and!; [done| |by rewrite pt_dual_dual].
    exists σ0, xs'. split_and!; [by apply (wext_ranked R R2 HRR2)|done|by eapply hsat_mono|done|done|done].
  Qed.

  (** The box can be called nowhere. *)
  Theorem rc_grow_no_model R s : ¬ box_P W Γb0 m C U R s.
  Proof. apply box_P_never, rc_step. Qed.
End rc.

Lemma rc_main_closed x : ¬ freevar x rc_main.
Proof. unfold rc_main, rc_grow, rc_body, let_new, ELet. simpl. lia. Qed.

(** rx-chain has no typing at any finite N, in any context that has a
    ranked model. Its main forces the box at the end w of a creation,
    which gives [box_P] at the point of w, and [rc_grow_no_model]
    refutes it. *)
Theorem rx_chain_rejected (EM : excluded_middle) n W Θ Γ Δ F T c :
  sworld_wf W → (∃ R σ, wranked R ∧ wmodels R W ∧ hsat R σ Γ) →
  ¬ typed W (Some n) Θ Γ Δ F rc_main T c.
Proof.
  intros Hwf (R & σ & HR & HW & Hs) Ht.
  pose proof (closed_unl _ _ _ _ _ _ _ _ _ rc_main_closed Ht) as Hunl.
  unfold rc_main, let_new, ELet in Ht. simpl in Ht.
  destruct (letnew_step W Hwf EM n _ _ _ _ _ _ _ _ _ _ Ht HR HW Hs (PΔ_lden R σ Δ Hunl))
    as (R1 & q & Θ1 & Γ1 & Δ1 & F1 & T1 & c1 & σ1 & HR1 & He1 & Hs1 & HΔ1).
  assert (wranked R1) as HR1' by (by apply (wext_ranked R R1)).
  assert (wmodels R1 W) as HW1 by (by eapply wmodels_mono).
  destruct (letu_split W Hwf _ _ _ _ _ _ _ _ _ _ _ _ He1 HW1 Hs1 HΔ1)
    as (_ & Γ2 & _ & _ & _ & Θ2 & Δ2 & F2 & T2 & c2 & σ2 & _ & Hap & Hs2 & _ & HΔ2).
  destruct (main_force_step W Hwf _ _ _ _ _ _ _ _ _ _ _ _ Hap HW1 Hs2 HΔ2)
    as (Γ0 & Δ0 & m & k & C & ub & cb & U & σ0 & xs & Hunl0 & Hbody & Hs0 & Hl & Hw & Hp).
  apply (rc_grow_no_model W Hwf EM n Γ0 Δ0 m k C ub cb U Hunl0 Hbody R1 q).
  by exists σ0, xs.
Qed.

(** The process of the one thread of rx-chain is not in the lock-free
    judgment. *)
Corollary rx_chain_proc_rejected (EM : excluded_middle) n η W Σ C0 T :
  ¬ ptyped (Some n) η W Σ (C0, {[+ rc_main +]}) T.
Proof.
  intros H. apply ptyped_one in H as (W' & ΘB & c & _ & _ & _ & _ & _ & _ & _ & _ & Ht & [Hwf Hwk]).
  destruct (wmodels_exists W' Hwf Hwk) as (R & HR & HW).
  refine (rx_chain_rejected EM n W' _ _ _ _ _ _ Hwf _ Ht).
  exists R, pvar. split_and!; [done|done|apply hsat_empty].
Qed.

(** ** Recursive fork-join

    The worker of examples/ForkJoin.v creates its two child channels at
    fields, spawns itself on their dual ends and closes c₁, c₂ and w.
    The close of c₁ asks the point q of c₁ below s̄, and the first child
    calls the box with the end at q̄. So the same descent rejects the
    program at every finite N, whereas [fjr_dftyped] types it at
    N = ∞. *)
Section fj.
  Context (W : sworld) (Hwf : sworld_wf W) (EM : excluded_middle) (n : nat).
  Context (Γb0 : hctx) (Δ0 : lenv) (m k : nat) (C : bcs) (ub : option point) (cb : fuel) (U : ty).
  Context (Hunl : lenv_unl Δ0).
  Context (Hbody : ∀ ss, length ss = k → sinsts (Some n) ss →
    typed W (Some n) ∅ (hc_open m C Γb0) (lenv_pinst (pshift m) (Some (TBox m k C ub cb U) :: Δ0))
      (∅, Some (rest_of ub)) (Lam wkr_body) (sinst_ty (slist ss) U) cb).

  Lemma fj_step R s : box_P W Γb0 m C U R s →
    ∃ R' s', R ⊑ R' ∧ box_P W Γb0 m C U R' s' ∧ R' ⊢ s'‾ ≺ s‾.
  Proof.
    intros (σ0 & xs & HR & HW & Hs & Hl & Hw & Hp).
    destruct (box_enter W (Some n) Γb0 Δ0 m k C ub cb U _ R σ0 xs s Hwf Hunl Hbody HW Hs Hl Hw Hp)
      as (Θ1 & Γ1 & Δ1 & F1 & T1 & c1 & σ1 & He & Hs1 & HΔ1).
    unfold wkr_body in He.
    destruct (letp_new_step W Hwf EM n _ _ _ _ _ _ _ _ _ _ He HR HW Hs1 HΔ1)
      as (R1 & q & Θ2 & Γ2 & Δ2 & F2 & T2 & c2 & σ2 & HR1 & He2 & Hs2 & HΔ2).
    assert (wranked R1) as HR1' by (by apply (wext_ranked R R1)).
    assert (wmodels R1 W) as HW1 by (by eapply wmodels_mono).
    destruct (letp_new_step W Hwf EM n _ _ _ _ _ _ _ _ _ _ He2 HR1' HW1 Hs2 HΔ2)
      as (R2 & r & Θ3 & Γ3 & Δ3 & F3 & T3 & c3 & σ3 & HR2 & He3 & Hs3 & HΔ3).
    assert (wmodels R2 W) as HW2 by (by eapply wmodels_mono).
    destruct (letu_split W Hwf _ _ _ _ _ _ _ _ _ _ _ _ He3 HW2 Hs3 HΔ3)
      as (Θ4 & Γ4 & Δ4 & F4 & c4 & Θ5 & Δ5 & F5 & T5 & c5 & σ4 & Hch & He4 & Hs4 & HΔ4 & HΔ5).
    destruct (letu_split W Hwf _ _ _ _ _ _ _ _ _ _ _ _ He4 HW2 Hs4 HΔ5)
      as (_ & Γ6 & _ & _ & _ & Θ6 & Δ6 & F6 & T6 & c6 & σ6 & _ & Hrd & Hs6 & _ & HΔ6).
    destruct (close_PV W Hwf _ _ _ _ _ 3 4 _ _ _ _ _ _ s Hrd ltac:(simpl; auto) eq_refl HW2 Hs6 HΔ6)
      as (q' & Eq & Hqs). simpl in Eq. injection Eq as <-.
    destruct (child_step W Hwf _ _ _ _ _ 5 2 _ _ _ _ _ _ _ _ Hch HW2 Hs4 HΔ4 eq_refl) as (xs' & Hl' & Hw' & Hp').
    assert (R ⊑ R2) as HRR2 by (by eapply wext_trans).
    exists R2, q‾. split_and!; [done| |by rewrite pt_dual_dual].
    exists σ0, xs'. split_and!; [by apply (wext_ranked R R2 HRR2)|done|by eapply hsat_mono|done|done|done].
  Qed.

  Theorem wkr_no_model R s : ¬ box_P W Γb0 m C U R s.
  Proof. apply box_P_never, fj_step. Qed.
End fj.

Lemma fjr_main_closed x : ¬ freevar x fjr_main.
Proof. unfold fjr_main, wkr, wkr_body, let_new, ELet. simpl. lia. Qed.

(** The recursive fork-join worker has no typing at any finite N, in
    any context that has a ranked model. *)
Theorem fjr_lf_rejected (EM : excluded_middle) n W Θ Γ Δ F T c :
  sworld_wf W → (∃ R σ, wranked R ∧ wmodels R W ∧ hsat R σ Γ) →
  ¬ typed W (Some n) Θ Γ Δ F fjr_main T c.
Proof.
  intros Hwf (R & σ & HR & HW & Hs) Ht.
  pose proof (closed_unl _ _ _ _ _ _ _ _ _ fjr_main_closed Ht) as Hunl.
  unfold fjr_main, let_new, ELet in Ht. simpl in Ht.
  destruct (letnew_step W Hwf EM n _ _ _ _ _ _ _ _ _ _ Ht HR HW Hs (PΔ_lden R σ Δ Hunl))
    as (R1 & q & Θ1 & Γ1 & Δ1 & F1 & T1 & c1 & σ1 & HR1 & He1 & Hs1 & HΔ1).
  assert (wmodels R1 W) as HW1 by (by eapply wmodels_mono).
  destruct (letu_split W Hwf _ _ _ _ _ _ _ _ _ _ _ _ He1 HW1 Hs1 HΔ1)
    as (Θ2 & Γ2 & Δ2 & F2 & c2 & _ & _ & _ & _ & _ & σ2 & Hch & _ & Hs2 & HΔ2 & _).
  destruct (spawn_lam_step W Hwf _ _ _ _ _ _ _ _ _ _ _ Hch HW1 Hs2 HΔ2)
    as (Θ3 & Γ3 & Δ3 & F3 & U3 & c3 & σ3 & Hc3 & Hs3 & HΔ3).
  destruct (letu_split W Hwf _ _ _ _ _ _ _ _ _ _ _ _ Hc3 HW1 Hs3 HΔ3)
    as (_ & Γ4 & _ & _ & _ & Θ4 & Δ4 & F4 & T4 & c4 & σ4 & _ & Hap & Hs4 & _ & HΔ4).
  destruct (main_force_step W Hwf _ _ _ _ _ _ _ _ _ _ _ _ Hap HW1 Hs4 HΔ4)
    as (Γ0 & Δ0 & m & k & C & ub & cb & U & σ0 & xs & Hunl0 & Hbody & Hs0 & Hl & Hw & Hp).
  apply (wkr_no_model W Hwf EM n Γ0 Δ0 m k C ub cb U Hunl0 Hbody R1 q‾).
  exists σ0, xs. split_and!; [by apply (wext_ranked R R1)|done|done|done|done|done].
Qed.

Corollary fjr_lf_proc_rejected (EM : excluded_middle) n η W Σ C0 T :
  ¬ ptyped (Some n) η W Σ (C0, {[+ fjr_main +]}) T.
Proof.
  intros H. apply ptyped_one in H as (W' & ΘB & c & _ & _ & _ & _ & _ & _ & _ & _ & Ht & [Hwf Hwk]).
  destruct (wmodels_exists W' Hwf Hwk) as (R & HR & HW).
  refine (fjr_lf_rejected EM n W' _ _ _ _ _ _ Hwf _ Ht).
  exists R, pvar. split_and!; [done|done|apply hsat_empty].
Qed.
