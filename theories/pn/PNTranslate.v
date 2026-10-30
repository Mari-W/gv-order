(** * From derivations of Padovani and Novara to the static system

    A derivation Γ ⊢ e : t & τ ⇝ e′ becomes a derivation of [typed] at
    the level world [Wpn] ([pn_translate]). The lemma holds at every
    anchor B whose facts the context Ψ provides ([good]), at every offset
    k (the shift ⇑ᵏ of the whole derivation), and at every frame F above
    the upper point of τ, as the PGV lemma reads its bound (PGVTranslate.v).

    The static system has no renaming lemma, and the body of a box sees
    the box itself at index 0. The lemma therefore also quantifies over
    the places [ins] where the environment Δ has extra unlimited or
    spent entries, and it types e′ renamed past them ([erel]).

    [soundness] then makes every closed program of type unit deadlock
    free ([pn_deadlock_free]). *)

From stdpp Require Import base gmap numbers.
From LRGV Require Export pn.PNWorld.

Set Default Proof Using "All".

(** ** Renaming past inserted entries *)

Fixpoint ren_of (ins : list bool) (x : nat) : nat :=
  match ins with
  | [] => x
  | false :: ins => match x with 0 => 0 | S x => S (ren_of ins x) end
  | true :: ins => S (ren_of ins x)
  end.

Lemma ren_of_inj ins x y : ren_of ins x = ren_of ins y → x = y.
Proof.
  revert x y. induction ins as [|[] ins IH]; intros x y; simpl; [done| |].
  - intros [=]. by apply IH.
  - destruct x, y; simpl; try done. intros [=]. f_equal. by apply IH.
Qed.

Lemma rename_id e : rename (λ x, x) e = e.
Proof.
  induction e; simpl; f_equal; try done;
    (etransitivity; [|eassumption]); apply rename_ext; by intros [|[|x]].
Qed.

Lemma ren_up ins e : rename (upren (ren_of ins)) e = rename (ren_of (false :: ins)) e.
Proof. apply rename_ext. by intros [|x]. Qed.

Lemma ren_up2 ins e :
  rename (upren (upren (ren_of ins))) e = rename (ren_of (false :: false :: ins)) e.
Proof. apply rename_ext. by intros [|[|x]]. Qed.

Lemma ren_box ins e :
  rename (upren (upren (ren_of ins))) (rename (upren S) e)
  = rename (ren_of (false :: true :: ins)) e.
Proof. rewrite rename_rename. apply rename_ext. by intros [|x]. Qed.

(** ** Linear environments *)

Section lenv.
  Lemma unl_wk Δ : lenv_unl Δ → lenv_wk (lenv_nones Δ) Δ.
  Proof.
    induction Δ as [|o Δ IH]; intros H; simpl; [constructor|].
    destruct (H o) as [->|(T & -> & HT)]; [by left| |].
    - constructor. apply IH. intros o' Ho'. apply H. by right.
    - apply lwk_drop; [done|]. apply IH. intros o' Ho'. apply H. by right.
  Qed.

  Lemma unl_heads Δ : lenv_unl Δ → lenv_heads Δ = ∅.
  Proof.
    induction Δ as [|o Δ IH]; intros H; simpl; [done|].
    destruct (H o) as [->|(T & -> & HT)]; [by left| |].
    - apply IH. intros o' Ho'. apply H. by right.
    - destruct T; try done. simpl. rewrite IH; [set_solver|]. intros o' Ho'. apply H. by right.
  Qed.

  Lemma unl_pinst σ Δ : lenv_unl Δ → lenv_unl (lenv_pinst σ Δ).
  Proof.
    intros H o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
    destruct (H o' Ho') as [->|(T & -> & HT)]; [by left|right].
    eexists. split; [done|]. by apply unlimited_pinst.
  Qed.

  Lemma nones_heads Δ : lenv_heads (lenv_nones Δ) = ∅.
  Proof. induction Δ; simpl; done. Qed.

  Lemma nones_unl Δ : lenv_unl (lenv_nones Δ).
  Proof. intros o Ho. left. by apply lenv_empty_nones in Ho. Qed.

  Lemma nones_nones Δ : lenv_nones (lenv_nones Δ) = lenv_nones Δ.
  Proof. induction Δ; simpl; congruence. Qed.

  Lemma lenv_split_nones_r Δ : lenv_split Δ Δ (lenv_nones Δ).
  Proof. apply lenv_split_comm, lenv_split_nones_l. Qed.

  (** A variable whose other entries are unlimited. *)
  Lemma lonly_wk_unl x Δ :
    (∀ y T, y ≠ x → Δ !! y = Some (Some T) → unlimited T) → lenv_wk (lonly x Δ) Δ.
  Proof.
    revert x. induction Δ as [|o Δ IH]; intros [|x] H; simpl; [constructor|constructor| |].
    - constructor. apply unl_wk. intros o' Ho'. apply list_elem_of_lookup_1 in Ho' as [y Hy].
      destruct o' as [T|]; [|by left]. right. exists T. split; [done|]. by apply (H (S y)).
    - destruct o as [T|].
      + apply lwk_drop; [by apply (H 0)|]. apply IH. intros y T' Hy HyT. apply (H (S y)); [lia|done].
      + constructor. apply IH. intros y T' Hy HyT. apply (H (S y)); [lia|done].
  Qed.
End lenv.

Section rules.
  Context (W : world) (HW : world_wf W).

  Lemma tv_var_unl Φ Ψ Δ F x T :
    Δ !! x = Some (Some T) → (∀ y T', y ≠ x → Δ !! y = Some (Some T') → unlimited T') →
    typed W Φ Ψ ∅ Δ F (Var x) T.
  Proof. intros H1 H2. eapply t_wk; [by apply lonly_wk_unl|]. apply t_var. by apply lonly_only. Qed.

  Lemma tv_unit_unl Φ Ψ Δ F : lenv_unl Δ → typed W Φ Ψ ∅ Δ F EUnit TUnit.
  Proof. intros H. eapply t_wk; [by apply unl_wk|]. apply t_unit, lenv_empty_nones. Qed.

  (** E-Exp for a closed constraint. *)
  Lemma tv_box Φ Ψ Δ F e m C ub T :
    lenv_unl Δ → bc_env C = [] →
    (∀ φ, φ ∉ dom Φ →
      typed W (<[φ := ub]> (fhyps_pinst (pshift m) Φ)) (hyps_inst (pshift m) Ψ ++ [(C, ids m)]) ∅
        (lenv_pinst (pshift m) (Some (TBox m C (TLolli ub None TUnit T)) :: Δ)) (∅, Some φ) e T) →
    typed W Φ Ψ ∅ Δ F (EBox e) (TBox m C (TLolli ub None TUnit T)).
  Proof.
    intros HΔ HC H. set (φ := fresh (dom Φ)). apply (t_box W Φ Ψ Δ F e m C ub T φ); [done|apply is_fresh|].
    assert (bcs_inst (pshift m) C = C) as -> by (destruct C; simpl in *; by subst).
    apply H, is_fresh.
  Qed.

  Lemma tv_unitv Φ Ψ Δ F : lenv_unl Δ → typed W Φ Ψ ∅ Δ F unitv U.
  Proof.
    intros HΔ. apply tv_box; [done|done|]. intros φ _. apply tv_unit_unl.
    apply unl_pinst. intros o [->|Ho]%elem_of_cons; [right; by eexists|by apply HΔ].
  Qed.

  (** A closed function applied to an argument. *)
  Lemma tv_app_closed Φ Ψ Δ F f e ub T U' :
    typed W Φ Ψ ∅ (lenv_nones Δ) (sf_union F (lenv_heads Δ)) f (TLolli ub None T U') →
    typed W Φ Ψ ∅ Δ F e T →
    ub_below_s W Ψ Φ ub F →
    typed W Φ Ψ ∅ Δ F (App f e) U'.
  Proof.
    intros Hf He Hub. eapply (t_app W Φ Ψ ∅ ∅ ∅ Δ (lenv_nones Δ) Δ F _ _ ub None).
    - by apply comp0.
    - apply lenv_split_nones_l.
    - done.
    - by rewrite (tenv_heads0 W HW), union_empty_l_L.
    - destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L.
  Qed.

  Lemma ubs_fresh Ψ Φ φ u : ub_below_s W Ψ (<[φ := u]> Φ) u (∅, Some φ).
  Proof.
    destruct u as [u|]; [|done]. split; simpl; [set_solver|].
    intros φ' [=<-]. apply (fl_v (FCtx _ _ _)). simpl. by rewrite lookup_insert_eq.
  Qed.

  Lemma ubs_union Ψ Φ u F X :
    ub_below_s W Ψ Φ u F → (∀ x, u = Some x → ∀ h, h ∈ X → slt W Ψ x h) →
    ub_below_s W Ψ Φ u (sf_union F X).
  Proof.
    destruct u as [x|]; [|done]. intros [H1 H2] HX. split; [|done]. simpl.
    intros y [Hy|Hy]%elem_of_union; [by apply H1|]. apply fl_points. by apply (HX x).
  Qed.

  Lemma ubs_lower Ψ Φ a b F :
    (∀ x, a = Some x → ∃ y, b = Some y ∧ sle W Ψ x y) →
    ub_below_s W Ψ Φ b F → ub_below_s W Ψ Φ a F.
  Proof.
    intros Hab Hb. destruct a as [x|]; [|done].
    destruct (Hab x eq_refl) as (y & -> & Hxy). destruct Hb as [H1 H2].
    destruct Hxy as [Hxy|Hxy]; split.
    - intros z Hz. eapply (fl_eql (FCtx W Ψ Φ)); [exact Hxy|by apply H1].
    - intros φ Hφ. eapply (fl_eql (FCtx W Ψ Φ)); [exact Hxy|by apply H2].
    - intros z Hz. eapply (fl_trans (FCtx W Ψ Φ)); [apply fl_points; exact Hxy|by apply H1].
    - intros φ Hφ. eapply (fl_trans (FCtx W Ψ Φ)); [apply fl_points; exact Hxy|by apply H2].
  Qed.

  (** The upper point of a frame variable's own hypothesis. *)
  Lemma ubs_hyp Ψ Φ φ x u :
    Φ !! φ = Some (Some u) → sle W Ψ x u → ub_below_s W Ψ Φ (Some x) (∅, Some φ).
  Proof.
    intros Hφ Hx. apply ub_below_s_intro; [set_solver|]. by exists u.
  Qed.
End rules.

(** ** Levels *)

Lemma lvl_le_refl a : lvl_le a a.
Proof. destruct a; simpl; lia. Qed.
Lemma lvl_le_max_l a b : lvl_le a (lvl_max a b).
Proof. destruct a, b; simpl; lia. Qed.
Lemma lvl_le_max_r a b : lvl_le b (lvl_max a b).
Proof. destruct a, b; simpl; lia. Qed.
Lemma lvl_le_trans a b c : lvl_le a b → lvl_le b c → lvl_le a c.
Proof. destruct a, b, c; simpl; lia. Qed.

Lemma env_lev_le Γ t z :
  Some t ∈ Γ → tlev t = Some z → ∃ z0, env_lev Γ = Some z0 ∧ (z0 ≤ z)%Z.
Proof.
  induction Γ as [|o Γ IH]; intros Ht Hz; [by apply elem_of_nil in Ht|].
  apply elem_of_cons in Ht as [<-|Ht]; simpl.
  - rewrite Hz. destruct (env_lev Γ); simpl; eexists; split; [done|lia|done|lia].
  - destruct (IH Ht Hz) as (z0 & E & Hle). destruct o as [t'|]; [|eauto].
    rewrite E. destruct (tlev t'); simpl; eexists; split; [done|lia|done|lia].
Qed.

Lemma env_lev_none Γ : env_lev Γ = None → penv_un Γ.
Proof.
  intros H t Ht. unfold un. destruct (tlev t) as [z|] eqn:E; [|done].
  destruct (env_lev_le Γ t z Ht E) as (z0 & E' & _). congruence.
Qed.

(** ** Environments up to inserted entries *)

Inductive erel (B : point) (k : Z) : list bool → penv → lenv → Prop :=
  | er_nil : erel B k [] [] []
  | er_keep o ins Γ Δ : erel B k ins Γ Δ → erel B k (false :: ins) (o :: Γ) (fmap (trz B k) o :: Δ)
  | er_skip o ins Γ Δ :
      (o = None ∨ ∃ T, o = Some T ∧ unlimited T) →
      erel B k ins Γ Δ → erel B k (true :: ins) Γ (o :: Δ).

Section erel.
  Context (B : point) (k : Z).

  Lemma erel_split ins Γ Δ Γ1 Γ2 :
    erel B k ins Γ Δ → pn_split Γ Γ1 Γ2 →
    ∃ Δ1 Δ2, lenv_split Δ Δ1 Δ2 ∧ erel B k ins Γ1 Δ1 ∧ erel B k ins Γ2 Δ2.
  Proof.
    intros H. revert Γ1 Γ2. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; intros Γ1 Γ2 Hs.
    - inversion Hs; subst. exists [], []. split_and!; constructor.
    - inversion Hs as [|? ? ? Hs'|t ? ? ? Hs'|t ? ? ? Hs'|t ? ? ? Ht Hs']; subst;
        destruct (IH _ _ Hs') as (Δ1 & Δ2 & Hd & H1 & H2).
      + exists (None :: Δ1), (None :: Δ2). split_and!; [by constructor|apply (er_keep _ _ None)..]; done.
      + exists (Some (trz B k t) :: Δ1), (None :: Δ2). split_and!; [by constructor
          |apply (er_keep _ _ (Some t))|apply (er_keep _ _ None)]; done.
      + exists (None :: Δ1), (Some (trz B k t) :: Δ2). split_and!; [by constructor
          |apply (er_keep _ _ None)|apply (er_keep _ _ (Some t))]; done.
      + exists (Some (trz B k t) :: Δ1), (Some (trz B k t) :: Δ2). split_and!;
          [apply lsplit_unl; [by apply trz_unlimited|done]|apply (er_keep _ _ (Some t))..]; done.
    - destruct (IH _ _ Hs) as (Δ1 & Δ2 & Hd & H1 & H2). exists (o :: Δ1), (o :: Δ2).
      split_and!; [|by constructor..].
      destruct Ho as [->|(T & -> & HT)]; [by constructor|by apply lsplit_unl].
  Qed.

  Lemma erel_lookup ins Γ Δ x o :
    erel B k ins Γ Δ → Γ !! x = Some o → Δ !! ren_of ins x = Some (fmap (trz B k) o).
  Proof.
    intros H. revert x. induction H as [|o' ins Γ Δ H IH|o' ins Γ Δ Ho H IH]; intros x Hx; simpl.
    - done.
    - destruct x; simpl in *; [by simplify_eq|by apply IH].
    - by apply IH.
  Qed.

  Lemma erel_inv ins Γ Δ y T :
    erel B k ins Γ Δ → Δ !! y = Some (Some T) →
    (∃ x t, y = ren_of ins x ∧ Γ !! x = Some (Some t) ∧ T = trz B k t) ∨ unlimited T.
  Proof.
    intros H. revert y. induction H as [|o' ins Γ Δ H IH|o' ins Γ Δ Ho H IH]; intros y Hy; simpl.
    - done.
    - destruct y; simpl in *.
      + destruct o' as [t|]; simpl in Hy; simplify_eq. left. by exists 0, t.
      + destruct (IH y Hy) as [(x & t & -> & Hx & ->)|]; [|by right]. left. by exists (S x), t.
    - destruct y; simpl in *.
      + simplify_eq. destruct Ho as [|(T' & ? & ?)]; [done|]. simplify_eq. by right.
      + destruct (IH y Hy) as [(x & t & -> & Hx & ->)|]; [|by right]. left. by exists x, t.
  Qed.

  Lemma erel_var ins Γ Δ W Φ Ψ F x t :
    world_wf W → erel B k ins Γ Δ → penv_only_un Γ x t →
    typed W Φ Ψ ∅ Δ F (Var (ren_of ins x)) (trz B k t).
  Proof.
    intros HW H [Hx Hun]. apply tv_var_unl; [done|by apply (erel_lookup _ Γ _ _ (Some t))|].
    intros y T Hy HyT. destruct (erel_inv _ _ _ _ _ H HyT) as [(x' & t' & -> & Hx' & ->)|]; [|done].
    apply trz_unlimited, (Hun x'); [|done]. intros ->. done.
  Qed.

  Lemma erel_unl ins Γ Δ : erel B k ins Γ Δ → penv_un Γ → lenv_unl Δ.
  Proof.
    intros H HΓ o Ho. apply list_elem_of_lookup_1 in Ho as [y Hy].
    destruct o as [T|]; [|by left]. right. exists T. split; [done|].
    destruct (erel_inv _ _ _ _ _ H Hy) as [(x & t & -> & Hx & ->)|]; [|done].
    apply trz_unlimited, HΓ. by eapply list_elem_of_lookup_2.
  Qed.

  Lemma erel_heads ins Γ Δ h :
    erel B k ins Γ Δ → h ∈ lenv_heads Δ → ∃ t, Some t ∈ Γ ∧ h ∈ heads (trz B k t).
  Proof.
    intros H. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; simpl; intros Hh.
    - set_solver.
    - destruct o as [t|]; simpl in Hh.
      + apply elem_of_union in Hh as [Hh|Hh]; [exists t; split; [by left|done]|].
        destruct (IH Hh) as (t' & ? & ?). exists t'. split; [by right|done].
      + destruct (IH Hh) as (t' & ? & ?). exists t'. split; [by right|done].
    - destruct Ho as [->|(T & -> & HT)]; simpl in Hh; [by apply IH|].
      destruct T; try done. simpl in Hh. apply IH. set_solver.
  Qed.

  Lemma erel_pinst ins Γ Δ σ B' k' :
    erel B k ins Γ Δ → penv_un Γ → erel B' k' ins Γ (lenv_pinst σ Δ).
  Proof.
    intros H. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; intros HΓ; simpl.
    - constructor.
    - assert (penv_un Γ) as HΓ' by (intros t Ht; apply HΓ; by right).
      destruct o as [t|]; simpl.
      + rewrite trz_pinst, (trz_un _ B' _ k'); [|apply HΓ; by left].
        apply (er_keep _ _ (Some t)). by apply IH.
      + apply (er_keep _ _ None). by apply IH.
    - apply er_skip; [|by apply IH]. destruct Ho as [->|(T & -> & HT)]; [by left|right].
      eexists. split; [done|]. by apply unlimited_pinst.
  Qed.
End erel.

Section heads.
  Context (Ψ : hyps) (B : point) (HB : good Ψ B) (k : Z).

  Lemma env_hi_below ins Γ Δ τ x h :
    erel B k ins Γ Δ → lvl_lt τ (olvl (env_lev Γ)) → hiz B k τ = Some x →
    h ∈ lenv_heads Δ → slt Wpn Ψ x h.
  Proof.
    intros H Hτ Hx Hh. destruct (erel_heads _ _ _ _ _ _ H Hh) as (t & Ht & Hh').
    destruct (tlev t) as [z|] eqn:Ez; [|by rewrite heads_un in Hh'].
    destruct (env_lev_le Γ t z Ht Ez) as (z0 & E0 & Hle). rewrite E0 in Hτ.
    eapply (hi_below Ψ B HB k τ (z0 + k)); [|done|].
    - by replace (z0 + k - k)%Z with z0 by lia.
    - apply (hd_at_mono Ψ B HB (z + k)); [lia|by apply (heads_trz Ψ B HB k t z)].
  Qed.

  Lemma env_lo_below ins Γ Δ z0 h :
    erel B k ins Γ Δ → env_lev Γ = Some z0 → h ∈ lenv_heads Δ → sle Wpn Ψ (loz B k z0) h.
  Proof.
    intros H E0 Hh. destruct (erel_heads _ _ _ _ _ _ H Hh) as (t & Ht & Hh').
    destruct (tlev t) as [z|] eqn:Ez; [|by rewrite heads_un in Hh'].
    destruct (env_lev_le Γ t z Ht Ez) as (z0' & E0' & Hle). rewrite E0 in E0'. injection E0' as <-.
    apply (lo_below Ψ B HB). apply (hd_at_mono Ψ B HB (z + k)); [lia|by apply (heads_trz Ψ B HB k t z)].
  Qed.

  Lemma ubs_lvl Φ a b F :
    lvl_le a b → ub_below_s Wpn Ψ Φ (hiz B k b) F → ub_below_s Wpn Ψ Φ (hiz B k a) F.
  Proof.
    intros Hab. apply (ubs_lower Wpn Wpn_wf). intros x Hx. by apply (hiz_mono Ψ B HB k a b).
  Qed.
End heads.

Lemma sf_union_empty F : sf_union F ∅ = F.
Proof. destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L. Qed.

(** ** Scoping and empty environments *)

Lemma pscoped_trz t : ∀ j B k, pt_scoped j B → pscoped j (trz B k t).
Proof.
  assert (∀ j B r, pt_scoped j B → pt_scoped j (rpt B r)) as Hr by done.
  assert (∀ j, pt_scoped j proot) as Hp by (intros j a Ha; done).
  induction t as [| t1 IH1 t2 IH2 | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros j B k HB;
    simpl.
  - split; [unfold bcs_scoped; simpl; constructor|]. repeat split.
  - split; [unfold bcs_scoped; simpl; constructor|]. split_and!; try done; [apply IH1|apply IH2]; apply Hp.
  - by apply Hr.
  - by apply Hr.
  - by apply IH.
  - destruct r as [r|]; simpl.
    + split_and!; [destruct σ; simpl; try done; by apply Hr|by apply Hr|by apply IH1|by apply IH2].
    + split; [unfold bcs_scoped; simpl; constructor|]. split_and!; try done.
      * destruct σ; simpl; try done; intros a Ha; simpl in Ha; injection Ha as <-; lia.
      * apply IH1. intros a Ha. injection Ha as <-. lia.
      * apply IH2. intros a Ha. injection Ha as <-. lia.
Qed.

Lemma empty_heads Δ : lenv_empty Δ → lenv_heads Δ = ∅.
Proof. intros H. apply unl_heads. intros o Ho. left. by apply H. Qed.

Lemma empty_lookup Δ y T : lenv_empty Δ → Δ !! y = Some (Some T) → False.
Proof. intros H Hy. apply list_elem_of_lookup_2 in Hy. by apply H in Hy. Qed.

Lemma lenv_split_empty' Δ : lenv_empty Δ → lenv_split Δ Δ Δ.
Proof.
  induction Δ as [|o Δ IH]; intros H; [constructor|].
  rewrite (H o) by set_solver. constructor. apply IH. intros o' Ho'. apply H. set_solver.
Qed.

Lemma empty_unl Δ : lenv_empty Δ → lenv_unl Δ.
Proof. intros H o Ho. left. by apply H. Qed.

Ltac var_others HΔ :=
  let y := fresh "y" in let T := fresh "T" in let Hne := fresh in let Hy := fresh in
  intros y T Hne Hy; destruct y as [|[|y]]; simpl in Hy; try done;
  exfalso; by eapply empty_lookup; [exact HΔ|exact Hy].

(** ** The terms of the translation *)

Section terms.
  Context (Ψ : hyps) (B : point) (HB : good Ψ B) (k : Z).
  Abbreviation W := Wpn.

  Definition chx (t : pty) (n : Z) : point := rpt B (RCh (PChan true (lshift k t) (n + k))).

  Lemma clev_chx t n : clev (PChan true (lshift k t) (n + k)) = Some (n + k)%Z.
  Proof. done. Qed.

  (** A payload of fragment v1 against the payload of send and recv. *)
  Lemma pay_conv t n :
    payok t → lvl_lt (LZ n) (olvl (tlev t)) →
    steq W Ψ (trz B k t) (payload_at (pbind t) (ppay t) (chx t n)) ∧
    steq W Ψ (payload_at (pbind t) (ppay t) (chx t n)) (trz B k t) ∧
    (∀ h, h ∈ heads (payload_at (pbind t) (ppay t) (chx t n)) →
       slt W Ψ (chx t n) h ∧ slt W Ψ (pt_shift 1 (chx t n)) h) ∧
    pscoped (pbind t) (ppay t).
  Proof.
    intros Hok Hn. unfold pbind, ppay. destruct (chanlike t) eqn:Ec.
    - destruct (chres_chanlike k t Ec) as [c' Hc']. rewrite (trz_chanlike B k t c' Hc').
      assert (payload_at 1 (TSess (sess t) (pvar 0)) (chx t n) = TSess (sess t) (pt_slot (chx t n) 0))
        as -> by (unfold payload_at, ty_inst; simpl; by rewrite pt_inst_pvar_at).
      assert (cpay (PChan true (lshift k t) (n + k)) = Some c') as Hp.
      { simpl. rewrite chres_lshift. by replace (0 + k)%Z with k by lia. }
      pose proof (pay_eq Ψ B HB _ _ Hp) as He.
      destruct (chres_lev k t c' Hc') as (z & Hz & Hlc). rewrite Hz in Hn. simpl in Hn.
      split_and!.
      + split; [by apply se_sym|apply seq_refl].
      + split; [done|apply seq_refl].
      + intros h Hh. simpl in Hh. apply elem_of_singleton in Hh as ->.
        apply (ch_below_pay Ψ B HB _ c' (n + k) (z + k)); [done|done|done|lia].
      + simpl. intros a Ha. injection Ha as <-. lia.
    - destruct Hok as [Hok|Hun]; [congruence|]. pose proof Hun as Hb. apply un_b_un in Hb. rewrite Hb.
      assert (payload_at 0 (trz proot 0 t) (chx t n) = trz B k t) as ->.
      { unfold payload_at, ty_inst. rewrite trz_pinst, (pt_inst_const _ proot 0) by done.
        by apply trz_un. }
      split_and!; [apply teq_steq, teq_refl|apply teq_steq, teq_refl| |].
      + intros h Hh. by rewrite heads_un in Hh.
      + apply pscoped_trz. intros a Ha. done.
  Qed.

  Lemma send_tr_typed Φ Δ0 F t n :
    lenv_empty Δ0 → payok t → lvl_lt (LZ n) (olvl (tlev t)) →
    typed W Φ Ψ ∅ Δ0 F send_tr
      (TLolli None None (trz B k (PChan false t n))
         (TLolli (hiz B k (LZ n)) (Some (loz B k n)) (trz B k t) U)).
  Proof.
    intros HΔ Hok Hn. pose proof Wpn_wf as HW.
    destruct (pay_conv t n Hok Hn) as (Hc1 & _ & Hh & Hs).
    set (x := chx t n). set (φ1 := fresh (dom Φ)).
    apply (t_lam W Φ Ψ ∅ Δ0 F _ _ _ None None φ1); [apply is_fresh| |].
    { simpl. by rewrite (tenv_heads0 W HW), empty_heads, union_empty_l_L. }
    set (Φ1 := <[φ1 := None]> Φ). set (φ2 := fresh (dom Φ1)).
    apply (t_lam W Φ1 Ψ ∅ _ _ _ _ _ (hiz B k (LZ n)) (Some (loz B k n)) φ2); [apply is_fresh| |].
    { simpl. rewrite (tenv_heads0 W HW), empty_heads, union_empty_l_L, union_empty_r_L by done.
      intros y Hy. apply elem_of_singleton in Hy as ->. apply (lo_below Ψ B HB).
      split; [done|right]. unfold x, chx. rewrite (den_ch0 Ψ B HB). simpl. lia. }
    set (Φ2 := <[φ2 := hiz B k (LZ n)]> Φ1).
    assert (Φ2 !! φ2 = Some (Some (rpt B (RHi (n + k))))) as Hφ2 by (unfold Φ2; by rewrite lookup_insert_eq).
    set (E := Some (trz B k t) :: Some (trz B k (PChan false t n)) :: Δ0).
    eapply (t_letu W Φ2 Ψ ∅ ∅ ∅ E E (lenv_nones E)); [by apply comp0|apply lenv_split_nones_r| |].
    2:{ apply tv_unitv; [done|apply nones_unl]. }
    rewrite (tenv_heads0 W HW), nones_heads, union_empty_l_L.
    set (Fr := sf_union (∅, Some φ2) ∅).
    assert (∀ z, slt W Ψ z (rpt B (RHi (n + k))) → ub_below_s W Ψ Φ2 (Some z) Fr) as Hub.
    { intros z Hz. apply ub_below_s_intro; [unfold Fr; simpl; set_solver|]. exists (rpt B (RHi (n + k))).
      split; [done|by right]. }
    eapply (t_app W Φ2 Ψ ∅ ∅ ∅ E (lenv_nones E) E Fr _ _ (Some (pt_shift 1 x)) None).
    { by apply comp0. } { apply lenv_split_nones_l. }
    { apply Hub. apply (ch1_below_hi Ψ B HB). apply clev_chx. }
    { apply t_konst; [apply lenv_empty_nones|apply KTClos|done]. }
    rewrite sf_union_empty.
    eapply (t_app W Φ2 Ψ ∅ ∅ ∅ E (lenv_nones E) E Fr _ _ (Some x) None
              (TProd (payload_at (pbind t) (ppay t) x) (TSess (SSnd (pbind t) (ppay t) SEnd) x))).
    { by apply comp0. } { apply lenv_split_nones_l. }
    { apply Hub. apply (ch_below_hi Ψ B HB). apply clev_chx. }
    { apply t_konst; [apply lenv_empty_nones| |done]. apply (KTSend _ _ _ (pbind t) (ppay t) SEnd x).
      intros h' Hh'. by apply Hh. }
    rewrite sf_union_empty.
    eapply (t_pair W Φ2 Ψ ∅ ∅ ∅ E (Some (trz B k t) :: None :: Δ0)
              (None :: Some (trz B k (PChan false t n)) :: Δ0)); [by apply comp0| | |].
    { constructor. constructor. by apply lenv_split_empty'. }
    - eapply t_conv; [exact Hc1|]. apply tv_var_unl; [done|done|var_others HΔ].
    - apply tv_var_unl; [done|done|var_others HΔ].
  Qed.

  Lemma recv_tr_typed Φ Δ0 F t n :
    lenv_empty Δ0 → payok t → lvl_lt (LZ n) (olvl (tlev t)) →
    typed W Φ Ψ ∅ Δ0 F recv_tr (TLolli (hiz B k (LZ n)) None (trz B k (PChan true t n)) (trz B k t)).
  Proof.
    intros HΔ Hok Hn. pose proof Wpn_wf as HW.
    destruct (pay_conv t n Hok Hn) as (_ & Hc2 & Hh & Hs).
    set (x := chx t n). set (φ := fresh (dom Φ)).
    apply (t_lam W Φ Ψ ∅ Δ0 F _ _ _ (hiz B k (LZ n)) None φ); [apply is_fresh| |].
    { simpl. by rewrite (tenv_heads0 W HW), empty_heads, union_empty_l_L. }
    set (Φ1 := <[φ := hiz B k (LZ n)]> Φ).
    assert (Φ1 !! φ = Some (Some (rpt B (RHi (n + k))))) as Hφ by (unfold Φ1; by rewrite lookup_insert_eq).
    set (E := Some (trz B k (PChan true t n)) :: Δ0).
    set (P := payload_at (pbind t) (ppay t) x).
    eapply (t_letp W Φ1 Ψ ∅ ∅ ∅ E E (lenv_nones E) _ _ _ P (TSess SEnd (pt_shift 1 x)));
      [by apply comp0|apply lenv_split_nones_r| |].
    - rewrite (tenv_heads0 W HW), nones_heads, union_empty_l_L, sf_union_empty.
      eapply (t_app W Φ1 Ψ ∅ ∅ ∅ E (lenv_nones E) E _ _ _ (Some x) None).
      { by apply comp0. } { apply lenv_split_nones_l. }
      { apply ub_below_s_intro; [simpl; set_solver|]. exists (rpt B (RHi (n + k))). split; [done|right].
        apply (ch_below_hi Ψ B HB). apply clev_chx. }
      { apply t_konst; [apply lenv_empty_nones|apply KTRecv|done]. }
      rewrite sf_union_empty. apply tv_var_unl; [done|done|].
      intros [|y] T' Hne Hy; [done|]. exfalso. simpl in Hy. by eapply empty_lookup.
    - set (N := lenv_nones E).
      assert (lenv_empty N) as HN by apply lenv_empty_nones.
      eapply (t_letu W Φ1 Ψ ∅ ∅ ∅ _ (Some (TSess SEnd (pt_shift 1 x)) :: None :: N)
                (None :: Some P :: N)); [by apply comp0| | |].
      { constructor. constructor. by apply lenv_split_empty'. }
      + rewrite (tenv_heads0 W HW), union_empty_l_L.
        eapply (t_app W Φ1 Ψ ∅ ∅ ∅ _ (lenv_nones (Some (TSess SEnd (pt_shift 1 x)) :: None :: N))
                  (Some (TSess SEnd (pt_shift 1 x)) :: None :: N) _ _ _ (Some (pt_shift 1 x)) None).
        { by apply comp0. } { apply lenv_split_nones_l. }
        { apply ub_below_s_intro.
          - simpl. rewrite nones_heads. intros y Hy.
            rewrite union_empty_l_L, union_empty_r_L in Hy. by apply Hh.
          - exists (rpt B (RHi (n + k))). split; [done|right].
            apply (ch1_below_hi Ψ B HB). apply clev_chx. }
        { apply t_konst; [apply lenv_empty_nones|apply KTClos|done]. }
        rewrite sf_union_empty. apply tv_var_unl; [done|done|var_others HN].
      + eapply t_conv; [exact Hc2|]. apply tv_var_unl; [done|done|var_others HN].
  Qed.

  Lemma fork_tr_typed Φ Δ0 F r σ :
    lenv_empty Δ0 →
    typed W Φ Ψ ∅ Δ0 F (fork_tr (match r with Some _ => false | None => true end))
      (TLolli None None (trz B k (PArr PUnit r σ PUnit)) U).
  Proof.
    intros HΔ. pose proof Wpn_wf as HW. set (φ0 := fresh (dom Φ)).
    apply (t_lam W Φ Ψ ∅ Δ0 F _ _ _ None None φ0); [apply is_fresh| |].
    { simpl. by rewrite (tenv_heads0 W HW), empty_heads, union_empty_l_L. }
    set (Φ1 := <[φ0 := None]> Φ).
    set (fT := trz B k (PArr PUnit r σ PUnit)).
    set (E := Some fT :: Δ0).
    eapply (t_letu W Φ1 Ψ ∅ ∅ ∅ E E (lenv_nones E)); [by apply comp0|apply lenv_split_nones_r| |].
    2:{ apply tv_unitv; [done|apply nones_unl]. }
    (* the thunk's points *)
    set (ub := match r with
               | Some _ => hiz B k σ
               | None => hiz (rpt B (RAnc 0)) (mneg (PArr PUnit None σ PUnit)) σ end).
    set (lb := match r with Some z => Some (loz B k z) | None => None end).
    eapply (t_app W Φ1 Ψ ∅ ∅ ∅ E (lenv_nones E) E _ _ _ None None (TLolli ub lb TUnit TUnit)).
    { by apply comp0. } { apply lenv_split_nones_l. } { done. }
    { apply t_konst; [apply lenv_empty_nones|apply KTSpawn|done]. }
    set (φ := fresh (dom Φ1)).
    apply (t_lam W Φ1 Ψ ∅ E _ _ _ _ ub lb φ); [apply is_fresh| |].
    { simpl. rewrite (tenv_heads0 W HW), empty_heads, union_empty_l_L, union_empty_r_L by done.
      unfold fT, lb. destruct r as [z|]; simpl.
      - intros y Hy. apply elem_of_singleton in Hy as ->. left. apply se_refl.
      - done. }
    set (Φ2 := <[φ := ub]> Φ1).
    eapply (t_letu W Φ2 Ψ ∅ ∅ ∅ _ (Some TUnit :: None :: Δ0) (None :: Some fT :: Δ0));
      [by apply comp0| | |].
    { constructor. constructor. by apply lenv_split_empty'. }
    { apply tv_var_unl; [done|done|var_others HΔ]. }
    assert (ub_below_s W Ψ Φ2 ub (∅, Some φ)) as Hub by apply (ubs_fresh W HW).
    destruct r as [z|]; simpl.
    - eapply (typed_force W Φ2 Ψ ∅ _ _ _ 0 C0 None TUnit []); [done|done| |done|done|].
      { intros g Hg. apply bcs_open_nil in Hg as [[] _]. }
      eapply (t_app W Φ2 Ψ ∅ ∅ ∅ _ (None :: Some fT :: Δ0) (lenv_nones (None :: Some fT :: Δ0))
                _ _ _ (hiz B k σ) (Some (loz B k z)) U U).
      { by apply comp0. } { apply lenv_split_nones_r. } { done. }
      { apply tv_var_unl; [done|done|var_others HΔ]. }
      { apply tv_unitv; [done|apply nones_unl]. }
    - set (m := mneg (PArr PUnit None σ PUnit)). set (X := rpt B (RAnc 0)).
      eapply (typed_force W Φ2 Ψ ∅ _ _ _ 0 C0 None TUnit []); [done|done| |done|done|].
      { intros g Hg. apply bcs_open_nil in Hg as [[] _]. }
      eapply (t_app W Φ2 Ψ ∅ ∅ ∅ _ (None :: Some fT :: Δ0) (lenv_nones (None :: Some fT :: Δ0))
                _ _ _ (hiz X m σ) None U U).
      { by apply comp0. } { apply lenv_split_nones_r. } { done. }
      2:{ apply tv_unitv; [done|apply nones_unl]. }
      assert (ty_inst [X] (TLolli (hiz (pvar 0) m σ) None (trz (pvar 0) m PUnit) (trz (pvar 0) m PUnit))
              = TLolli (hiz X m σ) None U U) as <-.
      { unfold ty_inst. simpl. rewrite hiz_pinst. by rewrite pt_inst_pvar_at. }
      eapply (typed_force W Φ2 Ψ ∅ _ _ _ 1 Crel None); [done|done|apply (crel_hold Ψ B HB)
        |apply (anc_known Ψ B HB)|done|].
      apply tv_var_unl; [done|done|var_others HΔ].
  Qed.

  Lemma inj_tr_typed Φ Δ0 F t s (b : bool) :
    lenv_empty Δ0 → un t → un s →
    typed W Φ Ψ ∅ Δ0 F (if b then inj1_tr else inj2_tr)
      (TLolli None None (trz B k (if b then t else s)) (trz B k (PSum t s))).
  Proof.
    intros HΔ Ht Hs. pose proof Wpn_wf as HW. set (φ := fresh (dom Φ)).
    assert (un (if b then t else s)) as Hu by (by destruct b).
    destruct b; [unfold inj1_tr|unfold inj2_tr];
      (apply (t_lam W Φ Ψ ∅ Δ0 F _ _ _ None None φ); [apply is_fresh| |]);
      try (simpl; by rewrite (tenv_heads0 W HW), empty_heads, union_empty_l_L);
      simpl; unfold Ubox; (apply (tv_box W HW); [|done|]);
      try (intros o [->|Ho]%elem_of_cons; [right; eexists; split; [done|by apply trz_unlimited]
                                          |left; by apply HΔ]).
    - intros φ' _. apply t_inj1. rewrite (trz_un proot B 0 k t) by done.
      apply tv_var_unl; [done|simpl; by rewrite trz_pinst, (trz_un _ B _ k)|].
      intros [|[|y]] T' Hne Hy; simpl in Hy; try done; [by injection Hy as <-|].
      exfalso. unfold lenv_pinst in Hy. rewrite list_lookup_fmap in Hy.
      apply fmap_Some in Hy as (o & Ho & Ho'). destruct o; [|done]. by eapply empty_lookup.
    - intros φ' _. apply t_inj2. rewrite (trz_un proot B 0 k s) by done.
      apply tv_var_unl; [done|simpl; by rewrite trz_pinst, (trz_un _ B _ k)|].
      intros [|[|y]] T' Hne Hy; simpl in Hy; try done; [by injection Hy as <-|].
      exfalso. unfold lenv_pinst in Hy. rewrite list_lookup_fmap in Hy.
      apply fmap_Some in Hy as (o & Ho & Ho'). destruct o; [|done]. by eapply empty_lookup.
  Qed.
End terms.

(** ** Closed terms are fixed by renaming *)

Lemma rename_unitv r : rename r unitv = unitv.
Proof. done. Qed.
Lemma rename_send r : rename r send_tr = send_tr.
Proof. done. Qed.
Lemma rename_recv r : rename r recv_tr = recv_tr.
Proof. done. Qed.
Lemma rename_fork r b : rename r (fork_tr b) = fork_tr b.
Proof. by destruct b. Qed.
Lemma rename_inj1 r : rename r inj1_tr = inj1_tr.
Proof. done. Qed.
Lemma rename_inj2 r : rename r inj2_tr = inj2_tr.
Proof. done. Qed.

Lemma hiz_sh B k n σ : hiz B k (lvl_sh n σ) = hiz B (k + n) σ.
Proof. destruct σ; simpl; zeq. Qed.

(** ** Fold, unfold, wrap and unwrap *)

Lemma pconv1_steq Ψ B k t t' :
  pconv1 t t' → steq Wpn Ψ (trz B k t) (trz B k t') ∧ steq Wpn Ψ (trz B k t') (trz B k t).
Proof.
  intros [p m n|m t0].
  - assert (seq (SMu (pol p 1 (TSess (SVar 0) (pvar 0)) SEnd))
              (pol p 1 (TSess (SMu (pol p 1 (TSess (SVar 0) (pvar 0)) SEnd)) (pvar 0)) SEnd)) as Hs
      by (apply seq_unf; destruct p; reflexivity).
    split; (split; [apply se_refl|]); [exact Hs|by apply seq_sym].
  - simpl. rewrite trz_lshift. split; apply teq_steq, teq_refl.
Qed.

Lemma pconv_typed Ψ B k Φ Δ F e t t' :
  pconv t t' → typed Wpn Φ Ψ ∅ Δ F e (trz B k t) → typed Wpn Φ Ψ ∅ Δ F e (trz B k t').
Proof.
  induction 1 as [t|t t1 t2 H1 _ IH|t t1 t2 H1 _ IH]; intros He; [done| |].
  - apply IH. eapply t_conv; [|exact He]. exact (proj1 (pconv1_steq Ψ B k _ _ H1)).
  - apply IH. eapply t_conv; [|exact He]. exact (proj2 (pconv1_steq Ψ B k _ _ H1)).
Qed.

(** ** The translation lemma *)

Theorem pn_translate Γ e t τ e' :
  pn_typed Γ e t τ e' →
  ∀ Ψ B k ins Δ Φ F, good Ψ B → erel B k ins Γ Δ → ub_below_s Wpn Ψ Φ (hiz B k τ) F →
  typed Wpn Φ Ψ ∅ Δ F (rename (ren_of ins) e') (trz B k t).
Proof.
  pose proof Wpn_wf as HW.
  induction 1 as [Γ x t Hx
    |Γ HΓ
    |Γ e e' t s ρ He IH
    |Γ Γ1 Γ2 e1 e2 e1' e2' t r σ s τ1 τ2 Hs H1 IH1 H2 IH2 Hl1 Hl2
    |Γ Γ1 Γ2 e1 e2 e1' e2' t σ s τ1 τ2 n Hs H1 IH1 H2 IH2 Hl1 Hl2
    |Γ e e' t n s τ Hn Hok He IH
    |Γ Γ1 Γ2 e1 e2 e1' e2' t n τ1 τ2 Hs H1 IH1 H2 IH2 Hn Hok Hl1 Hl2
    |Γ e e' t n τ He IH Hn Hok
    |Γ e e' r σ τ He IH
    |Γ e e' t σ s HΓ He IH
    |Γ e e' t s τ He IH Ht Hs'
    |Γ e e' t s τ He IH Ht Hs'
    |Γ Γ1 Γ2 e e1 e2 e' e1' e2' t s u τ1 τ2 Hs He IHe Ht Hs' H1 IH1 H2 IH2 Hl
    |Γ e e' t t' τ He IH Hc];
    intros Ψ B k ins Δ Φ F HB HΔ HF.
  - (* T-Name *)
    by apply (erel_var B k ins Γ Δ Wpn Φ Ψ F x t HW HΔ Hx).
  - (* () *)
    rewrite rename_unitv. apply (tv_unitv Wpn HW). by apply (erel_unl B k ins Γ Δ).
  - (* T-Fun *)
    destruct (env_lev Γ) as [z|] eqn:Ez; simpl.
    + (* a closure that holds channels *)
      rewrite ren_up. set (φ := fresh (dom Φ)).
      apply (t_lam Wpn Φ Ψ ∅ Δ F _ _ _ (hiz B k ρ) (Some (loz B k z)) φ); [apply is_fresh| |].
      * simpl. rewrite (tenv_heads0 _ HW), union_empty_l_L. intros y Hy.
        apply (env_lo_below Ψ B HB k ins Γ Δ z y HΔ Ez Hy).
      * apply IH; [done|by apply (er_keep _ _ (Some t))|apply (ubs_fresh _ HW)].
    + (* a closure of level ⊤ is a box *)
      rewrite ren_box. pose proof (env_lev_none Γ Ez) as HΓ.
      set (u := PArr t None ρ s). set (m := mneg u).
      apply (tv_box Wpn HW _ _ _ _ _ 1 Crel None
               (TLolli (hiz (pvar 0) m ρ) None (trz (pvar 0) m t) (trz (pvar 0) m s)));
        [by apply (erel_unl B k ins Γ Δ)|done|].
      intros φ Hφ.
      set (Ψ' := hyps_inst (pshift 1) Ψ ++ [(Crel, ids 1)]).
      assert (good Ψ' (pvar 0)) as HB' by (apply good_box; unfold Ψ'; set_solver).
      set (Φ1 := <[φ := None]> (fhyps_pinst (pshift 1) Φ)). set (φ' := fresh (dom Φ1)).
      apply (t_lam Wpn Φ1 Ψ' ∅ _ _ _ _ _ (hiz (pvar 0) m ρ) None φ'); [apply is_fresh| |].
      * simpl. rewrite (tenv_heads0 _ HW), !union_empty_l_L. apply unl_heads, unl_pinst.
        by apply (erel_unl B k ins Γ Δ).
      * apply IH; [done| |apply (ubs_fresh _ HW)].
        apply (er_keep _ _ (Some t)). simpl. apply er_skip.
        { right. eexists. split; [done|]. done. }
        by apply (erel_pinst B k).
  - (* T-App *)
    cbn [rename]. destruct (erel_split B k ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    eapply (t_app Wpn Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (hiz B k σ) (Some (loz B k r)) (trz B k t)).
    + by apply comp0.
    + done.
    + apply (ubs_lvl Ψ B HB k Φ σ (lvl_max σ (lvl_max τ1 τ2))); [apply lvl_le_max_l|done].
    + rewrite (tenv_heads0 _ HW), union_empty_l_L. apply (IH1 Ψ B k ins Δ1); [done|done|].
      apply (ubs_union _ HW).
      * apply (ubs_lvl Ψ B HB k Φ τ1 (lvl_max σ (lvl_max τ1 τ2))); [|done].
        eapply lvl_le_trans; [apply lvl_le_max_l|apply lvl_le_max_r].
      * intros x Hx h Hh. by apply (env_hi_below Ψ B HB k ins Γ2 Δ2 τ1 x h).
    + apply (IH2 Ψ B k ins Δ2); [done|done|]. apply (ubs_union _ HW).
      * apply (ubs_lvl Ψ B HB k Φ τ2 (lvl_max σ (lvl_max τ1 τ2))); [|done].
        eapply lvl_le_trans; [apply lvl_le_max_r|apply lvl_le_max_r].
      * intros x Hx h Hh. simpl in Hh. apply elem_of_singleton in Hh as ->.
        by apply (hi_below_lo Ψ B HB k τ2 r x).
  - (* T-App-Poly *)
    cbn [rename]. destruct (erel_split B k ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    set (u := PArr t None σ s). set (m := mneg u). set (X := rpt B (RAnc (k + n - m))).
    set (Tb := TLolli (hiz (pvar 0) m σ) None (trz (pvar 0) m t) (trz (pvar 0) m s)).
    eapply (t_app Wpn Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (hiz B k (lvl_sh n σ)) None (trz B k (lshift n t))).
    + by apply comp0.
    + done.
    + apply (ubs_lvl Ψ B HB k Φ _ (lvl_max (lvl_sh n σ) (lvl_max τ1 τ2))); [apply lvl_le_max_l|done].
    + rewrite (tenv_heads0 _ HW), union_empty_l_L.
      apply (t_conv _ _ _ _ _ _ _ (ty_inst [X] Tb)).
      { unfold ty_inst, Tb. simpl. rewrite hiz_pinst, !trz_pinst. rewrite pt_inst_pvar_at. simpl.
        rewrite hiz_sh, !trz_lshift. split_and!.
        - apply (hiz_anc Ψ B HB). lia.
        - done.
        - apply (trz_anc Ψ B HB). lia.
        - apply (trz_anc Ψ B HB). lia. }
      eapply (typed_force Wpn Φ Ψ ∅ Δ1 _ _ 1 Crel None Tb [X]);
        [done|done|apply (crel_hold Ψ B HB)|apply (anc_known Ψ B HB)|done|].
      apply (IH1 Ψ B k ins Δ1); [done|done|]. apply (ubs_union _ HW).
      * apply (ubs_lvl Ψ B HB k Φ τ1 (lvl_max (lvl_sh n σ) (lvl_max τ1 τ2))); [|done].
        eapply lvl_le_trans; [apply lvl_le_max_l|apply lvl_le_max_r].
      * intros x Hx h Hh. by apply (env_hi_below Ψ B HB k ins Γ2 Δ2 τ1 x h).
    + rewrite sf_union_empty. apply (IH2 Ψ B k ins Δ2); [done|done|].
      apply (ubs_lvl Ψ B HB k Φ τ2 (lvl_max (lvl_sh n σ) (lvl_max τ1 τ2))); [|done].
      eapply lvl_le_trans; [apply lvl_le_max_r|apply lvl_le_max_r].
  - (* let a = new() in e *)
    cbn [rename]. rewrite ren_up2.
    eapply (t_letp Wpn Φ Ψ ∅ ∅ ∅ Δ (lenv_nones Δ) Δ F _ _ (trz B k (PChan true t n))
              (trz B k (PChan false t n))); [by apply comp0|apply lenv_split_nones_l| |].
    + apply (tv_app_closed Wpn HW _ _ _ _ _ _ None TUnit).
      * apply t_konst; [apply lenv_empty_nones| |done].
        apply (KTNew _ _ _ (sess (PChan true t n)) (rpt B (RCh (PChan true (lshift k t) (n + k))))).
        by apply (gd_kn _ _ HB).
      * apply t_unit, lenv_empty_nones.
      * done.
    + apply IH; [done| |done]. apply (er_keep _ _ (Some _)), (er_keep _ _ (Some _)), HΔ.
  - (* send e₁ e₂ *)
    cbn [rename]. rewrite rename_send.
    destruct (erel_split B k ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    eapply (t_app Wpn Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (hiz B k (LZ n)) (Some (loz B k n)) (trz B k t) U).
    + by apply comp0.
    + done.
    + apply (ubs_lvl Ψ B HB k Φ _ (lvl_max (LZ n) (lvl_max τ1 τ2))); [apply lvl_le_max_l|done].
    + rewrite (tenv_heads0 _ HW), union_empty_l_L.
      apply (tv_app_closed Wpn HW _ _ _ _ _ _ None (trz B k (PChan false t n))).
      * by apply (send_tr_typed Ψ B HB k); [apply lenv_empty_nones| |].
      * apply (IH1 Ψ B k ins Δ1); [done|done|]. apply (ubs_union _ HW).
        -- apply (ubs_lvl Ψ B HB k Φ τ1 (lvl_max (LZ n) (lvl_max τ1 τ2))); [|done].
           eapply lvl_le_trans; [apply lvl_le_max_l|apply lvl_le_max_r].
        -- intros x Hx h Hh. by apply (env_hi_below Ψ B HB k ins Γ2 Δ2 τ1 x h).
      * done.
    + apply (IH2 Ψ B k ins Δ2); [done|done|]. apply (ubs_union _ HW).
      * apply (ubs_lvl Ψ B HB k Φ τ2 (lvl_max (LZ n) (lvl_max τ1 τ2))); [|done].
        eapply lvl_le_trans; [apply lvl_le_max_r|apply lvl_le_max_r].
      * intros x Hx h Hh. simpl in Hh. apply elem_of_singleton in Hh as ->.
        by apply (hi_below_lo Ψ B HB k τ2 n x).
  - (* recv e *)
    cbn [rename]. rewrite rename_recv.
    apply (tv_app_closed Wpn HW _ _ _ _ _ _ (hiz B k (LZ n)) (trz B k (PChan true t n))).
    + by apply (recv_tr_typed Ψ B HB k); [apply lenv_empty_nones| |].
    + apply IH; [done|done|]. apply (ubs_lvl Ψ B HB k Φ τ (lvl_max (LZ n) τ)); [apply lvl_le_max_r|done].
    + apply (ubs_lvl Ψ B HB k Φ (LZ n) (lvl_max (LZ n) τ)); [apply lvl_le_max_l|done].
  - (* fork e *)
    cbn [rename]. rewrite rename_fork.
    apply (tv_app_closed Wpn HW _ _ _ _ _ _ None (trz B k (PArr PUnit r σ PUnit))).
    + apply (fork_tr_typed Ψ B HB k). apply lenv_empty_nones.
    + by apply IH.
    + done.
  - (* fix λf.e *)
    cbn [rename]. rewrite ren_up.
    set (u := PArr t None σ s). set (m := mneg u).
    set (Tb := TLolli (hiz (pvar 0) m σ) None (trz (pvar 0) m t) (trz (pvar 0) m s)).
    apply (tv_box Wpn HW _ _ _ _ _ 1 Crel None Tb); [by apply (erel_unl B k ins Γ Δ)|done|].
    intros φ Hφ.
    set (Ψ' := hyps_inst (pshift 1) Ψ ++ [(Crel, ids 1)]).
    assert ((Crel, [pvar 0]) ∈ Ψ') as HC by (unfold Ψ'; set_solver).
    assert (good Ψ' (pvar 0)) as HB' by by apply good_box.
    assert (ty_inst [pvar 0] Tb = Tb) as HTb.
    { unfold ty_inst, Tb. simpl. by rewrite hiz_pinst, !trz_pinst. }
    apply (t_conv _ _ _ _ _ _ _ (ty_inst [pvar 0] Tb)); [rewrite HTb; apply teq_steq, teq_refl|].
    eapply (typed_force Wpn _ Ψ' ∅ _ _ _ 1 Crel None Tb [pvar 0]);
      [done|done|exact (hyp_in_fact Wpn Ψ' Crel [pvar 0] HC)|exact (hyp_in_known Wpn Ψ' Crel [pvar 0] HC)|done|].
    change (TBox 1 Crel (TLolli None None TUnit Tb)) with (trz (pvar 0) 0 u).
    apply IH; [done| |done].
    change (lenv_pinst (pshift 1) (Some (trz (pvar 0) 0 u) :: Δ))
      with (Some (pinst_ty (pshift 1) (trz (pvar 0) 0 u)) :: lenv_pinst (pshift 1) Δ).
    rewrite trz_pinst, (trz_un _ (pvar 0) _ 0) by done.
    apply (er_keep _ _ (Some u)). by apply (erel_pinst B k).
  - (* inj₁ e *)
    cbn [rename]. rewrite rename_inj1.
    apply (tv_app_closed Wpn HW _ _ _ _ _ _ None (trz B k t)).
    + by apply (inj_tr_typed Ψ B HB k _ _ _ t s true); [apply lenv_empty_nones| |].
    + by apply IH.
    + done.
  - (* inj₂ e *)
    cbn [rename]. rewrite rename_inj2.
    apply (tv_app_closed Wpn HW _ _ _ _ _ _ None (trz B k s)).
    + by apply (inj_tr_typed Ψ B HB k _ _ _ t s false); [apply lenv_empty_nones| |].
    + by apply IH.
    + done.
  - (* case *)
    cbn [rename]. rewrite !ren_up.
    destruct (erel_split B k ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    eapply (t_case Wpn Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ _ (trz proot 0 t) (trz proot 0 s));
      [by apply comp0|done| | |].
    + rewrite (tenv_heads0 _ HW), union_empty_l_L.
      assert (ty_inst [] (TSum (trz proot 0 t) (trz proot 0 s)) = TSum (trz proot 0 t) (trz proot 0 s))
        as <- by (unfold ty_inst; simpl; by rewrite !trz_pinst, (pt_inst_const _ proot 0)).
      eapply (typed_force Wpn Φ Ψ ∅ Δ1 _ _ 0 C0 None _ []); [done|done| |done|done|].
      { intros g Hg. apply bcs_open_nil in Hg as [[] _]. }
      apply (IHe Ψ B k ins Δ1); [done|done|]. apply (ubs_union _ HW).
      * apply (ubs_lvl Ψ B HB k Φ τ1 (lvl_max τ1 τ2)); [apply lvl_le_max_l|done].
      * intros x Hx h Hh. by apply (env_hi_below Ψ B HB k ins Γ2 Δ2 τ1 x h).
    + rewrite (trz_un proot B 0 k t) by done. apply IH1; [done| |].
      * by apply (er_keep _ _ (Some t)).
      * apply (ubs_lvl Ψ B HB k Φ τ2 (lvl_max τ1 τ2)); [apply lvl_le_max_r|done].
    + rewrite (trz_un proot B 0 k s) by done. apply IH2; [done| |].
      * by apply (er_keep _ _ (Some s)).
      * apply (ubs_lvl Ψ B HB k Φ τ2 (lvl_max τ1 τ2)); [apply lvl_le_max_r|done].
  - (* wrap, unwrap, fold, unfold *)
    apply (pconv_typed Ψ B k Φ Δ F _ t t' Hc). by apply IH.
Qed.

(** ** Deadlock freedom *)

(** A closed program of type unit translates to a typed closed thread at
    the strict world [Wpn], so it is deadlock free. *)
Theorem pn_deadlock_free e τ e' :
  pn_typed [] e PUnit τ e' → deadlock_free (∅, {[+ e' +]}).
Proof.
  intros H. apply (soundness Wpn _ U Wpn_strict). apply ptyped_closed; [repeat constructor|].
  rewrite <-(rename_id e'), (rename_ext e' (λ x, x) (ren_of [])) by done.
  apply (pn_translate [] e PUnit τ e' H [] proot 0 [] [] ∅ (∅, None)); [apply good_root|constructor|].
  destruct (hiz proot 0 τ); [|done]. split; simpl; [set_solver|done].
Qed.
