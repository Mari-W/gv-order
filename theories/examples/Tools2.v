(** * More tools for example derivations (stage S2) *)

From GV Require Export examples.Tools.

(** {x} ≺ F for a future of points X with no rest. *)
Lemma ub_below_nil W Γ x X b :
  b = false → (∀ y, y ∈ X → slt W Γ x y) → ub_below_s W Γ (Some x) (sf_unionb (∅, None) X b).
Proof. intros -> HX. simpl. split; [|done]. intros y Hy. apply HX. set_solver. Qed.

(** The heads of a concrete context, as point equations. *)
Ltac heads_cases Hy :=
  heads_simpl Hy; repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst;
  try contradiction.

(** The context after opening a [new] at the top: its constraint L at ι₀. *)
Definition Γnew (L : fact → Prop) : hctx := hc_open 1 (bcs_of L) hc_empty.

Lemma Γnew_in L : (bcs_of L, ids 1) ∈ hc_hyps (Γnew L).
Proof. unfold Γnew, hc_open. simpl. by left. Qed.

(** A fact of L at the opened base. *)
Lemma law_slt W (L : fact → Prop) f x y :
  L f → fact_scoped 1 f → fact_map (pt_inst (plist (ids 1))) f = FLt x y →
  slt W (Γnew L) x y.
Proof. intros Hf Hs Hxy. eapply (slt_hyp _ _ L (ids 1) f); [apply Γnew_in|done|done|done]. Qed.

Lemma pt_inst_ids k x : pn_vb k (pt_name x) → pt_inst (plist (ids k)) x = x.
Proof.
  intros H. rewrite (pt_inst_ext_root _ pvar); [apply pt_inst_pvar|]. intros a Ha.
  apply pn_vb_root in H as (a' & Ha' & Hlt). unfold pt_root in Ha. rewrite Ha in Ha'.
  injection Ha' as ->. unfold plist, ids. rewrite list_lookup_fmap, lookup_seq_lt by done. done.
Qed.

(** A fact x ≺ y of a constraint without outer points, at the identity
    instance ids k: the hypothesis of a box body or of an opened ∃. *)
Lemma hyp_slt_ids W Γ P k x y :
  (BCs [] P, ids k) ∈ hc_hyps Γ → P (FLt x y) → fact_scoped k (FLt x y) → slt W Γ x y.
Proof.
  intros Hin Hf Hs. eapply (slt_hyp _ _ P (ids k) (FLt x y)); [done|done| |].
  - unfold ids. by rewrite length_fmap, length_seq.
  - destruct Hs as [Hx Hy]. simpl. by rewrite !pt_inst_ids.
Qed.

Lemma law_slt' W (L : fact → Prop) x y :
  L (FLt x y) → fact_scoped 1 (FLt x y) → slt W (Γnew L) x y.
Proof. intros Hf Hs. eapply hyp_slt_ids; [apply Γnew_in|done|done]. Qed.

(** A box □∀ιs. C. T ⊸^u ∗ whose body is λp. e, typed under the
    context of the box body. *)
Definition box1 (m : nat) (C : bcs) (u : point) (T : ty) : ty :=
  TBox m 0 C None None (TLolli (UPt u) LNone None T TUnit None).

Definition Γbox (m : nat) (C : bcs) (u : point) (Γ : hctx) : hctx := hc_open m C Γ.

Lemma Γbox_in m C u Γ : (bcs_inst (pshift m) C, ids m) ∈ hc_hyps (Γbox m C u Γ).
Proof. unfold Γbox, hc_open. simpl. apply elem_of_app. right. by left. Qed.

Lemma lenv_pinst_cons' σ o Δ :
  lenv_pinst σ (o :: Δ) = (fmap (M:=option) (pinst_ty σ) o) :: lenv_pinst σ Δ.
Proof. done. Qed.

Lemma box1_typed W Γ n F m C u T e :
  tcontr T →
  pinst_ty (pshift m) (box1 m C u T) = box1 m C u T →
  dftyped W ∅ (Γbox m C u Γ) (Some T :: Some (box1 m C u T) :: nones n)
    (∅, Some (RAbove u)) e TUnit →
  dftyped W ∅ Γ (nones n) F (EBox (Lam e)) (box1 m C u T).
Proof.
  intros HT HB He. unfold box1 at 1. eapply d_box.
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  { cbn [tcontr]. by apply Is_true_andb. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil.
  rewrite lenv_pinst_cons'. cbn [fmap option_fmap option_map]. fold (box1 m C u T).
  rewrite HB, lenv_pinst_nones.
  eapply d_abs.
  { apply lb_below_none. spare_tac. }
  { done. }
  exact He.
Qed.

(** {x} ≺ F for any future whose rest is everything above u. *)
Lemma ub_below_gen W Γ x u (F : sfuture) :
  (∀ y, y ∈ F.1 → slt W Γ x y) → F.2 = Some (RAbove u) →
  sle W Γ x u → ub_below_s W Γ (Some x) F.
Proof.
  intros HX Hv Hu. split; [done|]. intros r Hr. rewrite Hv in Hr. by injection Hr as <-.
Qed.

(** {x} ≺ F for a future without variable. *)
Lemma ub_below_novar W Γ x (F : sfuture) :
  (∀ y, y ∈ F.1 → slt W Γ x y) → F.2 = None → ub_below_s W Γ (Some x) F.
Proof. destruct F as [X o]. simpl. intros HX ->. split; [done|]. done. Qed.

Lemma sf_pinst_nil' σ o : sf_pinst σ (∅, o) = (∅, frest_pinst σ <$> o).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

(** A box □∀ιs. C. T ⊸^ub U whose body is λp. e. *)
Definition boxg (m : nat) (C : bcs) (ub : option point) (T U : ty) : ty :=
  TBox m 0 C None None (TLolli (ubound_of ub) LNone None T U None).

Lemma boxg_typed W Γ n F m C ub T U e :
  tcontr T → tcontr U →
  pinst_ty (pshift m) (boxg m C ub T U) = boxg m C ub T U →
  dftyped W ∅ (hc_open m C Γ)
    (Some T :: Some (boxg m C ub T U) :: nones n) (∅, Some (rest_of ub)) e U →
  dftyped W ∅ Γ (nones n) F (EBox (Lam e)) (boxg m C ub T U).
Proof.
  intros HT HU HB He. unfold boxg at 1. eapply d_box.
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  { cbn [tcontr]. by apply Is_true_andb. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil.
  rewrite lenv_pinst_cons'. cbn [fmap option_fmap option_map]. fold (boxg m C ub T U).
  rewrite HB, lenv_pinst_nones.
  eapply d_abs; rewrite ?abs_fut_of.
  { apply lb_below_none. spare_tac. }
  { done. }
  exact He.
Qed.
