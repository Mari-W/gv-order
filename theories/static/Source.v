(** * The source judgment, without a world (static-system.md §2)

    [styped Φ Ψ Δ F t T] is the judgment Δ ⊢^F_Γ t : T of
    static-system.md for a self-contained single-threaded source
    program. Γ is the hypotheses Ψ and the frame hypotheses Φ, and no
    world occurs in the signature.

    Why a world is a don't-care here. A well-formed world relates two
    points only when both roots lie in its support ([wf_eq_supp],
    [wf_lt_supp]), or when the two points share a name and the offset
    grows. Every support name is a point constant ([wf_names_const]),
    so a point rooted at a point variable is related by no world beyond
    program order, and no world knows it ([pt_known]). A source program
    has no channel constants, its typing environment Θ stays empty, and
    every point it mentions is rooted at a variable bound by an
    enclosing binder. Program order is a rule of the fact theory
    ([fl_po]), so the world reaches such a derivation nowhere.

    The source judgment therefore drops both the world and Θ. It is a
    restriction of [typed], not a new rule set: [styped_typed] sends
    every derivation to one in [typed] at an arbitrary world, and
    [typed_styped] sends every derivation in a world with empty support
    back. Channel constants (E-Ch) and the process layer
    ([ptyped], P-Term, P-Connect) keep [typed] and its world. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.Typing.

Set Default Proof Using "All".

(** ** The fact theory of the hypotheses

    [heqs Ψ] and [hfl Ψ Φ] are [seqs] and [fl] without the generators
    of a world. Knownness is [hyp_known], a point rooted at an instance
    point of a hypothesis, which is what static-system.md asks of a
    point before [new] or force may name it. *)

Inductive heqs (Ψ : hyps) : point → point → Prop :=
  | he_h x y : hyp_fact Ψ (FEq x y) → heqs Ψ x y
  | he_refl x : heqs Ψ x x
  | he_sym x y : heqs Ψ x y → heqs Ψ y x
  | he_trans x y z : heqs Ψ x y → heqs Ψ y z → heqs Ψ x z
  | he_shift x y : heqs Ψ x y → heqs Ψ (pt_shift 1 x) (pt_shift 1 y)
  | he_slot x y i : heqs Ψ x y → heqs Ψ (pt_slot x i) (pt_slot y i).

Inductive hfl (Ψ : hyps) (Φ : fhyps) : node → node → Prop :=
  | hl_h x y : hyp_fact Ψ (FLt x y) → hfl Ψ Φ (NP x) (NP y)
  | hl_v φ u : Φ !! φ = Some (Some u) → hfl Ψ Φ (NP u) (NV φ)
  | hl_eql x x' b : heqs Ψ x x' → hfl Ψ Φ (NP x') b → hfl Ψ Φ (NP x) b
  | hl_eqr a y y' : hfl Ψ Φ a (NP y') → heqs Ψ y' y → hfl Ψ Φ a (NP y)
  | hl_trans a y b : hfl Ψ Φ a (NP y) → hfl Ψ Φ (NP y) b → hfl Ψ Φ a b
  | hl_po x : hfl Ψ Φ (NP x) (NP (pt_shift 1 x)).

Definition hlt (Ψ : hyps) (x y : point) : Prop := hfl Ψ ∅ (NP x) (NP y).

Definition hle (Ψ : hyps) (x y : point) : Prop := heqs Ψ x y ∨ hlt Ψ x y.

Lemma hl_po_n Ψ Φ x k : hfl Ψ Φ (NP x) (NP (pt_shift (S k) x)).
Proof.
  induction k as [|k IH]; [apply hl_po|].
  eapply hl_trans; [exact IH|]. rewrite <-(pt_shift_S (S k) x). apply hl_po.
Qed.

(** Program order between two points of one name. *)
Lemma hl_pofs Ψ Φ x y : pofs x y → hfl Ψ Φ (NP x) (NP y).
Proof.
  intros [Hn Ho]. destruct x as [p o], y as [q o']. simpl in *. subst q.
  replace o' with (o + S (o' - o - 1)) by lia.
  exact (hl_po_n Ψ Φ (Pt p o) (o' - o - 1)).
Qed.

Lemma hlt_pofs Ψ x y : pofs x y → hlt Ψ x y.
Proof. apply hl_pofs. Qed.

Lemma hlt_po Ψ x : hlt Ψ x (pt_shift 1 x).
Proof. apply hl_po. Qed.

Lemma hlt_trans Ψ x y z : hlt Ψ x y → hlt Ψ y z → hlt Ψ x z.
Proof. exact (hl_trans Ψ ∅ (NP x) y (NP z)). Qed.

(** A fact between two points holds under any frame hypotheses. *)
Lemma hfl_weaken Ψ Φ a b : hfl Ψ ∅ a b → hfl Ψ Φ a b.
Proof.
  induction 1.
  - by apply hl_h.
  - by rewrite lookup_empty in H.
  - by eapply hl_eql.
  - by eapply hl_eqr.
  - by eapply hl_trans.
  - apply hl_po.
Qed.

Lemma hlt_hfl Ψ Φ x y : hlt Ψ x y → hfl Ψ Φ (NP x) (NP y).
Proof. apply hfl_weaken. Qed.

(** ** Bounds and types, read from the hypotheses *)

Definition hlb_below_h (Ψ : hyps) (lb : option point) (H : gset point) : Prop :=
  match lb with None => H = ∅ | Some x => ∀ y, y ∈ H → hle Ψ x y end.

Definition hlb_below_hb (Ψ : hyps) (lb : option point)
    (H : gset point) (b : bool) : Prop :=
  if b then False else hlb_below_h Ψ lb H.

Definition hlbx_below_h (Ψ : hyps) (lb : lbound) (H : gset point) (b : bool) : Prop :=
  match lb with
  | LBot => True
  | LTop => H = ∅ ∧ b = false
  | LPt x => (∀ y, y ∈ H → hle Ψ x y) ∧ b = false
  end.

Definition hub_below_s (Ψ : hyps) (Φ : fhyps) (ub : option point) (F : sframe) : Prop :=
  match ub with
  | None => True
  | Some x => (∀ y, y ∈ F.1 → hfl Ψ Φ (NP x) (NP y)) ∧
              (∀ φ, fs_var F.2 = Some φ → hfl Ψ Φ (NP x) (NV φ)) ∧
              fs_bot F.2 = false
  end.

Fixpoint hsteq (Ψ : hyps) (T U : ty) : Prop :=
  match T, U with
  | TUnit, TUnit => True
  | TLolli ub lb T1 T2, TLolli ub' lb' U1 U2 =>
      opt_rel (heqs Ψ) ub ub' ∧ opt_rel (heqs Ψ) lb lb' ∧
      hsteq Ψ T1 U1 ∧ hsteq Ψ T2 U2
  | TProd T1 T2, TProd U1 U2 => hsteq Ψ T1 U1 ∧ hsteq Ψ T2 U2
  | TSum T1 T2, TSum U1 U2 => hsteq Ψ T1 U1 ∧ hsteq Ψ T2 U2
  | TBox n C T1, TBox n' C' U1 => n = n' ∧ C = C' ∧ teq T1 U1
  | TSess s x, TSess r y => heqs Ψ x y ∧ seq s r
  | TEx lb n C T1, TEx lb' n' C' U1 => lb = lb' ∧ n = n' ∧ C = C' ∧ teq T1 U1
  | _, _ => False
  end.

Lemma teq_hsteq Ψ T : ∀ U, teq T U → hsteq Ψ T U.
Proof.
  unfold teq. induction T; intros [] H; simpl in *; try done.
  - destruct H as (-> & -> & ? & ?). split_and!; auto.
    + destruct ub0; simpl; [apply he_refl|done].
    + destruct lb0; simpl; [apply he_refl|done].
  - destruct H. split; auto.
  - destruct H. split; auto.
  - destruct H as [<- ?]. split; [apply he_refl|done].
Qed.

(** ** The source judgment

    Every rule of [typed] for a form without channel constants, minus
    the world and minus Θ. E-Ch is gone. The frames of the composing
    rules lose the heads of Θ, which are those of the empty
    environment. *)

Inductive styped : fhyps → hyps → lenv → sframe → expr → ty → Prop :=
  | st_unit Φ Ψ Δ F :                                   (* E-Unit *)
      lenv_empty Δ →
      styped Φ Ψ Δ F EUnit TUnit
  | st_konst Φ Ψ Δ F k T :                              (* E-Const *)
      lenv_empty Δ → konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k T →
      styped Φ Ψ Δ F (Konst k) T
  | st_var Φ Ψ Δ F x T :                                (* E-LVar *)
      lenv_only Δ x T →
      styped Φ Ψ Δ F (Var x) T
  | st_lam Φ Ψ Δ F e T U ub lb φ :                      (* E-Abs *)
      φ ∉ dom Φ →
      hlb_below_hb Ψ lb (lenv_heads Δ) (lenv_bot Δ) →
      styped (<[φ := ub]> Φ) Ψ (Some T :: Δ) (∅, Some (FVar φ)) e U →
      styped Φ Ψ Δ F (Lam e) (TLolli ub lb T U)
  | st_app Φ Ψ Δ Δ1 Δ2 F e1 e2 ub lb T U :              (* E-App *)
      lenv_split Δ Δ1 Δ2 → hub_below_s Ψ Φ ub F →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TLolli ub lb T U) →
      styped Φ Ψ Δ2 (sf_union F (opt_heads lb)) e2 T →
      styped Φ Ψ Δ F (App e1 e2) U
  | st_pair Φ Ψ Δ Δ1 Δ2 F e1 e2 T U :                   (* E-Pair *)
      lenv_split Δ Δ1 Δ2 →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 T →
      styped Φ Ψ Δ2 (sf_unionb F (heads T) (hbot T)) e2 U →
      styped Φ Ψ Δ F (Pair e1 e2) (TProd T U)
  | st_letu Φ Ψ Δ Δ1 Δ2 F e1 e2 T :                     (* E-Let* *)
      lenv_split Δ Δ1 Δ2 →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit →
      styped Φ Ψ Δ2 F e2 T →
      styped Φ Ψ Δ F (LetU e1 e2) T
  | st_letp Φ Ψ Δ Δ1 Δ2 F e1 e2 T1 T2 T :               (* E-LetPair *)
      lenv_split Δ Δ1 Δ2 →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) →
      styped Φ Ψ (Some T2 :: Some T1 :: Δ2) F e2 T →
      styped Φ Ψ Δ F (LetP e1 e2) T
  | st_inj1 Φ Ψ Δ F e T U :                             (* E-Inj *)
      styped Φ Ψ Δ F e T → styped Φ Ψ Δ F (Inj1 e) (TSum T U)
  | st_inj2 Φ Ψ Δ F e T U :
      styped Φ Ψ Δ F e U → styped Φ Ψ Δ F (Inj2 e) (TSum T U)
  | st_case Φ Ψ Δ Δ1 Δ2 F e e1 e2 T1 T2 T :             (* E-Case *)
      lenv_split Δ Δ1 Δ2 →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e (TSum T1 T2) →
      styped Φ Ψ (Some T1 :: Δ2) F e1 T →
      styped Φ Ψ (Some T2 :: Δ2) F e2 T →
      styped Φ Ψ Δ F (Case e e1 e2) T
  | st_box Φ Ψ Δ F e m C ub T φ :                       (* E-Exp *)
      lenv_unl Δ → φ ∉ dom Φ →
      styped (<[φ := ub]> (fhyps_pinst (pshift m) Φ))
        (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
        (lenv_pinst (pshift m) (Some (TBox m C (TLolli ub None TUnit T)) :: Δ))
        (∅, Some (FVar φ)) e T →
      styped Φ Ψ Δ F (EBox e) (TBox m C (TLolli ub None TUnit T))
  | st_wk Φ Ψ Δ' Δ F e T :                              (* E-Weak *)
      lenv_wk Δ' Δ → styped Φ Ψ Δ' F e T → styped Φ Ψ Δ F e T
  | st_contract Φ Ψ Δ U F e T :                         (* E-Contract *)
      unlimited U →
      styped Φ Ψ (Some U :: Some U :: Δ) F e T →
      styped Φ Ψ (Some U :: Δ) F (rename pred e) T
  | st_conv Φ Ψ Δ F e T T' :                            (* E-Conv *)
      hsteq Ψ T T' → styped Φ Ψ Δ F e T → styped Φ Ψ Δ F e T'
  | st_pack Φ Ψ Δ F e lb m C T xs :                     (* E-Pack *)
      length xs = m → Forall (hyp_known Ψ) xs → bcs_hold (heqs Ψ) (hlt Ψ) C xs →
      hlbx_below_h Ψ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
      styped Φ Ψ Δ F e (ty_inst xs T) → styped Φ Ψ Δ F e (TEx lb m C T)
  | st_open Φ Ψ Δ F e i lb m C T U :                    (* E-Open *)
      Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
      styped (fhyps_pinst (pshift m) Φ)
        (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
        (<[i := Some T]> (lenv_pinst (pshift m) Δ))
        (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) →
      styped Φ Ψ Δ F e U.

(** ** From the source judgment into [typed], at every world

    The facts of the hypotheses are facts of every world's static
    theory, and program order is a rule, so no world law is needed. *)

Lemma heqs_seqs W Ψ x y : heqs Ψ x y → seqs W Ψ x y.
Proof. induction 1; eauto using seqs. Qed.

Lemma hfl_fl W Ψ Φ a b : hfl Ψ Φ a b → fl (FCtx W Ψ Φ) a b.
Proof.
  induction 1.
  - by apply fl_h.
  - by apply (fl_v (FCtx W Ψ Φ)).
  - eapply (fl_eql (FCtx W Ψ Φ)); [by apply heqs_seqs|done].
  - eapply (fl_eqr (FCtx W Ψ Φ)); [done|by apply heqs_seqs].
  - eapply (fl_trans (FCtx W Ψ Φ)); [exact IHhfl1|exact IHhfl2].
  - apply fl_po.
Qed.

Lemma hlt_slt W Ψ x y : hlt Ψ x y → slt W Ψ x y.
Proof. intros H. apply (hfl_fl W) in H. by apply fl_points in H. Qed.

Lemma hyp_known_skn W Ψ x : hyp_known Ψ x → skn W Ψ x.
Proof. by right. Qed.

Lemma hle_sle W Ψ x y : hle Ψ x y → sle W Ψ x y.
Proof. intros [H|H]; [left; by apply heqs_seqs|right; by apply hlt_slt]. Qed.

Lemma hsteq_steq W Ψ T : ∀ U, hsteq Ψ T U → steq W Ψ T U.
Proof.
  induction T; intros [] H; simpl in *; try done.
  - destruct H as (Hu & Hl & ? & ?). split_and!; auto.
    + destruct ub0, ub; simpl in *; [by apply heqs_seqs|done|done|done].
    + destruct lb0, lb; simpl in *; [by apply heqs_seqs|done|done|done].
  - destruct H. split; auto.
  - destruct H. split; auto.
  - destruct H as [Hx ?]. split; [by apply heqs_seqs|done].
Qed.

Lemma hub_below_s_ub W Ψ Φ ub F : hub_below_s Ψ Φ ub F → ub_below_s W Ψ Φ ub F.
Proof.
  destruct ub as [x|]; [|done]. intros (HP & Hφ & Hb). split_and!.
  - intros y Hy. by apply (hfl_fl W), HP.
  - intros φ Hφ'. by apply (hfl_fl W), Hφ.
  - exact Hb.
Qed.

Lemma hlb_below_hb_lb W Ψ lb H b :
  hlb_below_hb Ψ lb H b → lb_below_hb W Ψ lb H b.
Proof.
  destruct b; [done|]. destruct lb as [x|]; [|done].
  intros Hl y Hy. by apply (hle_sle W), Hl.
Qed.

Lemma hlbx_below_h_lbx W Ψ lb H b :
  hlbx_below_h Ψ lb H b → lbx_below_h W Ψ lb H b.
Proof.
  destruct lb as [| |x]; [done|done|]. intros [Hl Hb]. split; [|exact Hb].
  intros y Hy. by apply (hle_sle W), Hl.
Qed.

Lemma hkonst_ty W Ψ k T :
  konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k T →
  konst_ty (seqs W Ψ) (slt W Ψ) (skn W Ψ) k T.
Proof.
  apply konst_ty_mono;
    [apply heqs_seqs|apply hlt_slt|apply hyp_known_skn].
Qed.

Lemma tenv_heads_empty : tenv_heads ∅ = ∅.
Proof. unfold tenv_heads. by rewrite map_fold_empty. Qed.

(** The frames of a composing rule, with Θ empty. *)
Lemma sf_unionb_tenv0 F X b :
  sf_unionb F (tenv_heads ∅ ∪ X) b = sf_unionb F X b.
Proof. by rewrite tenv_heads_empty, (left_id_L ∅ (∪)). Qed.

Theorem styped_typed W Φ Ψ Δ F e T :
  styped Φ Ψ Δ F e T → typed W Φ Ψ ∅ Δ F e T.
Proof.
  induction 1.
  - by apply t_unit.
  - apply t_konst; [done|]. by apply hkonst_ty.
  - by apply t_var.
  - eapply t_lam; [done| |exact IHstyped].
    rewrite tenv_heads_empty, (left_id_L ∅ (∪)). by apply hlb_below_hb_lb.
  - eapply t_app; [apply tenv_comp_empty_r|done|by apply hub_below_s_ub| |done].
    by rewrite sf_unionb_tenv0.
  - eapply t_pair; [apply tenv_comp_empty_r|done| |done].
    by rewrite sf_unionb_tenv0.
  - eapply t_letu; [apply tenv_comp_empty_r|done| |done].
    by rewrite sf_unionb_tenv0.
  - eapply t_letp; [apply tenv_comp_empty_r|done| |done].
    by rewrite sf_unionb_tenv0.
  - by apply t_inj1.
  - by apply t_inj2.
  - eapply t_case; [apply tenv_comp_empty_r|done| |done|done].
    by rewrite sf_unionb_tenv0.
  - by eapply t_box.
  - by eapply t_wk.
  - by apply t_contract.
  - eapply t_conv; [by apply hsteq_steq|done].
  - eapply t_pack; [done| | | |done].
    + eapply Forall_impl; [done|]. intros x. apply hyp_known_skn.
    + eapply bcs_hold_mono; [apply heqs_seqs|apply hlt_slt|done].
    + by apply hlbx_below_h_lbx.
  - eapply t_open; [done|done|]. rewrite tenv_pinst_empty. exact IHstyped.
Qed.

(** ** From [typed] in a world of empty support back

    A world with empty support relates two points only by equality and
    program order, and knows no point, so its facts are facts of the
    hypotheses alone. *)

Section collapse.
  Context (W : world) (HW : world_wf W) (HN : w_names W = ∅).

  Lemma w_eq_nil x y : w_eq W x y → x = y.
  Proof.
    intros H. destruct (wf_eq_supp _ HW _ _ H) as [->|[Hx _]]; [done|].
    rewrite HN in Hx. by apply not_elem_of_empty in Hx.
  Qed.

  Lemma w_lt_nil x y : w_lt W x y → pofs x y.
  Proof.
    intros H. destruct (wf_lt_supp _ HW _ _ H) as [[Hn Ho]|[Hx _]]; [by split|].
    rewrite HN in Hx. by apply not_elem_of_empty in Hx.
  Qed.

  Lemma pt_known_nil x : ¬ pt_known W x.
  Proof. unfold pt_known. rewrite HN. apply not_elem_of_empty. Qed.

  Lemma seqs_heqs Ψ x y : seqs W Ψ x y → heqs Ψ x y.
  Proof.
    induction 1.
    - apply w_eq_nil in H as ->. apply he_refl.
    - by apply he_h.
    - apply he_refl.
    - by apply he_sym.
    - by eapply he_trans.
    - by apply he_shift.
    - by apply he_slot.
  Qed.

  Lemma fl_hfl Ψ Φ a b : fl (FCtx W Ψ Φ) a b → hfl Ψ Φ a b.
  Proof.
    induction 1.
    - by apply hl_pofs, w_lt_nil.
    - by apply hl_h.
    - by apply hl_v.
    - eapply hl_eql; [by apply seqs_heqs|done].
    - eapply hl_eqr; [done|by apply seqs_heqs].
    - by eapply hl_trans.
    - apply hl_po.
  Qed.

  Lemma slt_hlt Ψ x y : slt W Ψ x y → hlt Ψ x y.
  Proof. intros H. by apply fl_hfl in H. Qed.

  Lemma skn_hyp_known Ψ x : skn W Ψ x → hyp_known Ψ x.
  Proof. intros [H|H]; [by apply pt_known_nil in H|done]. Qed.

  Lemma sle_hle Ψ x y : sle W Ψ x y → hle Ψ x y.
  Proof. intros [H|H]; [left; by apply seqs_heqs|right; by apply slt_hlt]. Qed.

  Lemma steq_hsteq Ψ T : ∀ U, steq W Ψ T U → hsteq Ψ T U.
  Proof.
    induction T; intros [] H; simpl in *; try done.
    - destruct H as (Hu & Hl & ? & ?). split_and!; auto.
      + destruct ub0, ub; simpl in *; [by apply seqs_heqs|done|done|done].
      + destruct lb0, lb; simpl in *; [by apply seqs_heqs|done|done|done].
    - destruct H. split; auto.
    - destruct H. split; auto.
    - destruct H as [Hx ?]. split; [by apply seqs_heqs|done].
  Qed.

  Lemma ub_below_s_hub Ψ Φ ub F : ub_below_s W Ψ Φ ub F → hub_below_s Ψ Φ ub F.
  Proof.
    destruct ub as [x|]; [|done]. intros (HP & Hφ & Hb). split_and!.
    - intros y Hy. by apply fl_hfl, HP.
    - intros φ Hφ'. by apply fl_hfl, Hφ.
    - exact Hb.
  Qed.

  Lemma lb_below_hb_hlb Ψ lb H b : lb_below_hb W Ψ lb H b → hlb_below_hb Ψ lb H b.
  Proof.
    destruct b; [done|]. destruct lb as [x|]; [|done].
    intros Hl y Hy. by apply sle_hle, Hl.
  Qed.

  Lemma lbx_below_h_hlbx Ψ lb H b : lbx_below_h W Ψ lb H b → hlbx_below_h Ψ lb H b.
  Proof.
    destruct lb as [| |x]; [done|done|]. intros [Hl Hb]. split; [|exact Hb].
    intros y Hy. by apply sle_hle, Hl.
  Qed.

  Lemma konst_ty_h Ψ k T :
    konst_ty (seqs W Ψ) (slt W Ψ) (skn W Ψ) k T →
    konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k T.
  Proof.
    apply konst_ty_mono;
      [apply seqs_heqs|apply slt_hlt|apply skn_hyp_known].
  Qed.
End collapse.

(** An empty typing environment splits into two empty ones. *)
Lemma tenv_comp_empty_both R Θ1 Θ2 : tenv_comp R ∅ Θ1 Θ2 → Θ1 = ∅ ∧ Θ2 = ∅.
Proof.
  intros [Hj _]. apply tenv_join_dom in Hj. rewrite dom_empty_L in Hj.
  split; apply dom_empty_iff_L; set_solver.
Qed.

Theorem typed_styped W Φ Ψ Θ Δ F e T :
  world_wf W → w_names W = ∅ → typed W Φ Ψ Θ Δ F e T → Θ = ∅ → styped Φ Ψ Δ F e T.
Proof.
  intros HW HN Ht. induction Ht; intros HΘ.
  - by apply st_unit.
  - apply st_konst; [done|]. by eapply konst_ty_h.
  - by apply st_var.
  - exfalso. apply (f_equal dom) in HΘ.
    rewrite dom_singleton_L, dom_empty_L in HΘ. set_solver.
  - subst Θ. eapply st_lam; [done| |by apply IHHt].
    rewrite tenv_heads_empty, (left_id_L ∅ (∪)) in H0.
    by eapply lb_below_hb_hlb.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply st_app; [done|by eapply ub_below_s_hub| |by apply IHHt2].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply st_pair; [done| |by apply IHHt2].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply st_letu; [done| |by apply IHHt2].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply st_letp; [done| |by apply IHHt2].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - by apply st_inj1, IHHt.
  - by apply st_inj2, IHHt.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply st_case; [done| |by apply IHHt2|by apply IHHt3].
    rewrite sf_unionb_tenv0 in IHHt1. by apply IHHt1.
  - eapply st_box; [done|done|by apply IHHt].
  - eapply st_wk; [done|by apply IHHt].
  - by apply st_contract, IHHt.
  - eapply st_conv; [by eapply steq_hsteq|by apply IHHt].
  - eapply st_pack; [done| | | |by apply IHHt].
    + eapply Forall_impl; [done|]. intros x. by eapply skn_hyp_known.
    + eapply bcs_hold_mono; [by eapply seqs_heqs|by eapply slt_hlt|done].
    + by eapply lbx_below_h_hlbx.
  - subst Θ. eapply st_open; [done|done|]. apply IHHt. apply tenv_pinst_empty.
Qed.

(** The two judgments agree on the derivations of a source program. *)
Corollary styped_iff W Φ Ψ Δ F e T :
  world_wf W → w_names W = ∅ →
  styped Φ Ψ Δ F e T ↔ typed W Φ Ψ ∅ Δ F e T.
Proof.
  intros HW HN. split; [apply styped_typed|].
  intros Ht. by eapply typed_styped.
Qed.
