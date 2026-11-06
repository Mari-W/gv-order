(** * The source instance of the term judgment (static-system.md §2)

    There is one term judgment, [typed] (static/Typing.v). [styped Φ Ψ Δ
    F t T] is its instance at Θ = ∅ and the empty world [wnil], the
    judgment of a self-contained single-threaded source program. Γ is
    then the hypotheses Ψ and the future hypotheses Φ, and no constant
    occurs in it.

    Why the world is a don't-care there. A well-formed world relates two
    points only when both roots lie in its support ([wf_eq_supp],
    [wf_lt_supp]), or when the two points share a name and the offset
    grows. Every support name is a point constant ([wf_names_const]),
    so a point rooted at a point variable is related by no world beyond
    program order, and no world knows it ([pt_known]). A source program
    has no channel constants, its typing environment Θ stays empty, and
    every point it mentions is rooted at a variable bound by an
    enclosing binder. Program order is a rule of the fact theory
    ([fl_po]). [typed_world_transfer] moves a derivation with Θ = ∅ from
    a world of empty support to any world, so [styped_typed] sends a
    source derivation to every world, and [typed_styped] reads one back.
    Channel constants (E-Ch) and the process layer ([ptyped], P-Term,
    P-Connect) use worlds with constants. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.Typing.

(** Branch no-eq: [w_eq W] abbreviates equality and leaves W untyped. *)
Implicit Types W : world.


Set Default Proof Using "All".

(** ** The fact theory of the hypotheses

    [heqs Ψ] and [hfl Ψ Φ] are [seqs] and [fl] without the generators
    of a world. Knownness is [hyp_known], a point rooted at an instance
    point of a hypothesis, which is what static-system.md asks of a
    point before [new] or force may name it. *)

Inductive heqs (Ψ : hyps) : point → point → Prop :=
  | he_refl x : heqs Ψ x x
  | he_sym x y : heqs Ψ x y → heqs Ψ y x
  | he_trans x y z : heqs Ψ x y → heqs Ψ y z → heqs Ψ x z
  | he_shift x y : heqs Ψ x y → heqs Ψ (pt_shift 1 x) (pt_shift 1 y)
  | he_payload x y i : heqs Ψ x y → heqs Ψ (pt_payload x i) (pt_payload y i)
  | he_dual x y : heqs Ψ x y → heqs Ψ (pt_dual x) (pt_dual y).

Inductive hfl (Ψ : hyps) (Φ : fhyps) : node → node → Prop :=
  | hl_h x y : hyp_fact Ψ (FLt x y) → hfl Ψ Φ (NP x) (NP y)
  | hl_v φ u : Φ !! φ = Some (Some u) → hfl Ψ Φ (NP u) (NV φ)
  | hl_eql x x' b : heqs Ψ x x' → hfl Ψ Φ (NP x') b → hfl Ψ Φ (NP x) b
  | hl_eqr a y y' : hfl Ψ Φ a (NP y') → heqs Ψ y' y → hfl Ψ Φ a (NP y)
  | hl_trans a y b : hfl Ψ Φ a (NP y) → hfl Ψ Φ (NP y) b → hfl Ψ Φ a b
  | hl_po x : hfl Ψ Φ (NP x) (NP (pt_shift 1 x))
  | hl_dpo x : hfl Ψ Φ (NP x) (NP (pt_shift 1 (pt_dual x))).

Definition hlt (Ψ : hyps) (x y : point) : Prop := hfl Ψ ∅ (NP x) (NP y).

Definition hle (Ψ : hyps) (x y : point) : Prop := heqs Ψ x y ∨ hlt Ψ x y.

Lemma hl_po_n Ψ Φ x k : hfl Ψ Φ (NP x) (NP (pt_shift (S k) x)).
Proof.
  induction k as [|k IH]; [apply hl_po|].
  eapply hl_trans; [exact IH|]. rewrite <-(pt_shift_S (S k) x). apply hl_po.
Qed.

(** Program order between two points of one name. *)
Lemma hl_ppo Ψ Φ x y : ppo x y → hfl Ψ Φ (NP x) (NP y).
Proof. induction 1; [apply hl_po|apply hl_dpo|by eapply hl_trans]. Qed.

Lemma hl_pofs Ψ Φ x y : pofs x y → hfl Ψ Φ (NP x) (NP y).
Proof. intros H. by apply hl_ppo, pofs_ppo. Qed.

Lemma hlt_pofs Ψ x y : pofs x y → hlt Ψ x y.
Proof. apply hl_pofs. Qed.

Lemma hlt_po Ψ x : hlt Ψ x (pt_shift 1 x).
Proof. apply hl_po. Qed.

Lemma hlt_trans Ψ x y z : hlt Ψ x y → hlt Ψ y z → hlt Ψ x z.
Proof. exact (hl_trans Ψ ∅ (NP x) y (NP z)). Qed.

(** A fact between two points holds under any future hypotheses. *)
Lemma hfl_weaken Ψ Φ a b : hfl Ψ ∅ a b → hfl Ψ Φ a b.
Proof.
  induction 1.
  - by apply hl_h.
  - by rewrite lookup_empty in H.
  - by eapply hl_eql.
  - by eapply hl_eqr.
  - by eapply hl_trans.
  - apply hl_po.
  - apply hl_dpo.
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
  | LNone => H = ∅ ∧ b = false
  | LPt x => (∀ y, y ∈ H → hle Ψ x y) ∧ b = false
  end.

Definition hub_below_s (Ψ : hyps) (Φ : fhyps) (ub : option point) (F : sfuture) : Prop :=
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
  | TBox _ _ _ _, TBox _ _ _ _ => teq T U
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

(** ** The empty world and the source instance

    There is one term judgment, [typed W Φ Ψ Θ Δ F t T] (static/Typing.v),
    Θ ; Γ ; Δ ⊢_F t : T of the paper. Its fact context Γ is the world W
    (the ground facts between point constants), the hypotheses Ψ and the
    future hypotheses Φ, read through [FCtx W Ψ Φ]. A source program is
    the instance with Θ = ∅ and the empty world [wnil], so Γ mentions no
    constant. [styped] abbreviates that instance, it is no second rule
    set. A running thread is typed by P-Term with Γ := W.

    The source instance reads no ground fact: the world is a don't-care
    for a derivation with Θ = ∅ ([typed_world_transfer] below), because a
    well-formed world of empty support relates points only by program
    order, which is a rule of the fact theory ([fl_po]), and every point
    of a source derivation is rooted at a variable. *)

Definition wnil : world := wgen ∅ (λ _ _, False) (λ _ _, False).

Lemma wnil_strict : strict wnil.
Proof.
  split; [apply wgen_wf; [set_solver|done|done]|].
  assert (∀ x y, geq (λ _ _ : point, False) x y → x = y) as Hq.
  { induction 1; subst; done. }
  assert (∀ x y, glt (λ _ _ : point, False) (λ _ _ : point, False) x y → pofs x y) as Hl.
  { induction 1 as [x y []|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2|x].
    - apply pofs_shift.
    - apply Hq in Hx, Hy. by subst.
    - by eapply pofs_trans.
    - unfold pofs, pt_shift. simpl. split; [done|lia]. }
  intros x H. exact (pofs_irrefl x (Hl x x H)).
Qed.

Lemma wnil_names : w_names wnil = ∅.
Proof. done. Qed.

(** The source instance Θ = ∅ ; Ψ, Φ ; Δ ⊢_F t : T of the one judgment. *)
Definition styped (Φ : fhyps) (Ψ : hyps) (Δ : lenv) (F : sfuture) (e : expr) (T : ty) : Prop :=
  typed wnil Φ Ψ ∅ Δ F e T.

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
  - apply fl_dpo.
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

(** The futures of a composing rule, with Θ empty. *)
Lemma sf_unionb_tenv0 F X b :
  sf_unionb F (tenv_heads ∅ ∪ X) b = sf_unionb F X b.
Proof. by rewrite tenv_heads_empty, (left_id_L ∅ (∪)). Qed.

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
    intros H. destruct (wf_lt_supp _ HW _ _ H) as [Hp|[Hx _]]; [by apply ppo_pofs|].
    rewrite HN in Hx. by apply not_elem_of_empty in Hx.
  Qed.

  Lemma pt_known_nil x : ¬ pt_known W x.
  Proof. unfold pt_known. rewrite HN. apply not_elem_of_empty. Qed.

  Lemma seqs_heqs Ψ x y : seqs W Ψ x y → heqs Ψ x y.
  Proof.
    induction 1.
    - apply w_eq_nil in H as ->. apply he_refl.
    - apply he_refl.
    - by apply he_sym.
    - by eapply he_trans.
    - by apply he_shift.
    - by apply he_payload.
    - by apply he_dual.
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
    - apply hl_dpo.
  Qed.

  Lemma slt_hlt
 Ψ x y : slt W Ψ x y → hlt Ψ x y.
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

(** The world is a don't-care for a derivation with Θ = ∅: a derivation
    in a well-formed world of empty support is one in every world. Each
    side condition passes through the fact theory of the hypotheses
    alone ([heqs], [hfl]). *)
Theorem typed_world_transfer W1 W2 Φ Ψ Θ Δ F e T :
  world_wf W1 → w_names W1 = ∅ → typed W1 Φ Ψ Θ Δ F e T → Θ = ∅ →
  typed W2 Φ Ψ ∅ Δ F e T.
Proof.
  intros HW HN Ht. induction Ht; intros HΘ.
  - by apply t_unit.
  - apply t_const; [done| |done]. apply hkonst_ty. by apply (konst_ty_h W1 HW HN).
  - by apply t_var.
  - exfalso. apply (f_equal dom) in HΘ.
    rewrite dom_singleton_L, dom_empty_L in HΘ. set_solver.
  - subst Θ. eapply t_abs; [done| |by apply IHHt].
    apply hlb_below_hb_lb. by apply (lb_below_hb_hlb W1 HW HN).
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply t_app; [apply tenv_comp_empty_r|done| |by apply IHHt1|by apply IHHt2].
    apply hub_below_s_ub. by apply (ub_below_s_hub W1 HW HN).
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply t_pair; [apply tenv_comp_empty_r|done|by apply IHHt1|by apply IHHt2].
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply t_letstar; [apply tenv_comp_empty_r|done|by apply IHHt1|by apply IHHt2].
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply t_letpair; [apply tenv_comp_empty_r|done|by apply IHHt1|by apply IHHt2].
  - by apply t_inj1, IHHt.
  - by apply t_inj2, IHHt.
  - subst Θ. destruct (tenv_comp_empty_both _ _ _ H) as [-> ->].
    eapply t_case; [apply tenv_comp_empty_r|done|by apply IHHt1|by apply IHHt2|by apply IHHt3].
  - eapply t_exp; [done|done|]. intros ss Hss Hsc. by apply H2.
  - eapply t_weak; [done|by apply IHHt].
  - by apply t_contract, IHHt.
  - eapply t_conv; [apply hsteq_steq; by apply (steq_hsteq W1 HW HN)|by apply IHHt].
  - eapply t_pack; [done| | | |by apply IHHt].
    + eapply Forall_impl; [done|]. intros x Hx. apply hyp_known_skn.
      by apply (skn_hyp_known W1 HW HN).
    + eapply bcs_hold_mono; [| |done].
      * intros x y Hxy. apply heqs_seqs. by apply (seqs_heqs W1 HW HN).
      * intros x y Hxy. apply hlt_slt. by apply (slt_hlt W1 HW HN).
    + apply hlbx_below_h_lbx. by apply (lbx_below_h_hlbx W1 HW HN).
  - subst Θ. eapply t_open; [done|done|]. rewrite tenv_pinst_empty.
    apply IHHt. apply tenv_pinst_empty.
Qed.

(** The source instance holds in every world. *)
Theorem styped_typed W Φ Ψ Δ F e T :
  styped Φ Ψ Δ F e T → typed W Φ Ψ ∅ Δ F e T.
Proof.
  intros H. apply (typed_world_transfer wnil W _ _ ∅); [apply wnil_strict|apply wnil_names|exact H|done].
Qed.

Theorem typed_styped W Φ Ψ Θ Δ F e T :
  world_wf W → w_names W = ∅ → typed W Φ Ψ Θ Δ F e T → Θ = ∅ → styped Φ Ψ Δ F e T.
Proof. intros HW HN Ht HΘ. by apply (typed_world_transfer W wnil _ _ Θ). Qed.

(** The source instance agrees with the judgment at every world of empty support. *)
Corollary styped_iff W Φ Ψ Δ F e T :
  world_wf W → w_names W = ∅ →
  styped Φ Ψ Δ F e T ↔ typed W Φ Ψ ∅ Δ F e T.
Proof.
  intros HW HN. split; [apply styped_typed|].
  intros Ht. by eapply typed_styped.
Qed.
