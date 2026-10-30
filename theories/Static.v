(** * The static system (spec §9, with sharp edges 52 and 53)

    Θ; Δ ⊢^F_G t : T and Σ ⊢_G p : T. The facts G enter through the
    world W_G they generate: the judgments are indexed by a world W.
    Every side condition on points is read in the fact theory over W
    and the hypotheses of the enclosing boxes ([seqs], [slt], sharp
    edges 64, 65). Fundamental and soundness ask W strict.

    Sharp edges 54 (option D) and 56: the fresh μ of E-Abs and E-Exp is
    a frame variable φ with the single hypothesis u ≺ φ, so both rules
    have one premise about the body at the same world W. E-Exp types
    the body once, with the box's ιs as the point variables 0, …, m-1
    and the outer environment and hypotheses shifted past them. E-Const
    asks the payload of send and recv to be scoped by its binders
    ([kscoped]). [typed_pinst] substitutes points for point variables.
    [typed_sem_rules] does that and instantiates φ by any frame above u at
    any later world in one induction, and yields the semantic rules
    [sem_rules] of SemRules.v, whose fundamental theorem
    [sem_rules_fundamental] is the old one. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export SemRules.

Set Default Proof Using "All".

(** ** Lemmas on available variables, for [typed_term_wf_s] *)

Lemma lenv_wk_avail Δ' Δ x :
  lenv_wk Δ' Δ → lenv_avail Δ' x → lenv_avail Δ x.
Proof.
  intros Hwk. revert x.
  induction Hwk as [|o Δ' Δ Hwk IH|U Δ' Δ Hu Hwk IH];
    intros x (T & Hx); [by exists T| |].
  - destruct x as [|x']; simpl in *; simplify_eq/=; [by exists T|].
    destruct (IH x') as (T' & ?); [by exists T|]. by exists T'.
  - destruct x as [|x']; simpl in *; simplify_eq/=.
    destruct (IH x') as (T' & ?); [by exists T|]. by exists T'.
Qed.

Lemma lenv_wk_avail_lin Δ' Δ x :
  lenv_wk Δ' Δ → lenv_avail_lin Δ x → lenv_avail_lin Δ' x.
Proof.
  intros Hwk. revert x.
  induction Hwk as [|o Δ' Δ Hwk IH|U Δ' Δ Hu Hwk IH];
    intros x (T & Hx & Hnb); [by exists T| |].
  - destruct x as [|x']; simpl in *; simplify_eq/=.
    + exists T. auto.
    + destruct (IH x') as (T' & ? & ?); [exists T; auto|]. exists T'. auto.
  - destruct x as [|x']; simpl in *; simplify_eq/=; [by destruct (Hnb Hu)|].
    destruct (IH x') as (T' & ? & ?); [exists T; auto|]. exists T'. auto.
Qed.

Lemma lenv_empty_no_avail Δ x : lenv_empty Δ → ¬ lenv_avail Δ x.
Proof.
  intros HΔ (T & Hx). apply list_elem_of_lookup_2 in Hx.
  apply HΔ in Hx. done.
Qed.


(** ** The finitary static system (sharp edges 54, option D)

    E-Abs and E-Exp type the body under the frame {φ} for a fresh
    frame variable φ, with the single hypothesis u ≺ φ. A frame is a
    set of points and at most one frame variable: the body of λ or box
    starts at {φ} and the other rules only add points. φ occurs only in
    frames and in the hypotheses Φ, never in a type, an environment or
    the world, so it is never a point that [new] or force could alias.
    x ≺ φ holds when x ≼ u in W for the hypothesis u ≺ φ. E-Exp types
    the body with the ιs as point variables (sharp edges 57). *)

Notation sframe := (gset point * option nat)%type.
Notation fhyps := (gmap nat (option point)).

(** F[ρ]: replace the frame variable by a concrete frame. *)
Definition sf_inst (ρ : nat → gset point) (F : sframe) : gset point :=
  F.1 ∪ match F.2 with Some φ => ρ φ | None => ∅ end.

Definition sf_union (F : sframe) (X : gset point) : sframe := (F.1 ∪ X, F.2).

(** Hypotheses (sharp edges 58, 61, 65). Inside a box body the
    constraint of every enclosing box is a hypothesis (C, xs): every
    fact of C[xs/ιs] holds. The body's own hypothesis has the ιs as
    instance. The points of an instance are known, so new may create a
    channel at a point with the root of an instance point (sharp edges
    59). *)
Notation hyps := (list (bcs * list point)).

Definition hyp_fact (Ψ : hyps) (g : fact) : Prop :=
  ∃ C xs, (C, xs) ∈ Ψ ∧ ∃ g0, bcs_open (length xs) C g0 ∧ g = fact_map (pt_inst (plist xs)) g0.

Definition hyp_known (Ψ : hyps) (x : point) : Prop :=
  ∃ C xs y, (C, xs) ∈ Ψ ∧ y ∈ xs ∧ pt_root x = pt_root y.

(** Static knownness: known to W, or rooted at an instance point. *)
Definition skn (W : world) (Ψ : hyps) (x : point) : Prop := pt_known W x ∨ hyp_known Ψ x.

Definition hyps_inst (σ : nat → point) (Ψ : hyps) : hyps :=
  (λ g : bcs * list point, (bcs_inst σ g.1, pt_inst σ <$> g.2)) <$> Ψ.

Definition hyps_hold (eq lt : point → point → Prop) (pk : point → Prop) (Ψ : hyps) : Prop :=
  ∀ C xs, (C, xs) ∈ Ψ → bcs_hold eq lt C xs ∧ Forall pk xs.

(** The ιs of a box body, as an instance. *)
Definition ids (m : nat) : list point := pvar <$> List.seq 0 m.

(** ** One fact theory (sharp edges 64, 65)

    Every fact the static system reads comes from two judgments over
    the context Γ = (W, Ψ, Φ). Γ ⊢ x ≡ y ([seqs]) is the least
    congruence for successor and carried roots that contains ≡ of W and
    the ≡ facts of the hypotheses. Γ ⊢ a ≺ b ([fl]) is over nodes,
    which are points and frame variables. It has the order of W, the ≺
    facts of the hypotheses and u ≺ φ for every frame hypothesis of Φ,
    and it is closed under Γ ⊢ ≡ and under transitivity through
    points. Without hypotheses the two are ≡ and ≺ of W ([seqs_nil],
    [slt_nil]). [fl_map] carries derivations of both along a map of
    the generators, and it is the one lemma behind point substitution
    and frame instantiation. *)

Inductive node := NP (x : point) | NV (φ : nat).

Record fctx := FCtx { fc_W : world; fc_hyps : hyps; fc_fv : fhyps }.

Inductive seqs (W : world) (Ψ : hyps) : point → point → Prop :=
  | se_w x y : w_eq W x y → seqs W Ψ x y
  | se_h x y : hyp_fact Ψ (FEq x y) → seqs W Ψ x y
  | se_refl x : seqs W Ψ x x
  | se_sym x y : seqs W Ψ x y → seqs W Ψ y x
  | se_trans x y z : seqs W Ψ x y → seqs W Ψ y z → seqs W Ψ x z
  | se_shift x y : seqs W Ψ x y → seqs W Ψ (pt_shift 1 x) (pt_shift 1 y)
  | se_slot x y i : seqs W Ψ x y → seqs W Ψ (pt_slot x i) (pt_slot y i).

Inductive fl (Γ : fctx) : node → node → Prop :=
  | fl_w x y : w_lt (fc_W Γ) x y → fl Γ (NP x) (NP y)
  | fl_h x y : hyp_fact (fc_hyps Γ) (FLt x y) → fl Γ (NP x) (NP y)
  | fl_v φ u : fc_fv Γ !! φ = Some (Some u) → fl Γ (NP u) (NV φ)
  | fl_eql x x' b : seqs (fc_W Γ) (fc_hyps Γ) x x' → fl Γ (NP x') b → fl Γ (NP x) b
  | fl_eqr a y y' : fl Γ a (NP y') → seqs (fc_W Γ) (fc_hyps Γ) y' y → fl Γ a (NP y)
  | fl_trans a y b : fl Γ a (NP y) → fl Γ (NP y) b → fl Γ a b.

(** A map of the generators maps every derived fact, ≡ along [fp] into
    Q and ≺ along [f] into R. *)
Lemma fl_map Γ (Q : point → point → Prop) (R : node → node → Prop)
    (fp : point → point) (f : node → node) :
  (∀ x y, w_eq (fc_W Γ) x y → Q (fp x) (fp y)) →
  (∀ x y, hyp_fact (fc_hyps Γ) (FEq x y) → Q (fp x) (fp y)) →
  (∀ x, Q (fp x) (fp x)) →
  (∀ x y, Q (fp x) (fp y) → Q (fp y) (fp x)) →
  (∀ x y z, Q (fp x) (fp y) → Q (fp y) (fp z) → Q (fp x) (fp z)) →
  (∀ x y, Q (fp x) (fp y) → Q (fp (pt_shift 1 x)) (fp (pt_shift 1 y))) →
  (∀ x y i, Q (fp x) (fp y) → Q (fp (pt_slot x i)) (fp (pt_slot y i))) →
  (∀ x y, w_lt (fc_W Γ) x y → R (f (NP x)) (f (NP y))) →
  (∀ x y, hyp_fact (fc_hyps Γ) (FLt x y) → R (f (NP x)) (f (NP y))) →
  (∀ φ u, fc_fv Γ !! φ = Some (Some u) → R (f (NP u)) (f (NV φ))) →
  (∀ x x' b, Q (fp x) (fp x') → R (f (NP x')) (f b) → R (f (NP x)) (f b)) →
  (∀ a y y', R (f a) (f (NP y')) → Q (fp y') (fp y) → R (f a) (f (NP y))) →
  (∀ a y b, R (f a) (f (NP y)) → R (f (NP y)) (f b) → R (f a) (f b)) →
  (∀ x y, seqs (fc_W Γ) (fc_hyps Γ) x y → Q (fp x) (fp y)) ∧
  (∀ a b, fl Γ a b → R (f a) (f b)).
Proof.
  intros Hew Heh Her Hes Het Hesh Hesl Hw Hh Hv Hl Hr Ht.
  assert (∀ x y, seqs (fc_W Γ) (fc_hyps Γ) x y → Q (fp x) (fp y)) as Hq
    by (induction 1; eauto).
  split; [done|]. induction 1; eauto.
Qed.

(** The facts between points. They do not depend on Φ ([fl_points]). *)
Definition slt (W : world) (Ψ : hyps) (x y : point) : Prop := fl (FCtx W Ψ ∅) (NP x) (NP y).

Definition sle (W : world) (Ψ : hyps) (x y : point) : Prop :=
  seqs W Ψ x y ∨ slt W Ψ x y.

Lemma sl_w W Ψ x y : w_lt W x y → slt W Ψ x y.
Proof. exact (fl_w (FCtx W Ψ ∅) x y). Qed.
Lemma sl_h W Ψ x y : hyp_fact Ψ (FLt x y) → slt W Ψ x y.
Proof. exact (fl_h (FCtx W Ψ ∅) x y). Qed.
Lemma sl_eql W Ψ x x' y : seqs W Ψ x x' → slt W Ψ x' y → slt W Ψ x y.
Proof. exact (fl_eql (FCtx W Ψ ∅) x x' (NP y)). Qed.
Lemma sl_eqr W Ψ x y y' : slt W Ψ x y' → seqs W Ψ y' y → slt W Ψ x y.
Proof. exact (fl_eqr (FCtx W Ψ ∅) (NP x) y y'). Qed.
Lemma sl_trans W Ψ x y z : slt W Ψ x y → slt W Ψ y z → slt W Ψ x z.
Proof. exact (fl_trans (FCtx W Ψ ∅) (NP x) y (NP z)). Qed.

Lemma fl_points W Ψ Φ x y : fl (FCtx W Ψ Φ) (NP x) (NP y) ↔ slt W Ψ x y.
Proof.
  split.
  - intros H. change (match NP x, NP y with NP x, NP y => slt W Ψ x y | _, _ => True end).
    refine (proj2 (fl_map (FCtx W Ψ Φ) (seqs W Ψ)
      (λ a b, match a, b with NP x, NP y => slt W Ψ x y | _, _ => True end) id id
      _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ H); unfold id; simpl; eauto using seqs.
    + apply sl_w.
    + apply sl_h.
    + intros x0 x' [] ? ?; [by eapply sl_eql|done].
    + intros [] y0 y' ? ?; [by eapply sl_eqr|done].
    + intros [] y0 []; try done. apply sl_trans.
  - refine (proj2 (fl_map (FCtx W Ψ ∅) (seqs W Ψ) (fl (FCtx W Ψ Φ)) id id
      _ _ _ _ _ _ _ _ _ _ _ _ _) _ _); unfold id; simpl; eauto using seqs.
    + exact (fl_w (FCtx W Ψ Φ)).
    + exact (fl_h (FCtx W Ψ Φ)).
    + intros φ u H. by rewrite lookup_empty in H.
    + exact (fl_eql (FCtx W Ψ Φ)).
    + exact (fl_eqr (FCtx W Ψ Φ)).
    + exact (fl_trans (FCtx W Ψ Φ)).
Qed.

Definition lb_below_h (W : world) (Ψ : hyps) (lb : option point)
    (H : gset point) : Prop :=
  match lb with None => H = ∅ | Some x => ∀ y, y ∈ H → sle W Ψ x y end.

(** Without hypotheses the static ≡ and ≺ are those of W. *)
Lemma seqs_nil W x y : world_wf W → seqs W [] x y → w_eq W x y.
Proof.
  intros HW. induction 1 as [x y H|x y (? & ? & H & _)| | | | |].
  - done.
  - by apply elem_of_nil in H.
  - apply (wf_eq_refl _ HW).
  - by apply (wf_eq_sym _ HW).
  - by eapply (wf_eq_trans _ HW).
  - by apply (wf_eq_shift _ HW).
  - by apply (wf_eq_slot _ HW).
Qed.

Lemma slt_nil W x y : world_wf W → slt W [] x y → w_lt W x y.
Proof.
  intros HW H. change (match NP x, NP y with NP x, NP y => w_lt W x y | _, _ => True end).
  refine (proj2 (fl_map (FCtx W [] ∅) (w_eq W)
    (λ a b, match a, b with NP x, NP y => w_lt W x y | _, _ => True end) id id
    _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ H); clear H; unfold id; simpl; try done.
  - intros ? ? (? & ? & H & _). by apply elem_of_nil in H.
  - apply (wf_eq_refl _ HW).
  - apply (wf_eq_sym _ HW).
  - apply (wf_eq_trans _ HW).
  - apply (wf_eq_shift _ HW).
  - apply (wf_eq_slot _ HW).
  - intros ? ? (? & ? & H & _). by apply elem_of_nil in H.
  - intros x0 x' [] Hx H; [|done].
    eapply (wf_lt_eq _ HW); [exact Hx|exact H|apply (wf_eq_refl _ HW)].
  - intros [] y0 y' H Hy; [|done].
    eapply (wf_lt_eq _ HW); [apply (wf_eq_refl _ HW)|exact H|exact Hy].
  - intros [] y0 []; try done. apply (wf_lt_trans _ HW).
Qed.

(** A hypothesis of Ψ holds in the static ≡ and ≺, and its instance
    points are statically known. *)
Lemma hyp_in_fact W Ψ C xs : (C, xs) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) C xs.
Proof.
  intros H g Hg. destruct g as [x y|x y]; simpl; [apply sl_h|apply se_h];
    exists C, xs; (split; [done|]); eexists; (split; [exact Hg|done]).
Qed.

Lemma hyp_in_known W Ψ C xs : (C, xs) ∈ Ψ → Forall (skn W Ψ) xs.
Proof. intros H. apply Forall_forall. intros y Hy. right. by exists C, xs, y. Qed.

Lemma hyps_hold_sub W Ψ Ψ' :
  (∀ g, g ∈ Ψ → g ∈ Ψ') → hyps_hold (seqs W Ψ') (slt W Ψ') (skn W Ψ') Ψ.
Proof. intros H C xs Hg. split; [apply (hyp_in_fact W Ψ' C xs)|apply (hyp_in_known W Ψ' C xs)]; auto. Qed.

Lemma hyps_hold_mono (eq eq' lt lt' : point → point → Prop) (pk pk' : point → Prop) Ψ :
  (∀ x y, eq x y → eq' x y) → (∀ x y, lt x y → lt' x y) → (∀ x, pk x → pk' x) →
  hyps_hold eq lt pk Ψ → hyps_hold eq' lt' pk' Ψ.
Proof.
  intros He Hl Hk H C xs Hg. destruct (H C xs Hg) as [H1 H2].
  split; [by eapply bcs_hold_mono|by eapply Forall_impl].
Qed.

Lemma hyps_hold_wext W W' Ψ :
  wext W W' → hyps_hold (w_eq W) (w_lt W) (pt_known W) Ψ → hyps_hold (w_eq W') (w_lt W') (pt_known W') Ψ.
Proof.
  intros (HN & He & Hl & _). apply hyps_hold_mono; [exact He|exact Hl|].
  intros x Hx. unfold pt_known in *. clear -HN Hx. set_solver.
Qed.

Lemma hyps_hold_app (eq lt : point → point → Prop) (pk : point → Prop) Ψ1 Ψ2 :
  hyps_hold eq lt pk Ψ1 → hyps_hold eq lt pk Ψ2 → hyps_hold eq lt pk (Ψ1 ++ Ψ2).
Proof. intros H1 H2 C xs Hg. apply elem_of_app in Hg as [Hg|Hg]; auto. Qed.

Lemma hyps_inst_app σ Ψ1 Ψ2 : hyps_inst σ (Ψ1 ++ Ψ2) = hyps_inst σ Ψ1 ++ hyps_inst σ Ψ2.
Proof. apply fmap_app. Qed.

Lemma hyps_inst_single σ C xs :
  hyps_inst σ [(C, xs)] = [(bcs_inst σ C, pt_inst σ <$> xs)].
Proof. done. Qed.

Lemma skn_root W Ψ x y : pt_root x = pt_root y → skn W Ψ x → skn W Ψ y.
Proof.
  intros E [H|(C & xs & z & Hg & Hz & Hr)].
  - left. unfold pt_known in *. by rewrite <-E.
  - right. exists C, xs, z. split_and!; [done|done|congruence].
Qed.

(** {u} ≺ F, one judgment for the points of F and its frame variable. *)
Definition ub_below_s (W : world) (Ψ : hyps) (Φ : fhyps)
    (ub : option point) (F : sframe) : Prop :=
  match ub with
  | None => True
  | Some x => (∀ y, y ∈ F.1 → fl (FCtx W Ψ Φ) (NP x) (NP y)) ∧
              (∀ φ, F.2 = Some φ → fl (FCtx W Ψ Φ) (NP x) (NV φ))
  end.

(** The frame variable part read as x ≼ u for the hypothesis u ≺ φ. *)
Lemma ub_below_s_intro W Ψ Φ x P o :
  (∀ y, y ∈ P → slt W Ψ x y) →
  match o with Some φ => ∃ u, Φ !! φ = Some (Some u) ∧ sle W Ψ x u | None => True end →
  ub_below_s W Ψ Φ (Some x) (P, o).
Proof.
  intros H1 H2. split; simpl.
  - intros y Hy. apply fl_points. by apply H1.
  - intros φ ->. destruct H2 as (u & Hu & [Heq|Hlt]).
    + apply (fl_eql (FCtx W Ψ Φ) _ u); [done|]. by apply (fl_v (FCtx W Ψ Φ)).
    + apply (fl_trans (FCtx W Ψ Φ) _ u); [by apply fl_points|]. by apply (fl_v (FCtx W Ψ Φ)).
Qed.

(** ρ meets the hypotheses: {u} ≺_W ρ(φ) for every u ≺ φ in Φ. *)
Definition inst_ok (W : world) (Φ : fhyps) (ρ : nat → gset point) : Prop :=
  ∀ φ u, Φ !! φ = Some u → ub_below W u (ρ φ).

(** ** Point substitution (sharp edges 56, 57)

    The body of a box is typed once, with the box's ιs as the point
    variables 0, …, m-1 and every outer point variable shifted past
    them. [typed_sem_rules] substitutes points for the variables. A
    payload ∃ιs.T is scoped: its points are constants or among its m
    binders, so substitution commutes with [payload_at]. *)

Definition pshift (m : nat) : nat → point := λ a, pvar (a + m).

Lemma pt_shift_0 x : pt_shift 0 x = x.
Proof. destruct x as [p o]. unfold pt_shift. simpl. f_equal. lia. Qed.

Lemma pt_inst_pvar_at σ a : pt_inst σ (pvar a) = σ a.
Proof. unfold pt_inst, pvar. simpl. apply pt_shift_0. Qed.

Lemma pt_inst_shift σ n x : pt_inst σ (pt_shift n x) = pt_shift n (pt_inst σ x).
Proof.
  destruct x as [p o]. unfold pt_inst, pt_shift. simpl.
  destruct (pn_inst σ p). simpl. f_equal. lia.
Qed.

Lemma pt_inst_slot σ x i : pt_inst σ (pt_slot x i) = pt_slot (pt_inst σ x) i.
Proof. destruct x as [p o]. unfold pt_inst, pt_slot, pt_shift. simpl. done. Qed.

Lemma pn_inst_comp τ σ p : pt_inst τ (pn_inst σ p) = pn_inst (pt_inst τ ∘ σ) p.
Proof.
  induction p as [a|a|p IH b i]; simpl; [done|done|].
  by rewrite pt_inst_slot, pt_inst_shift, IH.
Qed.

Lemma pt_inst_comp τ σ x : pt_inst τ (pt_inst σ x) = pt_inst (pt_inst τ ∘ σ) x.
Proof. unfold pt_inst at 2 3. by rewrite pt_inst_shift, pn_inst_comp. Qed.

Lemma pn_inst_ext_root σ τ p :
  (∀ a, pn_root p = NVar a → σ a = τ a) → pn_inst σ p = pn_inst τ p.
Proof. induction p as [a|a|p IH b i]; simpl; intros H; [done|by apply H|by rewrite IH]. Qed.

Lemma pt_inst_ext_root σ τ x :
  (∀ a, pt_root x = NVar a → σ a = τ a) → pt_inst σ x = pt_inst τ x.
Proof. intros H. unfold pt_inst. f_equal. by apply pn_inst_ext_root. Qed.

Lemma pt_inst_ext σ τ x : (∀ a, σ a = τ a) → pt_inst σ x = pt_inst τ x.
Proof. intros H. apply pt_inst_ext_root. auto. Qed.

Lemma pn_inst_pvar p : pn_inst pvar p = Pt p 0.
Proof. induction p as [a|a|p IH b i]; simpl; [done|done|]. by rewrite IH. Qed.

Lemma pt_inst_pvar x : pt_inst pvar x = x.
Proof. destruct x as [p o]. unfold pt_inst. simpl. by rewrite pn_inst_pvar. Qed.

Lemma pn_inst_const σ p a : pn_root p = NConst a → pn_inst σ p = Pt p 0.
Proof.
  induction p as [a'|a'|p IH b i]; simpl; intros H; [done|done|].
  by rewrite (IH H).
Qed.

Lemma pt_inst_const σ x a : pt_root x = NConst a → pt_inst σ x = x.
Proof. destruct x as [p o]. intros H. unfold pt_inst. simpl. by rewrite (pn_inst_const σ p a H). Qed.

(** Lifting composes, and the identity lifts to itself. *)
Lemma pup_ext n σ τ a : (∀ b, σ b = τ b) → pup n σ a = pup n τ a.
Proof. intros H. unfold pup. by rewrite H. Qed.

Lemma pup_pvar n a : pup n pvar a = pvar a.
Proof.
  unfold pup. destruct (decide (a < n)); [done|].
  rewrite pt_inst_pvar_at. unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma pup_comp τ σ n a : pt_inst (pup n τ) (pup n σ a) = pup n (pt_inst τ ∘ σ) a.
Proof.
  unfold pup at 2 3. destruct (decide (a < n)).
  - rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True.
  - change ((pt_inst τ ∘ σ) (a - n)) with (pt_inst τ (σ (a - n))).
    rewrite !pt_inst_comp. apply pt_inst_ext. intros b. simpl.
    rewrite pt_inst_pvar_at. unfold pup. rewrite decide_False by lia.
    by replace (b + n - n) with b by lia.
Qed.

Lemma bcs_comp τ σ C : bcs_inst τ (bcs_inst σ C) = bcs_inst (pt_inst τ ∘ σ) C.
Proof.
  destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
  rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ x _. apply pt_inst_comp.
Qed.

Lemma bcs_pvar C : bcs_inst pvar C = C.
Proof.
  destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
  rewrite <-(list_fmap_id env) at 2. apply list_fmap_ext. intros _ x _. apply pt_inst_pvar.
Qed.

Lemma pinst_ty_ext T : ∀ σ τ, (∀ a, σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x];
    intros σ τ H; simpl.
  - done.
  - f_equal; [destruct ub; simpl; f_equal; auto using pt_inst_ext|destruct lb; simpl; f_equal; auto using pt_inst_ext|auto|auto].
  - f_equal; auto.
  - f_equal; auto.
  - f_equal.
    + by apply bcs_inst_ext.
    + apply IH. intros a. by apply pup_ext.
  - f_equal. by apply pt_inst_ext.
Qed.

Lemma pinst_ty_comp T : ∀ τ σ, pinst_ty τ (pinst_ty σ T) = pinst_ty (pt_inst τ ∘ σ) T.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x];
    intros τ σ; simpl.
  - done.
  - f_equal; [destruct ub; simpl; f_equal; auto using pt_inst_comp|destruct lb; simpl; f_equal; auto using pt_inst_comp|auto|auto].
  - f_equal; auto.
  - f_equal; auto.
  - f_equal.
    + apply bcs_comp.
    + rewrite IH. apply pinst_ty_ext. intros a. apply pup_comp.
  - f_equal. apply pt_inst_comp.
Qed.

Lemma pinst_ty_pvar T : pinst_ty pvar T = T.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x];
    simpl.
  - done.
  - f_equal; [destruct ub; simpl; f_equal; auto using pt_inst_pvar|destruct lb; simpl; f_equal; auto using pt_inst_pvar|auto|auto].
  - f_equal; auto.
  - f_equal; auto.
  - f_equal.
    + apply bcs_pvar.
    + rewrite (pinst_ty_ext _ _ pvar); [done|apply pup_pvar].
  - f_equal. apply pt_inst_pvar.
Qed.

(** Instantiating a list after lifting past it. *)
Lemma plist_shift xs m b : length xs = m → plist xs (b + m) = pvar b.
Proof.
  intros Hxs. unfold plist. rewrite lookup_ge_None_2 by lia.
  unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma plist_pup_shift xs m σ a :
  length xs = m → pt_inst (pt_inst (plist xs) ∘ pup m σ) (pshift m a) = σ a.
Proof.
  intros Hxs. unfold pshift. rewrite pt_inst_pvar_at. simpl.
  unfold pup. rewrite decide_False by lia. replace (a + m - m) with a by lia.
  rewrite pt_inst_comp. transitivity (pt_inst pvar (σ a)); [|apply pt_inst_pvar].
  apply pt_inst_ext. intros b. simpl. rewrite pt_inst_pvar_at. by apply plist_shift.
Qed.

Lemma plist_pup_comm xs n σ a :
  length xs = n →
  pt_inst (plist (pt_inst σ <$> xs)) (pup n σ a) = pt_inst σ (plist xs a).
Proof.
  intros Hxs. unfold pup. destruct (decide (a < n)).
  - rewrite pt_inst_pvar_at. unfold plist.
    destruct (lookup_lt_is_Some_2 xs a) as [x Hx]; [lia|].
    by rewrite list_lookup_fmap, Hx.
  - assert (plist xs a = pvar (a - n)) as ->.
    { unfold plist. rewrite lookup_ge_None_2 by lia. by rewrite Hxs. }
    rewrite pt_inst_pvar_at, pt_inst_comp.
    transitivity (pt_inst pvar (σ (a - n))); [|apply pt_inst_pvar].
    apply pt_inst_ext. intros b. simpl. rewrite pt_inst_pvar_at.
    apply plist_shift. by rewrite length_fmap.
Qed.

(** ** Constraints under substitution (sharp edges 65)

    C[σ] at xs[σ] holds when C at xs does: the facts of the one are the
    facts of the other, substituted ([bcs_open_inst]). *)

Lemma plist_pup_inst xs σ z :
  pt_inst (plist (pt_inst σ <$> xs)) (pt_inst (pup (length xs) σ) z)
  = pt_inst σ (pt_inst (plist xs) z).
Proof.
  rewrite !pt_inst_comp. apply pt_inst_ext. intros a. unfold compose.
  by apply plist_pup_comm.
Qed.

Lemma bcs_hold_inst (eq eq' lt lt' : point → point → Prop) σ C xs :
  (∀ x y, eq x y → eq' (pt_inst σ x) (pt_inst σ y)) →
  (∀ x y, lt x y → lt' (pt_inst σ x) (pt_inst σ y)) →
  bcs_hold eq lt C xs → bcs_hold eq' lt' (bcs_inst σ C) (pt_inst σ <$> xs).
Proof.
  intros He Hl H g Hg. rewrite length_fmap in Hg.
  apply bcs_open_inst in Hg as (g0 & Hg0 & ->). specialize (H g0 Hg0).
  destruct g0; simpl in *; rewrite !plist_pup_inst; auto.
Qed.

(** A constraint without outer points: its open facts are its scoped
    facts. *)
Lemma bcs_open_nil n P g : bcs_open n (BCs [] P) g ↔ P g ∧ fact_scoped n g.
Proof.
  unfold bcs_open. simpl. rewrite Nat.add_0_r.
  assert (∀ f, fact_map (pt_inst (pup n (plist []))) f = f) as E.
  { intros f. transitivity (fact_map id f); [|by destruct f].
    apply fact_map_ext. intros x. unfold id. rewrite <-(pt_inst_pvar x) at 2.
    apply pt_inst_ext. intros a. unfold pup. destruct (decide (a < n)); [done|].
    unfold plist. simpl. rewrite pt_inst_pvar_at. unfold pvar. f_equal. f_equal. lia. }
  split.
  - intros (f & Hf & Hs & ->). by rewrite E.
  - intros [Hg Hs]. exists g. by rewrite E.
Qed.

Lemma bcs_hold_intro (eq lt : point → point → Prop) P xs :
  (∀ g, P g → fact_scoped (length xs) g → fact_holds eq lt (fact_map (pt_inst (plist xs)) g)) →
  bcs_hold eq lt (BCs [] P) xs.
Proof. intros H g Hg. apply bcs_open_nil in Hg as [? ?]. auto. Qed.

(** A recursive call. The force at ys gets C[ys/ιs] from the body's
    own hypothesis (C, xs) when every fact of the instance is a fact of
    the hypothesis, C[ys/ιs] ⊆ C[xs/ιs] (sharp edges 65). No rule of
    its own is needed. *)
Lemma bcs_hold_sub W Ψ C xs ys :
  (C, xs) ∈ Ψ →
  (∀ g, bcs_open (length ys) C g → ∃ g', bcs_open (length xs) C g' ∧
     fact_map (pt_inst (plist ys)) g = fact_map (pt_inst (plist xs)) g') →
  bcs_hold (seqs W Ψ) (slt W Ψ) C ys.
Proof.
  intros Hg H g Hg0. destruct (H g Hg0) as (g' & Hg' & ->).
  exact (hyp_in_fact W Ψ C xs Hg g' Hg').
Qed.

Lemma pn_vb_root k p a : pn_vb k p → pn_root p = NVar a → a < k.
Proof. induction p as [b|b|q IH b i]; simpl; [done|congruence|exact IH]. Qed.

Lemma pt_inst_ids k x : pn_vb k (pt_name x) → pt_inst (plist (ids k)) x = x.
Proof.
  intros Hx. rewrite <-(pt_inst_pvar x) at 2. apply pt_inst_ext_root. intros a Ha.
  pose proof (pn_vb_root _ _ _ Hx Ha) as Hlt. unfold plist, ids.
  by rewrite list_lookup_fmap, lookup_seq_lt by done.
Qed.

Lemma pn_vb_inst k ys p :
  Forall (λ y, pn_vb k (pt_name y)) ys → pn_vb (length ys) p →
  pn_vb k (pt_name (pn_inst (plist ys) p)).
Proof.
  intros Hys. induction p as [b|b|q IH b i]; simpl; [done| |exact IH].
  intros Hb. unfold plist. destruct (lookup_lt_is_Some_2 ys b) as [y Hy]; [done|].
  rewrite Hy. rewrite Forall_lookup in Hys. exact (Hys b y Hy).
Qed.

Lemma fact_scoped_inst k ys g :
  Forall (λ y, pn_vb k (pt_name y)) ys → fact_scoped (length ys) g →
  fact_scoped k (fact_map (pt_inst (plist ys)) g).
Proof.
  intros Hys. destruct g as [x y|x y]; simpl; intros [Hx Hy];
    unfold pt_inst; simpl; split; by apply pn_vb_inst.
Qed.

(** The recursive call for a constraint without outer points, whose
    body hypothesis is C at its own ιs: C[ys/ιs] ⊆ C. *)
Lemma bcs_hold_self W Ψ P ys :
  (BCs [] P, ids (length ys)) ∈ Ψ → Forall (λ y, pn_vb (length ys) (pt_name y)) ys →
  (∀ g, P g → fact_scoped (length ys) g → P (fact_map (pt_inst (plist ys)) g)) →
  bcs_hold (seqs W Ψ) (slt W Ψ) (BCs [] P) ys.
Proof.
  intros Hg Hys H. apply (bcs_hold_sub W Ψ _ (ids (length ys))); [done|].
  intros g Hg0. apply bcs_open_nil in Hg0 as [HP Hs].
  exists (fact_map (pt_inst (plist ys)) g).
  pose proof (fact_scoped_inst _ _ _ Hys Hs) as Hs'. split.
  - unfold ids. rewrite length_fmap, length_seq. apply bcs_open_nil. split; [by apply H|done].
  - destruct (fact_map (pt_inst (plist ys)) g) as [x y|x y]; simpl in *;
      destruct Hs' as [Hx Hy]; by rewrite !pt_inst_ids.
Qed.

Lemma hyps_comp τ σ Ψ : hyps_inst τ (hyps_inst σ Ψ) = hyps_inst (pt_inst τ ∘ σ) Ψ.
Proof.
  unfold hyps_inst. rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ [C xs] _. simpl.
  rewrite bcs_comp. f_equal.
  rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ x _. apply pt_inst_comp.
Qed.

Lemma hyps_inst_ext σ τ Ψ : (∀ a, σ a = τ a) → hyps_inst σ Ψ = hyps_inst τ Ψ.
Proof.
  intros H. unfold hyps_inst. apply list_fmap_ext. intros _ [C xs] _. simpl. f_equal.
  - by apply bcs_inst_ext.
  - apply list_fmap_ext. intros _ x _. by apply pt_inst_ext.
Qed.

Lemma length_ids m : length (ids m) = m.
Proof. unfold ids. by rewrite length_fmap, length_seq. Qed.

Lemma ids_pup m σ : pt_inst (pup m σ) <$> ids m = ids m.
Proof.
  unfold ids. rewrite <-list_fmap_compose. apply list_fmap_ext. intros i x Hx. simpl.
  rewrite pt_inst_pvar_at. unfold pup. apply lookup_seq in Hx as [-> ?].
  by rewrite decide_True by lia.
Qed.

Lemma ids_plist xs τ : pt_inst (pt_inst (plist xs) ∘ pup (length xs) τ) <$> ids (length xs) = xs.
Proof.
  unfold ids. rewrite <-list_fmap_compose. apply list_eq. intros i. rewrite list_lookup_fmap.
  destruct (decide (i < length xs)).
  - rewrite lookup_seq_lt by done. simpl. rewrite pt_inst_pvar_at.
    change (Some (pt_inst (plist xs) (pup (length xs) τ i)) = xs !! i). unfold pup.
    rewrite decide_True by done. rewrite pt_inst_pvar_at. unfold plist.
    destruct (lookup_lt_is_Some_2 xs i) as [x Hx]; [done|]. by rewrite Hx.
  - rewrite lookup_seq_ge by lia. simpl. by rewrite lookup_ge_None_2 by lia.
Qed.

Lemma pn_root_inst σ p :
  pt_root (pn_inst σ p) = match pn_root p with NVar a => pt_root (σ a) | q => q end.
Proof. induction p as [a|a|p IH b i]; simpl; [done|done|]. exact IH. Qed.

Lemma pt_root_inst σ x :
  pt_root (pt_inst σ x) = match pt_root x with NVar a => pt_root (σ a) | q => q end.
Proof. destruct x as [p o]. exact (pn_root_inst σ p). Qed.

(** A hypothesis fact, substituted, is a fact of the substituted hypothesis. *)
Lemma hyp_fact_inst (eq lt : point → point → Prop) (pk : point → Prop) σ Ψ g :
  hyps_hold eq lt pk (hyps_inst σ Ψ) → hyp_fact Ψ g → fact_holds eq lt (fact_map (pt_inst σ) g).
Proof.
  intros H (C & xs & Hg & g0 & Hg0 & ->).
  assert ((bcs_inst σ C, pt_inst σ <$> xs) ∈ hyps_inst σ Ψ) as Hg'.
  { unfold hyps_inst. apply list_elem_of_fmap. by exists (C, xs). }
  destruct (H _ _ Hg') as [HC _].
  assert (bcs_open (length (pt_inst σ <$> xs)) (bcs_inst σ C)
            (fact_map (pt_inst (pup (length xs) σ)) g0)) as Ho.
  { rewrite length_fmap. apply bcs_open_inst. by exists g0. }
  specialize (HC _ Ho). destruct g0; simpl in *; by rewrite <-!plist_pup_inst.
Qed.

Lemma hyps_hold_inst (eq eq' lt lt' : point → point → Prop) (pk pk' : point → Prop) σ Ψ :
  (∀ x y, eq x y → eq' (pt_inst σ x) (pt_inst σ y)) →
  (∀ x y, lt x y → lt' (pt_inst σ x) (pt_inst σ y)) → (∀ x, pk x → pk' (pt_inst σ x)) →
  hyps_hold eq lt pk Ψ → hyps_hold eq' lt' pk' (hyps_inst σ Ψ).
Proof.
  intros He Hl Hk H C xs Hg. unfold hyps_inst in Hg.
  apply list_elem_of_fmap in Hg as ([C0 xs0] & Eg & Hg). injection Eg as -> ->.
  destruct (H C0 xs0 Hg) as [H1 H2]. split; [by eapply bcs_hold_inst|].
  apply Forall_fmap. eapply Forall_impl; [exact H2|]. intros x Hx. by apply Hk.
Qed.

Lemma skn_pinst W (pk : point → Prop) σ Ψ x :
  world_wf W → (∀ x y, pt_root x = pt_root y → pk x → pk y) → (∀ x, pt_known W x → pk x) →
  (∀ C xs, (C, xs) ∈ hyps_inst σ Ψ → Forall pk xs) → skn W Ψ x → pk (pt_inst σ x).
Proof.
  intros HW Hr Hk H [Hx|(C & xs & y & Hg & Hy & E)].
  - destruct (wf_names_const _ HW _ Hx) as [a Ha]. rewrite (pt_inst_const σ x a Ha). by apply Hk.
  - assert ((bcs_inst σ C, pt_inst σ <$> xs) ∈ hyps_inst σ Ψ) as Hg'
      by (unfold hyps_inst; apply list_elem_of_fmap; by exists (C, xs)).
    pose proof (H _ _ Hg') as Hf. rewrite Forall_forall in Hf.
    apply (Hr (pt_inst σ y)); [by rewrite !pt_root_inst, E|].
    apply Hf. by apply list_elem_of_fmap_2.
Qed.

(** ** Point scoping: every point variable lies below k *)

Definition pt_scoped (k : nat) (x : point) : Prop := ∀ a, pt_root x = NVar a → a < k.

Definition opt_scoped (k : nat) (o : option point) : Prop :=
  match o with Some x => pt_scoped k x | None => True end.

(** The outer points of a constraint live outside its binder. *)
Definition bcs_scoped (k : nat) (C : bcs) : Prop := Forall (pt_scoped k) (bc_env C).

Fixpoint pscoped (k : nat) (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli ub lb T1 U => opt_scoped k ub ∧ opt_scoped k lb ∧ pscoped k T1 ∧ pscoped k U
  | TProd T1 U | TSum T1 U => pscoped k T1 ∧ pscoped k U
  | TBox n C T1 => bcs_scoped k C ∧ pscoped (n + k) T1
  | TSess _ x => pt_scoped k x
  end.

Lemma pinst_ty_ext_scoped T : ∀ k σ τ,
  pscoped k T → (∀ a, a < k → σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof.
  assert (∀ k σ τ x, pt_scoped k x → (∀ a, a < k → σ a = τ a) →
            pt_inst σ x = pt_inst τ x) as Hpt.
  { intros k σ τ x Hx H. apply pt_inst_ext_root. intros a Ha. by apply H, Hx. }
  assert (∀ k n σ τ, (∀ a, a < k → σ a = τ a) → ∀ a, a < n + k → pup n σ a = pup n τ a) as Hup.
  { intros k n σ τ H a Ha. unfold pup. destruct (decide (a < n)); [done|].
    rewrite H; [done|lia]. }
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x];
    intros k σ τ HT H; simpl in *.
  - done.
  - destruct HT as (Hub & Hlb & H1 & H2).
    f_equal; [destruct ub; simpl in *; [f_equal; eauto|done]
             |destruct lb; simpl in *; [f_equal; eauto|done]|eauto|eauto].
  - destruct HT. f_equal; eauto.
  - destruct HT. f_equal; eauto.
  - destruct HT as (HC & H1). f_equal.
    + unfold bcs_inst. f_equal. apply list_fmap_ext. intros i x Hx.
      unfold bcs_scoped in HC. rewrite Forall_forall in HC. eapply Hpt; [|exact H].
      apply HC. by eapply list_elem_of_lookup_2.
    + eapply IH; [done|]. by apply Hup.
  - f_equal. eauto.
Qed.

Lemma payload_pinst σ m T x :
  pscoped m T → pinst_ty σ (payload_at m T x) = payload_at m T (pt_inst σ x).
Proof.
  intros HT. unfold payload_at, ty_inst. rewrite pinst_ty_comp.
  apply (pinst_ty_ext_scoped T m); [done|]. intros a Ha. simpl. unfold plist, slots.
  rewrite !list_lookup_fmap, !lookup_seq_lt by done. simpl. apply pt_inst_slot.
Qed.

(** E-Const asks the payload of send and recv to be scoped by its m
    binders (§4: "P ::= ∃ιs. T, all points of T bound"). *)
Definition kscoped (k : konst) (T : ty) : Prop :=
  match k, T with
  | KSend, TLolli _ _ (TProd _ (TSess (SSnd m P _) _)) _ => pscoped m P
  | KRecv, TLolli _ _ (TSess (SRcv m P _) _) _ => pscoped m P
  | _, _ => True
  end.

Lemma opt_heads_pinst σ o : opt_heads (pt_inst σ <$> o) = set_map (pt_inst σ) (opt_heads o).
Proof. destruct o; simpl; [by rewrite set_map_singleton_L|by rewrite set_map_empty]. Qed.

Lemma heads_pinst σ T : heads (pinst_ty σ T) = set_map (pt_inst σ) (heads T).
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x];
    simpl.
  - by rewrite set_map_empty.
  - apply opt_heads_pinst.
  - by rewrite IH1, IH2, set_map_union_L.
  - by rewrite IH1, IH2, set_map_union_L.
  - by rewrite set_map_empty.
  - by rewrite set_map_singleton_L.
Qed.

(** ** Facts survive substitution

    A world knows constants only (wf_names_const). A fact about a point
    with a variable root is reflexivity or program order, and both hold
    of any instance. *)

Definition node_inst (σ : nat → point) (a : node) : node :=
  match a with NP x => NP (pt_inst σ x) | NV φ => NV φ end.

Definition ends_pinst (σ : nat → point) (o : ends) : ends :=
  match o with
  | One e => One (e.1, pt_inst σ e.2)
  | Both e1 e2 => Both (e1.1, pt_inst σ e1.2) (e2.1, pt_inst σ e2.2)
  end.

Definition tenv_pinst (σ : nat → point) (Θ : tenv) : tenv := ends_pinst σ <$> Θ.

Lemma tenv_comp_pinst (R R' : point → point → Prop) σ Θ Θ1 Θ2 :
  (∀ x y, R x y → R' (pt_inst σ x) (pt_inst σ y)) → tenv_comp R Θ Θ1 Θ2 →
  tenv_comp R' (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2).
Proof.
  intros HR [Hj Hd]. split.
  - intros c. unfold tenv_pinst. rewrite !lookup_fmap. pose proof (Hj c) as Hc.
    destruct (Θ1 !! c), (Θ2 !! c), (Θ !! c); inversion Hc; subst; simpl; constructor.
  - intros c e1 e2 H1 H2. unfold tenv_pinst in H1, H2. rewrite lookup_fmap in H1, H2.
    destruct (Θ1 !! c) as [[e1'|]|] eqn:E1; simplify_eq/=.
    destruct (Θ2 !! c) as [[e2'|]|] eqn:E2; simplify_eq/=.
    destruct (Hd c e1' e2' E1 E2) as [He Hs]. split; [|done]. by apply HR.
Qed.

Section transfer.
  Context (W W1 : world) (σ : nat → point).
  Context (HW : world_wf W) (HW1 : wext W W1).

  Lemma pinst_eq x y : w_eq W x y → w_eq W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros Hxy. pose proof (wext_wf _ _ HW1) as Hwf.
    destruct (wf_eq_supp _ HW x y Hxy) as [->|[Hx Hy]]; [apply (wf_eq_refl _ Hwf)|].
    destruct (wf_names_const _ HW _ Hx) as [a Ha]. destruct (wf_names_const _ HW _ Hy) as [b Hb].
    rewrite (pt_inst_const σ x a Ha), (pt_inst_const σ y b Hb).
    destruct HW1 as (_ & He & Hl & _). auto.
  Qed.

  Lemma pinst_lt x y : w_lt W x y → w_lt W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros Hxy. pose proof (wext_wf _ _ HW1) as Hwf.
    destruct (wf_lt_supp _ HW x y Hxy) as [[Hn Ho]|[Hx Hy]].
    - destruct x as [p o], y as [p' o']. simpl in *. subst p'.
      replace (pt_inst σ (Pt p o')) with (pt_shift (S (o' - o - 1)) (pt_inst σ (Pt p o))).
      + by apply wf_lt_po_n.
      + unfold pt_inst, pt_shift. simpl. f_equal. lia.
    - destruct (wf_names_const _ HW _ Hx) as [a Ha]. destruct (wf_names_const _ HW _ Hy) as [b Hb].
      rewrite (pt_inst_const σ x a Ha), (pt_inst_const σ y b Hb).
    destruct HW1 as (_ & He & Hl & _). auto.
  Qed.

  Lemma pinst_le x y : w_le W x y → w_le W1 (pt_inst σ x) (pt_inst σ y).
  Proof. intros [H|H]; [left; by apply pinst_eq|right; by apply pinst_lt]. Qed.

  Lemma pinst_known x : pt_known W x → pt_known W1 (pt_inst σ x).
  Proof.
    intros Hx. destruct (wf_names_const _ HW _ Hx) as [a Ha].
    rewrite (pt_inst_const σ x a Ha). destruct HW1 as [HN _]. unfold pt_known in *. set_solver.
  Qed.

  Lemma ub_below_pinst ub F :
    ub_below W ub F → ub_below W1 (pt_inst σ <$> ub) (set_map (pt_inst σ) F).
  Proof.
    destruct ub as [x|]; simpl; [|done]. intros H y Hy.
    apply elem_of_map in Hy as (y0 & -> & Hy0). by apply pinst_lt, H.
  Qed.

  Lemma lb_below_pinst lb H :
    lb_below W lb H → lb_below W1 (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    destruct lb as [x|]; simpl.
    - intros Hl y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply pinst_le, Hl.
    - intros ->. apply set_map_empty.
  Qed.

  Lemma konst_ty_pinst (peq peq' plt plt' : point → point → Prop) (pk pk' : point → Prop) k T :
    (∀ x y, peq x y → peq' (pt_inst σ x) (pt_inst σ y)) →
    (∀ x y, plt x y → plt' (pt_inst σ x) (pt_inst σ y)) →
    (∀ x, pk x → pk' (pt_inst σ x)) →
    kscoped k T → konst_ty peq plt pk k T →
    konst_ty peq' plt' pk' k (pinst_ty σ T).
  Proof.
    intros Heq Hlt Hpk Hk.
    destruct 1 as [S x Hx|ub lb|m P S x Hh|m P S x|x|S x x' Hxx'|n C ub P xs Hxs HC HK];
      simpl in *.
    - constructor. by apply Hpk.
    - constructor.
    - rewrite payload_pinst, pt_inst_shift by done. constructor.
      intros h Hh'. rewrite <-payload_pinst, heads_pinst in Hh' by done.
      apply elem_of_map in Hh' as (h0 & -> & Hh0). by apply Hlt, Hh.
    - rewrite payload_pinst, pt_inst_shift by done. constructor.
    - constructor.
    - constructor. by apply Heq.
    - assert (∀ a, pt_inst (plist (pt_inst σ <$> xs)) (pup n σ a) = pt_inst σ (plist xs a))
        as Hc by (intros a; by apply plist_pup_comm).
      assert (pt_inst (plist (pt_inst σ <$> xs)) <$> (pt_inst (pup n σ) <$> ub) =
              pt_inst σ <$> (pt_inst (plist xs) <$> ub)) as E1.
      { destruct ub; simpl; [|done]. f_equal. rewrite !pt_inst_comp.
        apply pt_inst_ext. intros a. apply Hc. }
      assert (ty_inst (pt_inst σ <$> xs) (pinst_ty (pup n σ) P) = pinst_ty σ (ty_inst xs P)) as E2.
      { unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. apply Hc. }
      rewrite <-E1, <-E2. constructor; [by rewrite length_fmap| |].
      + by apply (bcs_hold_inst peq _ plt).
      + apply Forall_fmap. eapply Forall_impl; [exact HK|]. intros x Hx. by apply Hpk.
  Qed.

  Lemma skn_pinst_known Ψ x :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → skn W Ψ x → pt_known W1 (pt_inst σ x).
  Proof.
    intros HΨ. apply (skn_pinst W (pt_known W1) σ Ψ x HW).
    - intros y z E. unfold pt_known. by rewrite E.
    - intros y Hy. destruct HW1 as [HN _]. unfold pt_known in *. clear -HN Hy. set_solver.
    - intros C xs Hg. by destruct (HΨ C xs Hg).
  Qed.

  Lemma skn_pinst_s Ψ Ψ' x :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → skn W Ψ x → skn W1 Ψ' (pt_inst σ x).
  Proof.
    intros HΨ. apply (skn_pinst W (skn W1 Ψ') σ Ψ x HW).
    - intros y z E. by apply skn_root.
    - intros y Hy. left. destruct HW1 as [HN _]. unfold pt_known in *. clear -HN Hy. set_solver.
    - intros C xs Hg. by destruct (HΨ C xs Hg).
  Qed.

  (** Facts derived from W and the hypotheses Ψ survive into W₁ when
      the hypotheses hold there (sharp edges 58). One lemma maps a
      derivation of the fact theory along σ (sharp edges 64, 65). *)

  Lemma fl_pinst Ψ Ψ' Φ Φ' :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) →
    (∀ φ u, Φ !! φ = Some (Some u) → fl (FCtx W1 Ψ' Φ') (NP (pt_inst σ u)) (NV φ)) →
    (∀ x y, seqs W Ψ x y → seqs W1 Ψ' (pt_inst σ x) (pt_inst σ y)) ∧
    (∀ a b, fl (FCtx W Ψ Φ) a b → fl (FCtx W1 Ψ' Φ') (node_inst σ a) (node_inst σ b)).
  Proof.
    intros HΨ HΦ. apply (fl_map (FCtx W Ψ Φ) (seqs W1 Ψ') _ (pt_inst σ) (node_inst σ)); simpl.
    - intros x y H. apply se_w. by apply pinst_eq.
    - intros x y H. exact (hyp_fact_inst _ _ _ σ Ψ (FEq x y) HΨ H).
    - intros x. apply se_refl.
    - intros x y. apply se_sym.
    - intros x y z. apply se_trans.
    - intros x y H. rewrite !pt_inst_shift. by apply se_shift.
    - intros x y i H. rewrite !pt_inst_slot. by apply se_slot.
    - intros x y H. apply (fl_w (FCtx W1 Ψ' Φ')). by apply pinst_lt.
    - intros x y Hxy. apply fl_points. exact (hyp_fact_inst _ _ _ σ Ψ (FLt x y) HΨ Hxy).
    - exact HΦ.
    - intros x x' b Hx H. exact (fl_eql (FCtx W1 Ψ' Φ') _ _ _ Hx H).
    - intros a y y' H Hy. exact (fl_eqr (FCtx W1 Ψ' Φ') _ _ _ H Hy).
    - intros a y b. exact (fl_trans (FCtx W1 Ψ' Φ') _ _ _).
  Qed.

  Lemma seqs_pinst_s Ψ Ψ' x y :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) →
    seqs W Ψ x y → seqs W1 Ψ' (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ. exact (proj1 (fl_pinst Ψ Ψ' ∅ ∅ HΨ (λ φ u Hu, ltac:(by rewrite lookup_empty in Hu))) x y).
  Qed.

  Lemma slt_pinst_s Ψ Ψ' x y :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → slt W Ψ x y → slt W1 Ψ' (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ H. exact (proj2 (fl_pinst Ψ Ψ' ∅ ∅ HΨ (λ φ u Hu, ltac:(by rewrite lookup_empty in Hu))) _ _ H).
  Qed.

  (** The ground case: the target is the world W₁ itself. *)
  Lemma hyps_hold_ground Ψ :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) →
    hyps_hold (seqs W1 []) (slt W1 []) (skn W1 []) (hyps_inst σ Ψ).
  Proof.
    apply hyps_hold_mono; [intros ? ? ?; by apply se_w|intros ? ? ?; by apply sl_w|intros ? ?; by left].
  Qed.

  Lemma seqs_pinst Ψ x y :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → seqs W Ψ x y → w_eq W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ H. apply (seqs_nil _ _ _ (wext_wf _ _ HW1)). apply (seqs_pinst_s Ψ); [|done].
    by apply hyps_hold_ground.
  Qed.

  Lemma slt_pinst Ψ x y :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → slt W Ψ x y → w_lt W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ H. apply (slt_nil _ _ _ (wext_wf _ _ HW1)). apply (slt_pinst_s Ψ); [|done].
    by apply hyps_hold_ground.
  Qed.

  Lemma sle_pinst Ψ x y :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → sle W Ψ x y → w_le W1 (pt_inst σ x) (pt_inst σ y).
  Proof. intros HΨ [H|H]; [left; by apply (seqs_pinst Ψ)|right; by apply (slt_pinst Ψ)]. Qed.

  Lemma sle_pinst_s Ψ Ψ' x y :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → sle W Ψ x y → sle W1 Ψ' (pt_inst σ x) (pt_inst σ y).
  Proof. intros HΨ [H|H]; [left; by apply (seqs_pinst_s Ψ)|right; by apply (slt_pinst_s Ψ)]. Qed.

  Lemma lb_below_h_pinst Ψ lb H :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) →
    lb_below_h W Ψ lb H → lb_below W1 (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    intros HΨ. destruct lb as [x|]; simpl.
    - intros Hl y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply (sle_pinst Ψ), Hl.
    - intros ->. apply set_map_empty.
  Qed.

  Lemma lb_below_h_pinst_s Ψ Ψ' lb H :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) →
    lb_below_h W Ψ lb H → lb_below_h W1 Ψ' (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    intros HΨ. destruct lb as [x|]; simpl.
    - intros Hl y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply (sle_pinst_s Ψ), Hl.
    - intros ->. apply set_map_empty.
  Qed.

  (** Composition of environments reads Γ ⊢ ≡ (sharp edges 65). *)
  Lemma tenv_comp_pinst_g Ψ Θ Θ1 Θ2 :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → tenv_comp (seqs W Ψ) Θ Θ1 Θ2 →
    tenv_comp (w_eq W1) (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2).
  Proof. intros HΨ. apply tenv_comp_pinst. intros x y. by apply (seqs_pinst Ψ). Qed.

  Lemma tenv_comp_pinst_s Ψ Ψ' Θ Θ1 Θ2 :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → tenv_comp (seqs W Ψ) Θ Θ1 Θ2 →
    tenv_comp (seqs W1 Ψ') (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2).
  Proof. intros HΨ. apply tenv_comp_pinst. intros x y. by apply (seqs_pinst_s Ψ). Qed.
End transfer.

(** ** Substitution in environments, hypotheses and frames *)

Definition lenv_pinst (σ : nat → point) (Δ : lenv) : lenv := fmap (M:=option) (pinst_ty σ) <$> Δ.

Definition fhyps_pinst (σ : nat → point) (Φ : fhyps) : fhyps := fmap (M:=option) (pt_inst σ) <$> Φ.

Definition sf_pinst (σ : nat → point) (F : sframe) : sframe := (set_map (pt_inst σ) F.1, F.2).

Lemma unlimited_pinst σ U : unlimited U → unlimited (pinst_ty σ U).
Proof. by destruct U. Qed.

Lemma lenv_heads_pinst σ Δ : lenv_heads (lenv_pinst σ Δ) = set_map (pt_inst σ) (lenv_heads Δ).
Proof.
  induction Δ as [|[T|] Δ IH]; simpl.
  - by rewrite set_map_empty.
  - by rewrite IH, heads_pinst, set_map_union_L.
  - done.
Qed.

Lemma lenv_empty_pinst σ Δ : lenv_empty Δ → lenv_empty (lenv_pinst σ Δ).
Proof.
  intros HΔ o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho'). by rewrite (HΔ o' Ho').
Qed.

Lemma lenv_unl_pinst σ Δ : lenv_unl Δ → lenv_unl (lenv_pinst σ Δ).
Proof.
  intros HΔ o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (HΔ o' Ho') as [->|(U & -> & HU)]; [by left|right].
  exists (pinst_ty σ U). split; [done|by apply unlimited_pinst].
Qed.

Lemma lenv_pinst_lookup σ Δ x : lenv_pinst σ Δ !! x = fmap (pinst_ty σ) <$> Δ !! x.
Proof. unfold lenv_pinst. apply list_lookup_fmap. Qed.

Lemma lenv_only_pinst σ Δ x T : lenv_only Δ x T → lenv_only (lenv_pinst σ Δ) x (pinst_ty σ T).
Proof.
  intros [Hx Hu]. split.
  - by rewrite lenv_pinst_lookup, Hx.
  - intros y T' Hy. rewrite lenv_pinst_lookup in Hy.
    destruct (Δ !! y) as [[T0|]|] eqn:E; simplify_eq/=.
    destruct (Hu y T0 E) as [-> ->]. done.
Qed.

Lemma lenv_split_pinst σ Δ Δ1 Δ2 :
  lenv_split Δ Δ1 Δ2 → lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2).
Proof. induction 1; simpl; constructor; auto using unlimited_pinst. Qed.

Lemma lenv_wk_pinst σ Δ' Δ : lenv_wk Δ' Δ → lenv_wk (lenv_pinst σ Δ') (lenv_pinst σ Δ).
Proof. induction 1; simpl; constructor; auto using unlimited_pinst. Qed.

Lemma lenv_pinst_ext σ τ Δ : (∀ a, σ a = τ a) → lenv_pinst σ Δ = lenv_pinst τ Δ.
Proof.
  intros H. unfold lenv_pinst. apply list_fmap_ext. intros i [T|] _; simpl; [|done].
  f_equal. by apply pinst_ty_ext.
Qed.

Lemma lenv_pinst_comp τ σ Δ : lenv_pinst τ (lenv_pinst σ Δ) = lenv_pinst (pt_inst τ ∘ σ) Δ.
Proof.
  unfold lenv_pinst. rewrite <-list_fmap_compose. apply list_fmap_ext.
  intros i [T|] _; simpl; [|done]. f_equal. apply pinst_ty_comp.
Qed.

Lemma lenv_pinst_pvar Δ : lenv_pinst pvar Δ = Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [done| |]; rewrite IH; [|done].
  by rewrite pinst_ty_pvar.
Qed.

Lemma ends_heads_pinst σ c o :
  ends_heads c (ends_pinst σ o) = set_map (pt_inst σ) (ends_heads c o).
Proof. destruct o; simpl; set_solver. Qed.

Lemma tenv_heads_pinst σ Θ : tenv_heads (tenv_pinst σ Θ) = set_map (pt_inst σ) (tenv_heads Θ).
Proof.
  apply set_eq. intros x. rewrite elem_of_map, elem_of_tenv_heads. split.
  - intros (c & o & Hc & Hx). unfold tenv_pinst in Hc. rewrite lookup_fmap in Hc.
    destruct (Θ !! c) as [o0|] eqn:Ho; [|done]. injection Hc as <-.
    rewrite ends_heads_pinst in Hx.
    apply elem_of_map in Hx as (x0 & -> & Hx0). exists x0. split; [done|].
    apply elem_of_tenv_heads. eauto.
  - intros (x0 & -> & Hx0). apply elem_of_tenv_heads in Hx0 as (c & o & Hc & Hx).
    exists c, (ends_pinst σ o). split.
    + unfold tenv_pinst. by rewrite lookup_fmap, Hc.
    + rewrite ends_heads_pinst. by apply elem_of_map_2.
Qed.

Lemma tenv_pinst_pvar Θ : tenv_pinst pvar Θ = Θ.
Proof.
  apply map_eq. intros c. unfold tenv_pinst. rewrite lookup_fmap.
  destruct (Θ !! c) as [[[s x]|[s1 x1] [s2 x2]]|]; simpl; rewrite ?pt_inst_pvar; done.
Qed.

Lemma sf_pinst_union σ F X : sf_pinst σ (sf_union F X) = sf_union (sf_pinst σ F) (set_map (pt_inst σ) X).
Proof. unfold sf_pinst, sf_union. simpl. by rewrite set_map_union_L. Qed.

Lemma sf_pinst_pvar F : sf_pinst pvar F = F.
Proof.
  destruct F as [P o]. unfold sf_pinst. simpl. f_equal.
  apply set_eq. intros x. rewrite elem_of_map. split.
  - intros (y & -> & Hy). by rewrite pt_inst_pvar.
  - intros Hx. exists x. by rewrite pt_inst_pvar.
Qed.

Lemma ub_below_s_pinst W W1 σ Ψ Ψ' Φ ub F :
  world_wf W → wext W W1 → hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → ub_below_s W Ψ Φ ub F →
  ub_below_s W1 Ψ' (fhyps_pinst σ Φ) (pt_inst σ <$> ub) (sf_pinst σ F).
Proof.
  intros HW HW1 HΨ. destruct ub as [x|]; [|done]. intros [HP Hφ].
  assert (∀ a b, fl (FCtx W Ψ Φ) a b →
            fl (FCtx W1 Ψ' (fhyps_pinst σ Φ)) (node_inst σ a) (node_inst σ b)) as Hm.
  { refine (proj2 (fl_pinst W W1 σ HW HW1 Ψ Ψ' Φ _ HΨ _)). intros φ u Hu.
    apply (fl_v (FCtx W1 Ψ' (fhyps_pinst σ Φ))). simpl.
    unfold fhyps_pinst. by rewrite lookup_fmap, Hu. }
  split.
  - intros y Hy. destruct F as [P o]. simpl in *.
    apply elem_of_map in Hy as (y0 & -> & Hy0). exact (Hm _ _ (HP y0 Hy0)).
  - intros φ Hφ'. destruct F as [P o]. simpl in *. exact (Hm _ _ (Hφ φ Hφ')).
Qed.

Lemma eqT_pinst ρ T : ∀ U σ, eqT ρ T U → eqT ρ (pinst_ty σ T) (pinst_ty σ U).
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x];
    intros [| ub' lb' U1 U2 | U1 U2 | U1 U2 | n' C' U1 | r y] σ; simpl; try done.
  - intros (-> & -> & H1 & H2). split_and!; auto.
  - intros [H1 H2]. split_and!; auto.
  - intros [H1 H2]. split_and!; auto.
  - intros (-> & -> & H1). split_and!; auto.
  - intros (-> & H). split_and!; auto.
Qed.

Lemma tenv_pinst_empty σ : tenv_pinst σ ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma sf_pinst_fresh σ φ : sf_pinst σ (∅, Some φ) = (∅, Some φ).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

Inductive typed (W : world) : fhyps → hyps → tenv → lenv → sframe → expr → ty → Prop :=
  | t_unit Φ Ψ Δ F :                                    (* E-Unit *)
      lenv_empty Δ →
      typed W Φ Ψ ∅ Δ F EUnit TUnit
  | t_konst Φ Ψ Δ F k T :                               (* E-Const *)
      lenv_empty Δ → konst_ty (seqs W Ψ) (slt W Ψ) (skn W Ψ) k T → kscoped k T →
      typed W Φ Ψ ∅ Δ F (Konst k) T
  | t_var Φ Ψ Δ F x T :                                 (* E-LVar *)
      lenv_only Δ x T →
      typed W Φ Ψ ∅ Δ F (Var x) T
  | t_chan Φ Ψ Δ F c s k s' y :                         (* E-Ch, ι′ ≡_Γ ι *)
      lenv_empty Δ → seq s s' → seqs W Ψ k y →
      typed W Φ Ψ {[c := One (s, k)]} Δ F (Chan c) (TSess s' y)
  | t_lam Φ Ψ Θ Δ F e T U ub lb φ :                     (* E-Abs *)
      φ ∉ dom Φ →
      lb_below_h W Ψ lb (tenv_heads Θ ∪ lenv_heads Δ) →
      typed W (<[φ := ub]> Φ) Ψ Θ (Some T :: Δ) (∅, Some φ) e U →
      typed W Φ Ψ Θ Δ F (Lam e) (TLolli ub lb T U)
  | t_app Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :       (* E-App *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below_s W Ψ Φ ub F →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TLolli ub lb T U) →
      typed W Φ Ψ Θ2 Δ2 (sf_union F (opt_heads lb)) e2 T →
      typed W Φ Ψ Θ Δ F (App e1 e2) U
  | t_pair Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :            (* E-Pair *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 T →
      typed W Φ Ψ Θ2 Δ2 (sf_union F (heads T)) e2 U →
      typed W Φ Ψ Θ Δ F (Pair e1 e2) (TProd T U)
  | t_letu Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :              (* E-Let* *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 TUnit →
      typed W Φ Ψ Θ2 Δ2 F e2 T →
      typed W Φ Ψ Θ Δ F (LetU e1 e2) T
  | t_letp Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :        (* E-LetPair *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TProd T1 T2) →
      typed W Φ Ψ Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
      typed W Φ Ψ Θ Δ F (LetP e1 e2) T
  | t_inj1 Φ Ψ Θ Δ F e T U :                            (* E-Inj *)
      typed W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F (Inj1 e) (TSum T U)
  | t_inj2 Φ Ψ Θ Δ F e T U :
      typed W Φ Ψ Θ Δ F e U → typed W Φ Ψ Θ Δ F (Inj2 e) (TSum T U)
  | t_case Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :      (* E-Case *)
      tenv_comp (seqs W Ψ) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W Φ Ψ Θ1 Δ1 (sf_union F (tenv_heads Θ2 ∪ lenv_heads Δ2)) e (TSum T1 T2) →
      typed W Φ Ψ Θ2 (Some T1 :: Δ2) F e1 T →
      typed W Φ Ψ Θ2 (Some T2 :: Δ2) F e2 T →
      typed W Φ Ψ Θ Δ F (Case e e1 e2) T
  | t_box Φ Ψ Δ F e m C ub T φ :                        (* E-Exp *)
      lenv_unl Δ → φ ∉ dom Φ →
      typed W (<[φ := ub]> (fhyps_pinst (pshift m) Φ))
        (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)]) ∅
        (lenv_pinst (pshift m) (Some (TBox m C (TLolli ub None TUnit T)) :: Δ)) (∅, Some φ) e T →
      typed W Φ Ψ ∅ Δ F (EBox e) (TBox m C (TLolli ub None TUnit T))
  | t_wk Φ Ψ Θ Δ' Δ F e T :                             (* E-Weak *)
      lenv_wk Δ' Δ → typed W Φ Ψ Θ Δ' F e T → typed W Φ Ψ Θ Δ F e T
  | t_contract Φ Ψ Θ Δ U F e T :                        (* E-Contract *)
      unlimited U →
      typed W Φ Ψ Θ (Some U :: Some U :: Δ) F e T →
      typed W Φ Ψ Θ (Some U :: Δ) F (rename pred e) T
  | t_conv Φ Ψ Θ Δ F e T T' :                           (* E-Conv *)
      teq T T' → typed W Φ Ψ Θ Δ F e T → typed W Φ Ψ Θ Δ F e T'.

(** E-Force is E-App at the constant force. The instance must meet the
    box's constraint, every fact read from W and the hypotheses Ψ
    (sharp edges 58, 65). *)
Lemma typed_force W Φ Ψ Θ Δ F e m C ub T xs :
  world_wf W → length xs = m → bcs_hold (seqs W Ψ) (slt W Ψ) C xs → Forall (skn W Ψ) xs →
  ub_below_s W Ψ Φ (pt_inst (plist xs) <$> ub) F →
  typed W Φ Ψ Θ Δ F e (TBox m C (TLolli ub None TUnit T)) →
  typed W Φ Ψ Θ Δ F (App EForce e) (ty_inst xs T).
Proof.
  intros HW Hxs HC HK Hub He.
  eapply (t_app W Φ Ψ Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, se_sym.
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply t_konst; [apply lenv_empty_nones| |done]. by constructor.
  - destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L.
Qed.

(** ** Frame instantiation

    Replacing the frame variables by concrete frames that meet the
    hypotheses, at any later world, turns a derivation into one of the
    infinitary judgment. Monotonicity in W is folded in: typing reads W
    only through facts, and facts survive W ⊑ W₁. *)

Lemma sf_inst_union ρ F X : sf_inst ρ (sf_union F X) = sf_inst ρ F ∪ X.
Proof. destruct F as [P [φ|]]; unfold sf_inst, sf_union; simpl; set_solver. Qed.

(** Frame instantiation: a node stands for the points it denotes. *)
Definition node_den (ρ : nat → gset point) (a : node) (z : point) : Prop :=
  match a with NP x => z = x | NV φ => z ∈ ρ φ end.

Lemma ub_below_s_inst W W1 Φ ρ ub F :
  world_wf W → wext W W1 → inst_ok W1 Φ ρ → ub_below_s W [] Φ ub F →
  ub_below W1 ub (sf_inst ρ F).
Proof.
  intros HW HW1 Hρ. destruct ub as [x|]; [|done]. intros [HP Hφ]. simpl.
  pose proof (wext_wf _ _ HW1) as Hwf. pose proof HW1 as (_ & He & Hl & _).
  assert (∀ a b, fl (FCtx W [] Φ) a b →
            ∀ a' b', node_den ρ a a' → node_den ρ b b' → w_lt W1 a' b') as Hm.
  { refine (proj2 (fl_map _ (w_eq W1)
      (λ a b, ∀ a' b', node_den ρ a a' → node_den ρ b b' → w_lt W1 a' b') id id
      _ _ _ _ _ _ _ _ _ _ _ _ _)); unfold id; simpl.
    - intros x0 y0 H. by apply He.
    - intros ? ? (? & ? & H & _). by apply elem_of_nil in H.
    - apply (wf_eq_refl _ Hwf).
    - apply (wf_eq_sym _ Hwf).
    - apply (wf_eq_trans _ Hwf).
    - apply (wf_eq_shift _ Hwf).
    - apply (wf_eq_slot _ Hwf).
    - intros x0 y0 H ? ? -> ->. by apply Hl.
    - intros ? ? (? & ? & H & _). by apply elem_of_nil in H.
    - intros φ u Hu ? b' -> Hb'. exact (Hρ φ (Some u) Hu b' Hb').
    - intros x0 x' b Hx H ? b' -> Hb'.
      exact (wf_lt_eq _ Hwf x0 x' b' b' Hx (H x' b' eq_refl Hb') (wf_eq_refl _ Hwf b')).
    - intros a y y' H Hy a' ? Ha' ->.
      exact (wf_lt_eq _ Hwf a' a' y y' (wf_eq_refl _ Hwf a') (H a' y' Ha' eq_refl) Hy).
    - intros a y b H1 H2 a' b' Ha' Hb'.
      exact (wf_lt_trans _ Hwf a' y b' (H1 a' y Ha' eq_refl) (H2 y b' eq_refl Hb')). }
  intros y Hy. unfold sf_inst in Hy. apply elem_of_union in Hy as [Hy|Hy].
  - exact (Hm _ _ (HP y Hy) x y eq_refl eq_refl).
  - destruct F as [P [φ|]]; simpl in *; [|by apply elem_of_empty in Hy].
    exact (Hm _ _ (Hφ φ eq_refl) x y eq_refl Hy).
Qed.

Lemma inst_ok_mono W W1 Φ ρ : wext W W1 → inst_ok W Φ ρ → inst_ok W1 Φ ρ.
Proof. intros HW1 Hρ φ u Hu. exact (ub_below_mono W W1 u _ HW1 (Hρ φ u Hu)). Qed.

Lemma inst_ok_insert W Φ ρ φ ub F' :
  inst_ok W Φ ρ → ub_below W ub F' →
  inst_ok W (<[φ := ub]> Φ) (λ ψ, if decide (ψ = φ) then F' else ρ ψ).
Proof.
  intros Hρ Hub ψ u Hu. cbv beta. destruct (decide (ψ = φ)) as [->|Hne].
  - by simplify_map_eq.
  - simplify_map_eq. by apply Hρ.
Qed.

Lemma sf_inst_fresh ρ φ F' :
  sf_inst (λ ψ, if decide (ψ = φ) then F' else ρ ψ) (∅, Some φ) = F'.
Proof. unfold sf_inst. simpl. rewrite decide_True; [|done]. by rewrite union_empty_l_L. Qed.

Lemma inst_ok_pinst_insert W Φ σ φ ub ρ F' :
  inst_ok W (fhyps_pinst σ Φ) ρ → ub_below W (pt_inst σ <$> ub) F' →
  inst_ok W (fhyps_pinst σ (<[φ := ub]> Φ)) (λ ψ, if decide (ψ = φ) then F' else ρ ψ).
Proof. intros Hρ Hub. unfold fhyps_pinst. rewrite fmap_insert. by apply inst_ok_insert. Qed.

(** Typed terms are well formed, read off the finitary derivation: the
    box body is typed once, so no instance of C is needed. *)
Lemma unlimited_pinst_iff σ U : unlimited (pinst_ty σ U) ↔ unlimited U.
Proof. by destruct U. Qed.

Lemma term_wf_lenv_pinst σ Θ Δ e : term_wf Θ (lenv_pinst σ Δ) e ↔ term_wf Θ Δ e.
Proof.
  assert (∀ x, lenv_avail (lenv_pinst σ Δ) x ↔ lenv_avail Δ x) as Ha.
  { intros x. unfold lenv_avail. rewrite lenv_pinst_lookup.
    destruct (Δ !! x) as [[T|]|]; simpl; split; intros [U HU]; simplify_eq; eauto. }
  assert (∀ x, lenv_avail_lin (lenv_pinst σ Δ) x ↔ lenv_avail_lin Δ x) as Hl.
  { intros x. unfold lenv_avail_lin. rewrite lenv_pinst_lookup.
    destruct (Δ !! x) as [[T|]|]; simpl; split; intros (U & HU & Hn); simplify_eq.
    + eexists. split; [reflexivity|]. by rewrite <-(unlimited_pinst_iff σ).
    + eexists. split; [reflexivity|]. by rewrite unlimited_pinst_iff. }
  unfold term_wf. split; intros (Hfc & Hfv & Hrv); split_and!; try done.
  - eapply allfv_mono; [|exact Hfv]. intros x. apply Ha.
  - intros x Hx. apply Hrv, Hl, Hx.
  - eapply allfv_mono; [|exact Hfv]. intros x. apply Ha.
  - intros x Hx. apply Hrv, Hl, Hx.
Qed.

Lemma typed_term_wf_s W Φ Ψ Θ Δ F e T : typed W Φ Ψ Θ Δ F e T → term_wf Θ Δ e.
Proof.
  unfold term_wf. induction 1 as
    [Φ Ψ Δ F HΔ
    |Φ Ψ Δ F k T HΔ Hk _
    |Φ Ψ Δ F x T Ho
    |Φ Ψ Δ F c s k s' y HΔ _ _
    |Φ Ψ Θ Δ F e T U ub lb φ _ _ _ IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ _ _ IH1 _ IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ _ IH1 _ IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ _ IH1 _ IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ _ IH1 _ IH2
    |Φ Ψ Θ Δ F e T U _ IH
    |Φ Ψ Θ Δ F e T U _ IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ _ IH0 _ IH1 _ IH2
    |Φ Ψ Δ F e m C ub T φ HΔ _ _ IH
    |Φ Ψ Θ Δ' Δ F e T Hwk _ IH
    |Φ Ψ Θ Δ U F e T Hu _ IH
    |Φ Ψ Θ Δ F e T T' _ _ IH].
  (* E-Unit *)
  - split_and!; simpl; [by rewrite dom_empty_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-Const *)
  - split_and!; simpl; [by rewrite dom_empty_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-LVar *)
  - split_and!; simpl.
    + by rewrite dom_empty_L.
    + destruct Ho as [Hlk _]. by exists T.
    + intros x' (T' & Hx' & _). destruct Ho as [_ Huniq].
      by destruct (Huniq x' T' Hx') as [-> _].
  (* E-Ch *)
  - split_and!; simpl; [by rewrite dom_singleton_L|done|].
    intros x Hx. exact (lenv_empty_no_avail _ _ HΔ (lenv_avail_lin_avail _ _ Hx)).
  (* E-Abs *)
  - destruct IH as (Hfc & Hfv & Hrv).
    split_and!; simpl; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      * intros _. done.
      * intros (T' & HT'). by exists T'.
    + intros x (T' & Hx & Hnb). apply (Hrv (S x)). exists T'. auto.
  (* E-App *)
  - destruct IH1 as (Hfc1 & Hfv1 & Hrv1). destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-Pair *)
  - destruct IH1 as (Hfc1 & Hfv1 & Hrv1). destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-Let* *)
  - destruct IH1 as (Hfc1 & Hfv1 & Hrv1). destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply Hrv2. exists T'. auto.
  (* E-LetPair *)
  - destruct IH1 as (Hfc1 & Hfv1 & Hrv1). destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split.
      * eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv2]. intros [|[|x]]; simpl.
        -- intros _. done.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv1. exists T'. auto.
      * right. apply (Hrv2 (S (S x))). exists T'. auto.
  (* E-Inj *)
  - exact IH.
  - exact IH.
  (* E-Case *)
  - destruct IH0 as (Hfc0 & Hfv0 & Hrv0). destruct IH1 as (Hfc1 & Hfv1 & Hrv1).
    destruct IH2 as (Hfc2 & Hfv2 & Hrv2).
    split_and!.
    + simpl. rewrite (tenv_join_dom _ _ _ (proj1 HΘ)). set_solver.
    + simpl. split_and!.
      * eapply allfv_mono; [|exact Hfv0]. intros x (T' & ?).
        exists T'. eauto using lenv_split_lookup_l.
      * eapply allfv_mono; [|exact Hfv1]. intros [|x]; simpl.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
      * eapply allfv_mono; [|exact Hfv2]. intros [|x]; simpl.
        -- intros _. done.
        -- intros (T' & ?). exists T'. eauto using lenv_split_lookup_r.
    + intros x (T' & Hx & Hnb). simpl.
      destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
      * left. apply Hrv0. exists T'. auto.
      * right. left. apply (Hrv1 (S x)). exists T'. auto.
  (* E-Exp *)
  - destruct (proj1 (term_wf_lenv_pinst _ _ _ _) IH) as (Hfc & Hfv & Hrv).
    split_and!; simpl; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      * intros _. done.
      * intros (T' & HT'). by exists T'.
    + intros x (T' & Hx & Hnb). apply (Hrv (S x)). exists T'. auto.
  (* E-Weak *)
  - destruct IH as (Hfc & Hfv & Hrv). split_and!; [done| |].
    + eapply allfv_mono; [|exact Hfv]. intros x Hx. eauto using lenv_wk_avail.
    + intros x Hx. apply Hrv. eauto using lenv_wk_avail_lin.
  (* E-Contract *)
  - destruct IH as (Hfc & Hfv & Hrv). split_and!.
    + by rewrite fchans_rename.
    + apply allfv_rename. eapply allfv_mono; [|exact Hfv].
      intros [|[|x]] (T' & HT'); simpl in *; by exists T'.
    + intros [|x] (T' & Hx & Hnb); simpl in Hx.
      * simplify_eq. by destruct (Hnb Hu).
      * apply (freevar_rename e (S (S x)) pred). apply Hrv. by exists T'.
  (* E-Conv *)
  - exact IH.
Qed.

Ltac frame_pinst :=
  rewrite ?tenv_heads_pinst, ?lenv_heads_pinst, ?heads_pinst, ?opt_heads_pinst,
    <-?set_map_union_L, <-?sf_inst_union, <-?sf_pinst_union.

(** Frame instantiation and point substitution in one induction: the
    frame variables become frames above their hypotheses at a later
    world W₁, the point variables become points by σ. A box body is
    typed with its ιs as variables, so the box case substitutes the
    instance xs there and the outer σ beyond (plist_pup_shift). *)
Lemma typed_sem_rules W Φ Ψ Θ Δ F e T :
  typed W Φ Ψ Θ Δ F e T →
  ∀ W1 ρ σ, world_wf W → wext W W1 → inst_ok W1 (fhyps_pinst σ Φ) ρ →
  hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) →
  sem_rules W1 (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_inst ρ (sf_pinst σ F)) e (pinst_ty σ T).
Proof.
  induction 1 as
    [Φ Ψ Δ F HΔ
    |Φ Ψ Δ F k T HΔ Hk Hks
    |Φ Ψ Δ F x T Ho
    |Φ Ψ Δ F c s k s' y HΔ Hs Hk
    |Φ Ψ Θ Δ F e T U ub lb φ Hφ Hlb Hb IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ Hub H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ H0 IH0 H1 IH1 H2 IH2
    |Φ Ψ Δ F e m C ub T φ HΔ Hφ Hb IH
    |Φ Ψ Θ Δ' Δ F e T Hwk H IH
    |Φ Ψ Θ Δ U F e T Hu H IH
    |Φ Ψ Θ Δ F e T T' Hteq H IH]; intros W1 ρ σ HW HW1 Hρ HΨ;
    pose proof HW1 as (HN & He & Hl & HS).
  - rewrite tenv_pinst_empty. apply sr_unit. by apply lenv_empty_pinst.
  - rewrite tenv_pinst_empty. apply sr_konst; [by apply lenv_empty_pinst|].
    apply (konst_ty_pinst W W1 σ HW HW1 (seqs W Ψ) _ (slt W Ψ) _ (skn W Ψ)); [| | |done|done].
    + intros x y Hxy. by apply (seqs_pinst W W1 σ HW HW1 Ψ).
    + intros x y Hxy. by apply (slt_pinst W W1 σ HW HW1 Ψ).
    + intros x Hx. by apply (skn_pinst_known W W1 σ HW HW1 Ψ).
  - rewrite tenv_pinst_empty. apply sr_var. by apply lenv_only_pinst.
  - unfold tenv_pinst. rewrite map_fmap_singleton. simpl.
    apply sr_chan; [by apply lenv_empty_pinst|done|by apply (seqs_pinst W W1 σ HW HW1 Ψ)].
  - cbn [pinst_ty]. apply sr_lam.
    + assert (term_wf Θ (lenv_pinst σ (Some T :: Δ)) e) as (Hfc & Hwf)
        by (rewrite term_wf_lenv_pinst; exact (typed_term_wf_s _ _ _ _ _ _ _ _ Hb)).
      split; [unfold tenv_pinst; by rewrite dom_fmap_L|exact Hwf].
    + rewrite tenv_heads_pinst, lenv_heads_pinst, <-set_map_union_L.
      by apply (lb_below_h_pinst W W1 σ HW HW1 Ψ).
    + intros W2 F' HW2 Hub'. rewrite <-(sf_inst_fresh ρ φ F'), <-(sf_pinst_fresh σ φ).
      apply (IH W2 _ σ HW (wext_trans _ _ _ HW1 HW2)).
      * apply inst_ok_pinst_insert; [exact (inst_ok_mono _ _ _ _ HW2 Hρ)|exact Hub'].
      * exact (hyps_hold_wext _ _ _ HW2 HΨ).
  - apply (sr_app W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + apply (ub_below_s_inst W1 W1 (fhyps_pinst σ Φ)); [apply HS|exact (wext_refl _ HS)|done|].
      apply (ub_below_s_pinst W W1 σ Ψ []); [done|done| |done].
      by apply (hyps_hold_ground W W1 σ HW HW1).
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + frame_pinst. by apply IH2.
  - cbn [pinst_ty].
    apply (sr_pair W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply IH1.
    + frame_pinst. by apply IH2.
  - apply (sr_letu W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + by apply IH2.
  - apply (sr_letp W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 W1 ρ σ).
    + by apply (IH2 W1 ρ σ).
  - cbn [pinst_ty]. apply sr_inj1. by apply IH.
  - cbn [pinst_ty]. apply sr_inj2. by apply IH.
  - apply (sr_case W1 _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_g W W1 σ HW HW1 Ψ).
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH0 W1 ρ σ).
    + by apply (IH1 W1 ρ σ).
    + by apply (IH2 W1 ρ σ).
  - cbn [pinst_ty]. rewrite tenv_pinst_empty. apply sr_box; [by apply lenv_unl_pinst| |].
    { pose proof (typed_term_wf_s _ _ _ _ _ _ _ _ Hb) as Hwf.
      rewrite term_wf_lenv_pinst in Hwf.
      change (term_wf ∅ (lenv_pinst σ (Some (TBox m C (TLolli ub None TUnit T)) :: Δ)) e).
      by rewrite term_wf_lenv_pinst. }
    intros W2 xs F' HW2 Hxs HC HK Hub'. subst m.
    assert (∀ a, pt_inst (pt_inst (plist xs) ∘ pup (length xs) σ) (pshift (length xs) a) = σ a) as Hsh
      by (intros a; by apply plist_pup_shift).
    set (m := length xs).
    assert (lenv_pinst (pt_inst (plist xs) ∘ pup m σ) (lenv_pinst (pshift m) (Some (TBox m C (TLolli ub None TUnit T)) :: Δ))
            = lenv_pinst σ (Some (TBox m C (TLolli ub None TUnit T)) :: Δ)) as E1.
    { rewrite lenv_pinst_comp. apply lenv_pinst_ext. exact Hsh. }
    assert (pinst_ty (pt_inst (plist xs) ∘ pup m σ) T = ty_inst xs (pinst_ty (pup m σ) T)) as E2.
    { unfold ty_inst. by rewrite pinst_ty_comp. }
    assert (fhyps_pinst (pt_inst (plist xs) ∘ pup m σ) (fhyps_pinst (pshift m) Φ)
            = fhyps_pinst σ Φ) as E3.
    { unfold fhyps_pinst. rewrite <-map_fmap_compose. apply map_fmap_ext.
      intros i [u|] _; simpl; [|done]. f_equal. rewrite pt_inst_comp.
      apply pt_inst_ext. exact Hsh. }
    assert (hyps_inst (pt_inst (plist xs) ∘ pup m σ)
              (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
            = hyps_inst σ Ψ ++ [(bcs_inst σ C, xs)]) as E4.
    { rewrite hyps_inst_app, hyps_comp, hyps_inst_single. f_equal.
      - apply hyps_inst_ext. exact Hsh.
      - f_equal. f_equal; [|apply ids_plist].
        rewrite bcs_comp. apply bcs_inst_ext. exact Hsh. }
    pose proof (IH W2 (λ ψ, if decide (ψ = φ) then F' else ρ ψ)
                  (pt_inst (plist xs) ∘ pup m σ) HW (wext_trans _ _ _ HW1 HW2)) as Hb'.
    fold m in Hb'. rewrite tenv_pinst_empty, sf_pinst_fresh, sf_inst_fresh, E1, E2, E4 in Hb'.
    apply Hb'.
    + apply inst_ok_pinst_insert.
      * rewrite E3. exact (inst_ok_mono _ _ _ _ HW2 Hρ).
      * destruct ub as [u|]; simpl in *; [|done]. by rewrite pt_inst_comp in Hub'.
    + apply hyps_hold_app; [exact (hyps_hold_wext _ _ _ HW2 HΨ)|].
      intros C0 xs0 Hg. apply list_elem_of_singleton in Hg. injection Hg as -> ->. done.
  - eapply sr_wk; [by apply lenv_wk_pinst|by apply IH].
  - cbn [lenv_pinst]. apply sr_contract; [by apply unlimited_pinst|by apply (IH W1 ρ σ)].
  - eapply sr_conv; [by apply eqT_pinst|by apply IH].
Qed.


(** ** The substitution lemma on its own

    Instantiating point variables by points preserves derivations at
    the same world. [typed_sem_rules] composes this substitution with
    frame instantiation; the fundamental theorem needs only that. *)

Lemma kscoped_pinst peq plt pk k T σ :
  konst_ty peq plt pk k T → kscoped k T → kscoped k (pinst_ty σ T).
Proof. destruct 1; simpl; auto. Qed.

Lemma fhyps_pinst_insert σ Φ φ u :
  fhyps_pinst σ (<[φ := u]> Φ) = <[φ := pt_inst σ <$> u]> (fhyps_pinst σ Φ).
Proof. unfold fhyps_pinst. by rewrite fmap_insert. Qed.

Lemma fhyps_pinst_dom σ Φ : dom (fhyps_pinst σ Φ) = dom Φ.
Proof. unfold fhyps_pinst. by rewrite dom_fmap_L. Qed.

Lemma fhyps_pinst_comp_ext τ σ τ' σ' Φ :
  (∀ a, pt_inst τ (σ a) = pt_inst τ' (σ' a)) →
  fhyps_pinst τ (fhyps_pinst σ Φ) = fhyps_pinst τ' (fhyps_pinst σ' Φ).
Proof.
  intros H. unfold fhyps_pinst. rewrite <-!map_fmap_compose. apply map_fmap_ext.
  intros i [u|] _; simpl; [|done]. f_equal. rewrite !pt_inst_comp. by apply pt_inst_ext.
Qed.

Lemma pup_pshift m σ a : pt_inst (pup m σ) (pshift m a) = pt_inst (pshift m) (σ a).
Proof.
  unfold pshift. rewrite pt_inst_pvar_at. unfold pup. rewrite decide_False by lia.
  by replace (a + m - m) with a by lia.
Qed.

Lemma typed_pinst W Φ Ψ Θ Δ F e T :
  strict W → typed W Φ Ψ Θ Δ F e T →
  ∀ σ Ψ', hyps_hold (seqs W Ψ') (slt W Ψ') (skn W Ψ') (hyps_inst σ Ψ) →
  typed W (fhyps_pinst σ Φ) Ψ' (tenv_pinst σ Θ) (lenv_pinst σ Δ) (sf_pinst σ F) e (pinst_ty σ T).
Proof.
  intros HW. pose proof (proj1 HW) as Hwf. pose proof (wext_refl _ HW) as HWW.
  induction 1 as
    [Φ Ψ Δ F HΔ
    |Φ Ψ Δ F k T HΔ Hk Hks
    |Φ Ψ Δ F x T Ho
    |Φ Ψ Δ F c s k s' y HΔ Hs Hk
    |Φ Ψ Θ Δ F e T U ub lb φ Hφ Hlb Hb IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U HΘ HΔ Hub H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T HΘ HΔ H1 IH1 H2 IH2
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Δ F e T U H IH
    |Φ Ψ Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T HΘ HΔ H0 IH0 H1 IH1 H2 IH2
    |Φ Ψ Δ F e m C ub T φ HΔ Hφ Hb IH
    |Φ Ψ Θ Δ' Δ F e T Hwk H IH
    |Φ Ψ Θ Δ U F e T Hu H IH
    |Φ Ψ Θ Δ F e T T' Hteq H IH]; intros σ Ψ' HΨ.
  - rewrite tenv_pinst_empty. apply t_unit. by apply lenv_empty_pinst.
  - rewrite tenv_pinst_empty. apply t_konst; [by apply lenv_empty_pinst| |].
    + apply (konst_ty_pinst W W σ Hwf HWW (seqs W Ψ) _ (slt W Ψ) _ (skn W Ψ)); [| | |done|done].
      * intros x y Hxy. by apply (seqs_pinst_s W W σ Hwf HWW Ψ).
      * intros x y Hxy. by apply (slt_pinst_s W W σ Hwf HWW Ψ).
      * intros x Hx. by apply (skn_pinst_s W W σ Hwf HWW Ψ).
    + by apply (kscoped_pinst (seqs W Ψ) (slt W Ψ) (skn W Ψ)).
  - rewrite tenv_pinst_empty. apply t_var. by apply lenv_only_pinst.
  - unfold tenv_pinst. rewrite map_fmap_singleton. simpl.
    apply t_chan; [by apply lenv_empty_pinst|done|by apply (seqs_pinst_s W W σ Hwf HWW Ψ)].
  - cbn [pinst_ty]. apply (t_lam W _ _ _ _ _ _ _ _ _ _ φ).
    + by rewrite fhyps_pinst_dom.
    + rewrite tenv_heads_pinst, lenv_heads_pinst, <-set_map_union_L.
      by apply (lb_below_h_pinst_s W W σ Hwf HWW Ψ).
    + pose proof (IH σ Ψ' HΨ) as H. by rewrite fhyps_pinst_insert, sf_pinst_fresh in H.
  - apply (t_app W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pt_inst σ <$> ub) (pt_inst σ <$> lb) (pinst_ty σ T)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + by apply (ub_below_s_pinst W W σ Ψ Ψ').
    + frame_pinst. by apply (IH1 σ Ψ').
    + frame_pinst. by apply IH2.
  - cbn [pinst_ty].
    apply (t_pair W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + frame_pinst. by apply IH1.
    + frame_pinst. by apply IH2.
  - apply (t_letu W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 σ Ψ').
    + by apply IH2.
  - apply (t_letp W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH1 σ Ψ').
    + by apply (IH2 σ Ψ').
  - cbn [pinst_ty]. apply t_inj1. by apply IH.
  - cbn [pinst_ty]. apply t_inj2. by apply IH.
  - apply (t_case W _ _ _ (tenv_pinst σ Θ1) (tenv_pinst σ Θ2) _ (lenv_pinst σ Δ1) (lenv_pinst σ Δ2)
             _ _ _ _ (pinst_ty σ T1) (pinst_ty σ T2)).
    + by apply (tenv_comp_pinst_s W W σ Hwf HWW Ψ Ψ').
    + by apply lenv_split_pinst.
    + frame_pinst. by apply (IH0 σ Ψ').
    + by apply (IH1 σ Ψ').
    + by apply (IH2 σ Ψ').
  - cbn [pinst_ty]. rewrite tenv_pinst_empty.
    apply (t_box W _ _ _ _ _ _ _ _ _ φ); [by apply lenv_unl_pinst|by rewrite fhyps_pinst_dom|].
    set (Ψt := hyps_inst (pshift m) Ψ' ++ [(bcs_inst (pshift m) (bcs_inst σ C), ids m)]).
    assert (hyps_hold (seqs W Ψt) (slt W Ψt) (skn W Ψt)
              (hyps_inst (pup m σ) (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])))
      as HΨ'.
    { assert (hyps_hold (seqs W Ψt) (slt W Ψt) (skn W Ψt) (hyps_inst (pshift m) Ψ')) as Hsub.
      { apply hyps_hold_sub. intros g Hg. apply elem_of_app. by left. }
      rewrite hyps_inst_app, hyps_comp,
        (hyps_inst_ext (pt_inst (pup m σ) ∘ pshift m) (pt_inst (pshift m) ∘ σ) Ψ)
        by (intros a; apply pup_pshift).
      rewrite <-hyps_comp. apply hyps_hold_app.
      - apply (hyps_hold_inst (seqs W Ψ') _ (slt W Ψ') _ (skn W Ψ') _ (pshift m)); [| | |exact HΨ].
        + intros x y Hxy. by apply (seqs_pinst_s W W (pshift m) Hwf HWW Ψ').
        + intros x y Hxy. by apply (slt_pinst_s W W (pshift m) Hwf HWW Ψ').
        + intros x Hx. by apply (skn_pinst_s W W (pshift m) Hwf HWW Ψ').
      - rewrite hyps_inst_single. apply hyps_hold_sub. intros g Hg.
        apply list_elem_of_singleton in Hg as ->. apply elem_of_app. right.
        apply list_elem_of_singleton. rewrite ids_pup, !bcs_comp. f_equal.
        apply bcs_inst_ext. intros a. unfold compose. apply pup_pshift. }
    pose proof (IH (pup m σ) _ HΨ') as H.
    rewrite tenv_pinst_empty, sf_pinst_fresh, fhyps_pinst_insert in H.
    rewrite (fhyps_pinst_comp_ext (pup m σ) (pshift m) (pshift m) σ) in H by apply pup_pshift.
    rewrite lenv_pinst_comp, (lenv_pinst_ext _ (pt_inst (pshift m) ∘ σ)), <-lenv_pinst_comp in H
      by apply pup_pshift.
    exact H.
  - eapply t_wk; [by apply lenv_wk_pinst|by apply IH].
  - cbn [lenv_pinst]. apply t_contract; [by apply unlimited_pinst|by apply (IH σ Ψ')].
  - eapply t_conv; [by apply eqT_pinst|by apply IH].
Qed.


(** A closed derivation: no frame variables, no hypotheses, and the
    identity substitution. *)
Lemma typed_sem_rules_closed W Θ Δ F e T :
  strict W → typed W ∅ [] Θ Δ (F, None) e T → sem_rules W Θ Δ F e T.
Proof.
  intros HW Ht.
  pose proof (typed_sem_rules _ _ _ _ _ _ _ _ Ht W (λ _, ∅) pvar (proj1 HW) (wext_refl _ HW)) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  unfold sf_inst in H. simpl in H. rewrite union_empty_r_L in H.
  apply H.
  - intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty.
  - intros C xs Hg. cbn in Hg. by apply elem_of_nil in Hg.
Qed.

Lemma typed_term_wf W Θ Δ F e T :
  typed W ∅ [] Θ Δ (F, None) e T → strict W → term_wf Θ Δ e.
Proof. intros Ht _. exact (typed_term_wf_s _ _ _ _ _ _ _ _ Ht). Qed.

(** ** The fundamental theorem for terms *)

Theorem fundamental W Θ Δ F e T :
  typed W ∅ [] Θ Δ (F, None) e T → strict W → sem_typed W Θ Δ F e T.
Proof. intros Ht HW. apply sem_rules_fundamental; [|done]. by apply typed_sem_rules_closed. Qed.

(** ** Processes

    P-Term and P-Connect of §9. The side conditions are the implicit
    well-formedness of the spec: Θ_B holds both ends, dual at aliased
    points, of exactly the channels of C₀; the unions C₁ ⊍ C₂ ⊍ C₀ and
    Σ₁, Σ₂, Σ_C are disjoint; the cut ends are dual at aliased points. *)

Inductive ptyped (W : world) : senv → proc → ty → Prop :=
  | pt_term Σ ΘB C0 t T :                               (* P-Term *)
      prim T → dom ΘB = C0 → dom Σ ## C0 →
      (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
      typed W ∅ [] (tenv_of Σ ∪ ΘB) [] (∅, None) t T →
      ptyped W Σ (C0, {[+ t +]}) T
  | pt_connect Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :         (* P-Connect *)
      ptyped W (Σ1 ∪ ΣC) (C1, E1) T → ptyped W (Σ2 ∪ ΣC') (C2, E2) TUnit →
      dom ΣC = C0 → dom ΣC' = C0 →
      (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' → w_eq W e.2 e'.2 ∧ sdual e.1 e'.1) →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
      C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
      ptyped W (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T.

Lemma ptyped_prim W Σ p T : ptyped W Σ p T → prim T.
Proof. induction 1; auto. Qed.

(** One world for both components: W ⊔ W lies below W. *)
Lemma wext_join_self W : strict W → wext (wjoin W W) W.
Proof.
  intros HW.
  destruct (wgen_in_world W (λ x y, w_eq W x y ∨ w_eq W x y)
              (λ x y, w_lt W x y ∨ w_lt W x y)) as [Heq Hlt];
    [apply HW|naive_solver|naive_solver|].
  split_and!; [simpl; set_solver|exact Heq|exact Hlt|exact HW].
Qed.

Theorem fundamental_proc W Σ p T : ptyped W Σ p T → strict W → sem_ptyped W Σ p T.
Proof.
  induction 1 as [Σ ΘB C0 t T HT Hd Hdj Hb Hdu Ht
                 |Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T H1 IH1 H2 IH2 HdC HdC' Hcut
                    ? ? ? ? ? ? ? ? ? ?]; intros HW.
  - apply (Prel_term W Σ ΘB C0); try done. by apply fundamental.
  - assert (strict (wjoin W W)) as HWW by (by apply wjoin_sub_strict, wext_refl).
    intros n. eapply Prel_mono; [apply HWW|by apply wext_join_self|].
    revert n. apply (Prel_connect W W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T); try done.
    + exact (ptyped_prim _ _ _ _ H1).
    + by apply IH1.
    + by apply IH2.
    + intros c e e' He He'. destruct (Hcut c e e' He He') as [Heq Hs].
      split; [by apply wjoin_l|done].
    + apply HW.
    + apply HW.
Qed.

(** ** Soundness: typed closed configurations are deadlock free *)

Theorem soundness W p T : strict W → ptyped W ∅ p T → deadlock_free p.
Proof. intros HW Hp. apply (adequacy W T p). by apply fundamental_proc. Qed.

(** ** Example: a box that needs ι ≺ ι′ between its arguments (58)

    ordered : □(∀ι ι′. {ι ≺ ι′}.^⊥ Close@ι ⊗ Close@ι′ ⊸^{ι′}_⊤ ∗)
    ordered = !(f = λp. let (c, d) = p in let () = close c in close d)

    close c blocks at ι while the body still holds d at ι′, so E-App
    asks ι ≺ ι′. Program order relates nothing between two point
    variables, so without the constraint the box does not type. With it
    the fact is the hypothesis itself. A caller forces the box at
    ((a, 0), (a, 1)), where program order meets the constraint. *)

Definition ord_body : ty :=
  TLolli (Some (pvar 1)) None (TProd (TSess SEnd (pvar 0)) (TSess SEnd (pvar 1))) TUnit.

Definition ord_C : bcs := BCs [] (λ g, g = FLt (pvar 0) (pvar 1)).

Definition ord_ty : ty := TBox 2 ord_C (TLolli None None TUnit ord_body).

(** A ≺ fact of a hypothesis without outer points. *)
Lemma sl_hyp0 W Ψ P xs x y x' y' :
  (BCs [] P, xs) ∈ Ψ → P (FLt x y) → fact_scoped (length xs) (FLt x y) →
  pt_inst (plist xs) x = x' → pt_inst (plist xs) y = y' → slt W Ψ x' y'.
Proof.
  intros Hg Hxy Hs <- <-. apply sl_h. exists (BCs [] P), xs. split; [done|].
  exists (FLt x y). split; [by apply bcs_open_nil|done].
Qed.

Definition ord_box : expr :=
  EBox (Lam (LetP (Var 0)
    (LetU (App (Konst KClos) (Var 1)) (App (Konst KClos) (Var 0))))).

Lemma ordered_typed W F : world_wf W → typed W ∅ [] ∅ [] F ord_box ord_ty.
Proof.
  intros HW. unfold ord_box, ord_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  cbn. set (Bx := TBox 2 _ _).
  set (Ψ := [(_, _)]). set (Tc := TSess SEnd (pvar 0)). set (Td := TSess SEnd (pvar 1)).
  unfold ord_body. fold Tc Td.
  apply (t_lam W _ _ _ _ _ _ _ _ _ _ 1); [set_solver|done|].
  apply (t_letp W _ _ ∅ ∅ ∅ _ [Some (TProd Tc Td); None] [None; Some Bx] _ _ _ Tc Td).
  { apply tenv_comp_empty_l. intros ? ?. apply se_sym. }
  { repeat constructor. }
  { apply t_var. split; [done|]. intros [|[|y]] T' Hy; simplify_eq/=; done. }
  apply (t_letu W _ _ ∅ ∅ ∅ _ [None; Some Tc; None; None] [Some Td; None; None; Some Bx]).
  { apply tenv_comp_empty_l. intros ? ?. apply se_sym. }
  { repeat constructor. }
  { eapply (t_app W _ _ ∅ ∅ ∅ _ (lenv_nones _) _ _ _ _ (Some (pvar 0)) None Tc TUnit).
    - apply tenv_comp_empty_l. intros ? ?. apply se_sym.
    - apply lenv_split_nones_l.
    - apply ub_below_s_intro.
      + intros y Hy. unfold sf_union, tenv_heads in Hy. rewrite map_fold_empty in Hy.
        subst Td Bx. simpl in Hy. assert (y = pvar 1) as -> by set_solver.
        eapply (sl_hyp0 W _ _ _ (pvar 0) (pvar 1)); [by left|done|cbn; lia|done|done].
      + exists (pvar 1). split; [done|]. right.
        eapply (sl_hyp0 W _ _ _ (pvar 0) (pvar 1)); [by left|done|cbn; lia|done|done].
    - apply t_konst; [apply lenv_empty_nones|constructor|done].
    - apply t_var. split; [done|]. intros [|[|y]] T' Hy; simplify_eq/=; try done.
      destruct y as [|[|y]]; simplify_eq/=. }
  eapply t_wk; [apply (lwk_cons _ [None; None; None]), lwk_cons, lwk_cons, lwk_drop;
                [done|constructor]|].
  eapply (t_app W _ _ ∅ ∅ ∅ _ (lenv_nones _) _ _ _ _ (Some (pvar 1)) None Td TUnit).
  - apply tenv_comp_empty_l. intros ? ?. apply se_sym.
  - apply lenv_split_nones_l.
  - apply ub_below_s_intro.
    + intros y Hy. simpl in Hy. set_solver.
    + exists (pvar 1). split; [done|]. left. apply se_refl.
  - apply t_konst; [apply lenv_empty_nones|constructor|done].
  - apply t_var. split; [done|]. intros [|[|y]] T' Hy; simplify_eq/=; try done.
    destruct y as [|[|y]]; simplify_eq/=.
Qed.

(** Forcing at ((a, 0), (a, 1)): (a, 0) ≺ (a, 1) by program order, and
    both points are known when a is (59). *)
Lemma ordered_force W F a : world_wf W → pt_known W (Pt (NConst a) 0) →
  typed W ∅ [] ∅ [] (F, None) (App EForce ord_box)
    (ty_inst [Pt (NConst a) 0; Pt (NConst a) 1] ord_body).
Proof.
  intros HW Ha. apply typed_force with (m := 2) (C := ord_C) (ub := None); [done|done| | |done|].
  - apply bcs_hold_intro. intros g -> _. cbn.
    apply sl_w. apply (wf_lt_po_n W (Pt (NConst a) 0) 0 HW).
  - constructor; [left; exact Ha|constructor; [left; unfold pt_known in *; exact Ha|constructor]].
  - by apply ordered_typed.
Qed.
