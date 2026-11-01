(** * Frames, hypotheses and the fact theory of the static system (spec §9)

    Static frames, box hypotheses, and the two judgments Γ ⊢ x ≡ y
    ([seqs]) and Γ ⊢ a ≺ b ([fl], [slt]) from which the static system
    reads every fact (sharp edges 64, 65). [steq] is ≈ up to Γ ⊢ ≡
    (sharp edges 67). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export rules.SemanticRules.

Set Default Proof Using "All".

(** ** Static frames and hypotheses (sharp edges 54, 56)

    E-Abs and E-Exp type the body under the frame {φ} for a fresh
    frame variable φ, with the single hypothesis u ≺ φ. A fresh point
    would not do, because a world that adds a fresh point cannot be
    dropped again (counterexamples/DropCounter.v). A frame is a set of
    points and at most one frame variable. The body of λ or box starts
    at {φ} and the other rules only add points. φ occurs only in
    frames and in the hypotheses Φ, never in a type, an environment or
    the world, so it is never a point that [new] or force could alias.
    x ≺ φ holds when x ≼ u in W for the hypothesis u ≺ φ. E-Exp types
    the body with the ιs as point variables (sharp edges 57). *)

(** The second component of a frame (sharp edges 103): a frame
    variable φ ([FVar φ]), or the ⊥ flag with or without a frame
    variable ([FBot o]). [None] is neither. The flag says that the
    context holds an unopened existential with lower bound ⊥, so no
    known point lies below everything the context holds. *)
Inductive fslot := FVar (φ : nat) | FBot (o : option nat).

Notation sframe := (gset point * option fslot)%type.
Notation fhyps := (gmap nat (option point)).

Definition fs_var (o : option fslot) : option nat :=
  match o with Some (FVar φ) => Some φ | Some (FBot o') => o' | None => None end.

Definition fs_bot (o : option fslot) : bool :=
  match o with Some (FBot _) => true | _ => false end.

(** F[ρ]: replace the frame variable by a concrete frame, and the flag
    by the point [pbot] of relation/Worlds.v. *)
Definition sf_inst (ρ : nat → gset point) (F : sframe) : gset point :=
  F.1 ∪ match fs_var F.2 with Some φ => ρ φ | None => ∅ end ∪ bot_pts (fs_bot F.2).

Definition sf_union (F : sframe) (X : gset point) : sframe := (F.1 ∪ X, F.2).

(** F, X with the flag set when b holds: the points X and flag b are
    the heads of what the context of a subterm holds. *)
Definition sf_unionb (F : sframe) (X : gset point) (b : bool) : sframe :=
  if b then (F.1 ∪ X, Some (FBot (fs_var F.2))) else sf_union F X.

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

(** λ ≼ H with the flag b of H (sharp edges 103). A flagged H holds
    something below no known point, so no lower point of an arrow lies
    below it. *)
Definition lb_below_hb (W : world) (Ψ : hyps) (lb : option point)
    (H : gset point) (b : bool) : Prop :=
  if b then False else lb_below_h W Ψ lb H.

(** ℓ ≼ H for the lower bound of an existential, with the flag b of H.
    ⊥ lies below everything. *)
Definition lbx_below_h (W : world) (Ψ : hyps) (lb : lbound)
    (H : gset point) (b : bool) : Prop :=
  match lb with
  | LBot => True
  | LTop => H = ∅ ∧ b = false
  | LPt x => (∀ y, y ∈ H → sle W Ψ x y) ∧ b = false
  end.

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

(** ** Types up to Γ ⊢ ≡ (sharp edges 67)

    [steq W Ψ T U] is ≈ with the points of T outside session types and
    boxes compared by Γ ⊢ ≡ ([seqs W Ψ]). A box and an existential
    are compared by ≈ with their points on the nose, because their
    points live under the binder of their ιs. E-Conv reads it. [teq_steq] makes ≈ a special case,
    and [steq_teqW] carries it into ≈_W₁ of a world where the
    hypotheses hold. *)
Fixpoint steq (W : world) (Ψ : hyps) (T U : ty) : Prop :=
  match T, U with
  | TUnit, TUnit => True
  | TLolli ub lb T1 T2, TLolli ub' lb' U1 U2 =>
      opt_rel (seqs W Ψ) ub ub' ∧ opt_rel (seqs W Ψ) lb lb' ∧
      steq W Ψ T1 U1 ∧ steq W Ψ T2 U2
  | TProd T1 T2, TProd U1 U2 => steq W Ψ T1 U1 ∧ steq W Ψ T2 U2
  | TSum T1 T2, TSum U1 U2 => steq W Ψ T1 U1 ∧ steq W Ψ T2 U2
  | TBoxM T1, TBoxM U1 => teq T1 U1
  | TAll n C T1, TAll n' C' U1 => n = n' ∧ C = C' ∧ teq T1 U1
  | TSess s x, TSess r y => seqs W Ψ x y ∧ seq s r
  | TEx lb n C T1, TEx lb' n' C' U1 => lb = lb' ∧ n = n' ∧ C = C' ∧ teq T1 U1
  | _, _ => False
  end.

Lemma teq_steq W Ψ T : ∀ U, teq T U → steq W Ψ T U.
Proof.
  unfold teq. induction T; intros [] H; simpl in *; unfold teq in *; try done.
  - destruct H as (-> & -> & ? & ?). split_and!; auto.
    + destruct ub0; simpl; [apply se_refl|done].
    + destruct lb0; simpl; [apply se_refl|done].
  - destruct H. split; auto.
  - destruct H. split; auto.
  - destruct H as [<- ?]. split; [apply se_refl|done].
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
              (∀ φ, fs_var F.2 = Some φ → fl (FCtx W Ψ Φ) (NP x) (NV φ)) ∧
              fs_bot F.2 = false
  end.

(** The frame variable part read as x ≼ u for the hypothesis u ≺ φ. *)
Lemma ub_below_s_intro W Ψ Φ x P o :
  (∀ y, y ∈ P → slt W Ψ x y) →
  match o with
  | Some (FVar φ) => ∃ u, Φ !! φ = Some (Some u) ∧ sle W Ψ x u
  | Some (FBot _) => False
  | None => True
  end →
  ub_below_s W Ψ Φ (Some x) (P, o).
Proof.
  intros H1 H2. split_and!; simpl.
  - intros y Hy. apply fl_points. by apply H1.
  - intros φ Hφ. destruct o as [[φ'|o']|]; simpl in Hφ; [|done|done]. injection Hφ as ->.
    destruct H2 as (u & Hu & [Heq|Hlt]).
    + apply (fl_eql (FCtx W Ψ Φ) _ u); [done|]. by apply (fl_v (FCtx W Ψ Φ)).
    + apply (fl_trans (FCtx W Ψ Φ) _ u); [by apply fl_points|]. by apply (fl_v (FCtx W Ψ Φ)).
  - by destruct o as [[]|].
Qed.

(** ρ meets the hypotheses: {u} ≺_W ρ(φ) for every u ≺ φ in Φ. *)
Definition inst_ok (W : world) (Φ : fhyps) (ρ : nat → gset point) : Prop :=
  ∀ φ u, Φ !! φ = Some u → ub_below W u (ρ φ).
