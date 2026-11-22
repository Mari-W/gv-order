(** * Contexts, futures, the fact theory and the cost relations (stage S2)

    The judgment Θ ; Γ ; Δ ⊢^F_{W,N} e : T ▷ c reads

    - Θ : end ⇀ (S@x)^a_m, one entry per end, with the credit and the
      tickets of the end,
    - Γ, the facts: box constraints in force with their instances,
    - Δ, a de Bruijn list of optional types T,
    - F, the future, a set of points X with a rest, "everything above u"
      or "everything", and the ⊥ flag. There are no future variables
      (entry 14b of docs/redesign/pending.md).

    Every fact the judgment reads comes from Γ ⊢ₛ x ≺ y ([slt]), the least
    transitive relation over the order of W, the facts of the
    hypotheses and u ≺ φ. Aging ([tage]) and subtyping ([tsub]) are the
    cost relations of static/CostTyping.v, restated over types, and the
    capture of E-Abs is aging. Credits sit on ends and closures only, so
    both recurse through products, sums and existentials. *)

From GV Require Export types.Contractive.

(** ** Environments *)

Record tentry := TE { te_sty : sty; te_pt : point; te_cr : fuel; te_tk : fuel }.

Abbreviation tenv := (gmap cend tentry).

(** cr(Θ) ≤ N on the map: every credit of Θ is at most N. *)
Definition cr_le (Θ : tenv) (N : fuel) : Prop := ∀ o te, Θ !! o = Some te → fle (te_cr te) N.

(** Every credit of Θ is at most the tickets of its end. *)
Definition cr_tk (Θ : tenv) : Prop := ∀ o te, Θ !! o = Some te → fle (te_cr te) (te_tk te).
Abbreviation lenv := (list (option ty)).

(** Θ = Θ1 ⊎ Θ2. Ends are never shared. *)
Definition tsplit (Θ Θ1 Θ2 : tenv) : Prop := Θ1 ##ₘ Θ2 ∧ Θ = Θ1 ∪ Θ2.

(** heads(c : S@x) = {x‾}. *)
Definition tenv_heads (Θ : tenv) : gset point :=
  ⋃ ((λ oe : cend * tentry, {[(te_pt oe.2)‾]}) <$> map_to_list Θ).

Lemma elem_of_tenv_heads Θ y : y ∈ tenv_heads Θ ↔ ∃ o e, Θ !! o = Some e ∧ y = (te_pt e)‾.
Proof.
  unfold tenv_heads. rewrite elem_of_union_list. split.
  - intros (X & HX & Hy). apply list_elem_of_fmap in HX as ([o e] & -> & Hoe).
    apply elem_of_map_to_list in Hoe. apply elem_of_singleton in Hy. eauto.
  - intros (o & e & Hoe & ->). exists {[(te_pt e)‾]}. split; [|set_solver].
    apply list_elem_of_fmap. exists (o, e). split; [done|]. by apply elem_of_map_to_list.
Qed.

(** x holds σ, and every other entry is absent or unlimited. *)
Definition lenv_only (Δ : lenv) (x : nat) (σ : ty) : Prop :=
  Δ !! x = Some (Some σ) ∧ ∀ y σ', y ≠ x → Δ !! y = Some (Some σ') → unlimited σ'.

Inductive lenv_split : lenv → lenv → lenv → Prop :=
  | lsplit_nil : lenv_split [] [] []
  | lsplit_none Δ Δ1 Δ2 :
      lenv_split Δ Δ1 Δ2 → lenv_split (None :: Δ) (None :: Δ1) (None :: Δ2)
  | lsplit_l σ Δ Δ1 Δ2 :
      lenv_split Δ Δ1 Δ2 → lenv_split (Some σ :: Δ) (Some σ :: Δ1) (None :: Δ2)
  | lsplit_r σ Δ Δ1 Δ2 :
      lenv_split Δ Δ1 Δ2 → lenv_split (Some σ :: Δ) (None :: Δ1) (Some σ :: Δ2)
  | lsplit_unl U Δ Δ1 Δ2 :
      unlimited U → lenv_split Δ Δ1 Δ2 →
      lenv_split (Some U :: Δ) (Some U :: Δ1) (Some U :: Δ2).

Inductive lenv_wk : lenv → lenv → Prop :=
  | lwk_nil : lenv_wk [] []
  | lwk_cons o Δ' Δ : lenv_wk Δ' Δ → lenv_wk (o :: Δ') (o :: Δ)
  | lwk_drop U Δ' Δ : unlimited U → lenv_wk Δ' Δ → lenv_wk (None :: Δ') (Some U :: Δ).

Definition lenv_unl (Δ : lenv) : Prop :=
  ∀ o, o ∈ Δ → o = None ∨ ∃ U, o = Some U ∧ unlimited U.

Fixpoint lenv_heads (Δ : lenv) : gset point :=
  match Δ with
  | [] => ∅
  | None :: Δ' => lenv_heads Δ'
  | Some T :: Δ' => heads T ∪ lenv_heads Δ'
  end.

Fixpoint lenv_bot (Δ : lenv) : bool :=
  match Δ with
  | [] => false
  | None :: Δ' => lenv_bot Δ'
  | Some T :: Δ' => hbot T || lenv_bot Δ'
  end.

(** The process interface Σ and its entries at credit and tickets a. *)
Abbreviation senv := (gmap cend (sty * point)).

Definition tenv_of (a : fuel) (Σ : senv) : tenv := (λ e, TE e.1 e.2 a a) <$> Σ.

(** ** Futures and hypotheses *)

(** The unknown rest of a future: everything above u, the future of a
    body below the upper point u ([RAbove]), or everything, the future
    of a body with no upper point ([RAll]). *)
Inductive frest := RAbove (u : point) | RAll.

(** A rest, or the ⊥ flag with or without a rest. *)
Inductive futrest := FRest (r : frest) | FBot (o : option frest).

Abbreviation sfuture := (gset point * option futrest)%type.
Abbreviation hyps := (list (bcs * list point)).

Definition fs_var (o : option futrest) : option frest :=
  match o with Some (FRest r) => Some r | Some (FBot o') => o' | None => None end.

Definition fs_bot (o : option futrest) : bool :=
  match o with Some (FBot _) => true | _ => false end.

Definition sf_unionb (F : sfuture) (X : gset point) (b : bool) : sfuture :=
  if b then (F.1 ∪ X, Some (FBot (fs_var F.2))) else (F.1 ∪ X, F.2).

(** Γ, the facts of the box constraints in force (A.5). *)
Record hctx := HCtx { hc_hyps : hyps }.

Definition hc_empty : hctx := HCtx [].

Definition hyp_fact (Ψ : hyps) (g : fact) : Prop :=
  ∃ C xs, (C, xs) ∈ Ψ ∧ bcs_at C xs g.

(** Γ ⊢ₛ x ≺ y. Program order comes with the order of W. *)
Inductive fl (W : sworld) (Γ : hctx) : point → point → Prop :=
  | fl_w x y : W ⊢ₛ x ≺ y → fl W Γ x y
  | fl_h x y : hyp_fact (hc_hyps Γ) (FLt x y) → fl W Γ x y
  | fl_trans x y z : fl W Γ x y → fl W Γ y z → fl W Γ x z.

Definition slt (W : sworld) (Γ : hctx) (x y : point) : Prop := fl W Γ x y.
Definition sle (W : sworld) (Γ : hctx) (x y : point) : Prop := x = y ∨ slt W Γ x y.

Lemma sl_w W Γ x y : W ⊢ₛ x ≺ y → slt W Γ x y.
Proof. apply fl_w. Qed.
Lemma sl_trans W Γ x y z : slt W Γ x y → slt W Γ y z → slt W Γ x z.
Proof. apply fl_trans. Qed.
Lemma sl_po W Γ x : slt W Γ x x⁺.
Proof. apply sl_w, sw_lt_po. Qed.
(** C holds at the instance xs. *)
Definition hold_at (W : sworld) (Γ : hctx) (C : bcs) (xs : list point) : Prop :=
  ∀ x y, bcs_at C xs (FLt x y) → slt W Γ x y.

(** x ≺ r for a rest: x ≺ "everything above u" iff x ≼ u (entry 14b,
    docs/redesign/check-future-variables.md), and nothing lies below
    "everything". *)
Definition rest_below (W : sworld) (Γ : hctx) (x : point) (r : frest) : Prop :=
  match r with RAbove u => sle W Γ x u | RAll => False end.

(** {u} ≺ F, for the points of F and its rest. *)
Definition ub_below_s (W : sworld) (Γ : hctx) (ub : option point) (F : sfuture) : Prop :=
  match ub with
  | None => True
  | Some x => (∀ y, y ∈ F.1 → slt W Γ x y) ∧
              (∀ r, fs_var F.2 = Some r → rest_below W Γ x r) ∧
              fs_bot F.2 = false
  end.

(** u ≺ F for the upper point of an arrow (entry 12, generalized arrows).
    No upper point asks nothing, ⊤ asks the empty future. *)
Definition ub_below_u (W : sworld) (Γ : hctx) (ub : ubound) (F : sfuture) : Prop :=
  match ub with
  | UNone => True
  | UPt x => ub_below_s W Γ (Some x) F
  | UTop => F = (∅, None)
  end.


Definition lbx_below_h (W : sworld) (Γ : hctx) (lb : lbound) (H : gset point) (b : bool) : Prop :=
  match lb with
  | LBot => True
  | LNone => H = ∅ ∧ b = false
  | LPt x => (∀ y, y ∈ H → sle W Γ x y) ∧ b = false
  end.


(** ** Point instantiation of contexts *)

Definition hyps_inst (σ : nat → point) (Ψ : hyps) : hyps :=
  (λ g : bcs * list point, (bcs_inst σ g.1, pt_inst σ <$> g.2)) <$> Ψ.

Definition ids (m : nat) : list point := pvar <$> seq 0 m.

(** The context of a body under m new point variables with the
    constraint C, the box of E-Box and the existential of E-Open. *)
Definition hc_open (m : nat) (C : bcs) (Γ : hctx) : hctx :=
  HCtx (hyps_inst (pshift m) (hc_hyps Γ) ++ [(bcs_inst (pshift m) C, ids m)]).

(** Well-formed existential types (finding 6.3 of
    docs/redesign/algorithmic-plan.md). The lower bound l of ∃^l ιs. C. T
    lies below the points of T under C: l ≼ ap(T) at the m new point
    variables. A static condition on the type, read where E-Pack forms
    it. *)
Definition ex_wf (W : sworld) (Γ : hctx) (lb : lbound) (m : nat) (C : bcs) (T : ty) : Prop :=
  lbx_below_h W (hc_open m C Γ) (lb_map (pt_inst (pshift m)) lb) (heads T) (hbot T).

(** Conservativity of an opening. The constraint C under m new point
    variables derives no new fact between points of Γ: a fact between
    two shifted outer points in [hc_open m C Γ] holds in Γ already
    (docs/redesign/check-flag-rejection.md, fix (c)). *)
Definition cons_open (W : sworld) (Γ : hctx) (m : nat) (C : bcs) : Prop :=
  ∀ x y, slt W (hc_open m C Γ) (pt_inst (pshift m) x) (pt_inst (pshift m) y) → slt W Γ x y.

(** ** The constraint of a creation at a fresh root (wf-new)

    The constraint C of E-New at a fresh root speaks of the bound point
    variable 0, the new root ρ, and of the points of its environment.
    Every fact of C ends in the tree of ρ, so a context point lies only
    below new points, and C with program order is well-founded on the
    tree of ρ. The premise reads no semantics. *)
Definition in_tree0 (x : point) : Prop := pt_root x = NVar 0.

Definition new_step (C : bcs) (x y : point) : Prop :=
  in_tree0 x ∧ in_tree0 y ∧
  ((bc_facts C (FLt x y) ∧ fact_scoped (1 + length (bc_env C)) (FLt x y)) ∨ y = x⁺ ∨ y = x‾⁺).

Definition wf_new (C : bcs) : Prop :=
  (∀ x y, bc_facts C (FLt x y) → fact_scoped (1 + length (bc_env C)) (FLt x y) → in_tree0 y) ∧
  well_founded (new_step C).

(** ** The most general constraint of a creation (gen-new₁)

    docs/redesign/check-general-new.md, section 6, and (wf-new⁺) of
    check-layers-open.md. A fact of C may also end at a context point,
    an exit u ≺ y. A relation S pairs points of the tree of ρ with points
    of Γ, so that each exit has a partner below y, partners descend along
    C with program order, and each fact z ≺ s into a paired point lies
    below its partner. Facts between two context points follow from Γ.
    A context point is the instance [ctx_pt] of a variable 1 + j of C at
    the j-th point of its environment. The premise reads [slt], the facts
    of C and program order, and names no rank. *)
Definition ctx_pt (C : bcs) (x : point) : point := pt_inst (plist (pvar 0 :: bc_env C)) x.

Definition cfact (C : bcs) (x y : point) : Prop :=
  bc_facts C (FLt x y) ∧ fact_scoped (1 + length (bc_env C)) (FLt x y).

Definition gen_new_rel (W : sworld) (Γ : hctx) (C : bcs) (Sr : point → point → Prop) : Prop :=
  (∀ u y, cfact C u y → in_tree0 u → ¬ in_tree0 y → ∃ t, Sr u t ∧ slt W Γ t (ctx_pt C y)) ∧
  (∀ s t s', Sr s t → new_step C s' s → ∃ t', Sr s' t' ∧ slt W Γ t' t) ∧
  (∀ s t z, Sr s t → cfact C z s → ¬ in_tree0 z → slt W Γ (ctx_pt C z) t).

Definition gen_new (W : sworld) (Γ : hctx) (C : bcs) : Prop :=
  well_founded (new_step C) ∧
  (∀ x y, cfact C x y → ¬ in_tree0 x → ¬ in_tree0 y → slt W Γ (ctx_pt C x) (ctx_pt C y)) ∧
  ∃ Sr, gen_new_rel W Γ C Sr.

(** (wf-new⁺): the partners come from a map h on the points D below an
    exit, and no fact joins two context points. *)
Definition wf_new_plus (W : sworld) (Γ : hctx) (C : bcs) : Prop :=
  well_founded (new_step C) ∧
  (∀ x y, cfact C x y → in_tree0 x ∨ in_tree0 y) ∧
  ∃ (D : point → Prop) (h : point → point),
    (∀ s s', D s → new_step C s' s → D s') ∧
    (∀ u y, cfact C u y → in_tree0 u → ¬ in_tree0 y → D u ∧ slt W Γ (h u) (ctx_pt C y)) ∧
    (∀ s s', D s → new_step C s' s → slt W Γ (h s') (h s)) ∧
    (∀ u z, D u → cfact C z u → ¬ in_tree0 z → slt W Γ (ctx_pt C z) (h u)).

Lemma wf_new_plus_gen W Γ C : wf_new_plus W Γ C → gen_new W Γ C.
Proof.
  intros (Hwf & Hin & D & h & HD & Hx & Hs & He). split_and!; [done| |].
  - intros x y Hf Hx' Hy'. by destruct (Hin x y Hf).
  - exists (λ u t, D u ∧ t = h u). split_and!.
    + intros u y Hf Hu Hy. destruct (Hx u y Hf Hu Hy) as [HDu Hlt]. eauto.
    + intros s t s' [HDs ->] Hst. exists (h s'). split; [split; [by eapply HD|done]|]. by apply Hs.
    + intros s t z [HDs ->] Hf Hz. by apply He.
Qed.

Lemma wf_new_gen W Γ C : wf_new C → gen_new W Γ C.
Proof.
  intros [HC Hwf]. apply wf_new_plus_gen. split_and!; [done| |].
  - intros x y [Hf Hs]. right. by apply (HC x y).
  - exists (λ _, False), id. split_and!; try done.
    intros u y [Hf Hs] _ Hy. exfalso. by apply Hy, (HC u y).
Qed.

(** The rest above an optional upper point. *)
Definition rest_of (ub : option point) : frest :=
  match ub with Some u => RAbove u | None => RAll end.

(** The future of the body of E-Abs and E-Box. Below a point the body
    runs under everything above it, with no upper point under
    everything, and below ⊤ under the empty future. *)
Definition abs_fut (ub : ubound) : sfuture :=
  match ub with
  | UNone => (∅, Some (FRest RAll))
  | UPt u => (∅, Some (FRest (RAbove u)))
  | UTop => (∅, None)
  end.

Lemma abs_fut_of o : abs_fut (ubound_of o) = (∅, Some (FRest (rest_of o))).
Proof. by destruct o. Qed.


Definition tentry_pinst (σ : nat → point) (e : tentry) : tentry :=
  TE (pinst_sty σ (te_sty e)) (pt_inst σ (te_pt e)) (te_cr e) (te_tk e).

Definition tenv_pinst (σ : nat → point) (Θ : tenv) : tenv := tentry_pinst σ <$> Θ.

Definition lenv_pinst (σ : nat → point) (Δ : lenv) : lenv :=
  fmap (M:=option) (pinst_ty σ) <$> Δ.

Definition frest_pinst (σ : nat → point) (r : frest) : frest :=
  match r with RAbove u => RAbove (pt_inst σ u) | RAll => RAll end.

Definition futrest_pinst (σ : nat → point) (o : futrest) : futrest :=
  match o with FRest r => FRest (frest_pinst σ r) | FBot o' => FBot (frest_pinst σ <$> o') end.

Definition sf_pinst (σ : nat → point) (F : sfuture) : sfuture :=
  (set_map (pt_inst σ) F.1, futrest_pinst σ <$> F.2).

(** ** Aging Γ − c

    An entry that holds no end stays. An end and a closure cover c by
    their credit and lose c. An idle end loses c truncated at 0 and need
    not cover c. A product, a sum and an existential age their parts. *)
Inductive tage (c : fuel) : ty → ty → Prop :=
  | age_free T : tfree T → tage c T T
  | age_sess S x a mt : fle c a → tage c (TSess S x a mt) (TSess S x (fsub a c) mt)
  | age_idle S x a mt : idle S → tage c (TSess S x a mt) (TSess S x (fsub a c) mt)
  | age_arr ub lb c0 T U a : fle c a →
      tage c (TLolli ub lb c0 T U a) (TLolli ub lb c0 T U (fsub a c))
  | age_prod T1 T2 T1' T2' : tage c T1 T1' → tage c T2 T2' → tage c (TProd T1 T2) (TProd T1' T2')
  | age_sum T1 T2 T1' T2' : tage c T1 T1' → tage c T2 T2' → tage c (TSum T1 T2) (TSum T1' T2')
  | age_ex lb n C T T' : tage c T T' → tage c (TEx lb n C T) (TEx lb n C T').

Inductive lage (c : fuel) : lenv → lenv → Prop :=
  | lage_nil : lage c [] []
  | lage_none Δ Δ' : lage c Δ Δ' → lage c (None :: Δ) (None :: Δ')
  | lage_some σ σ' Δ Δ' : tage c σ σ' → lage c Δ Δ' → lage c (Some σ :: Δ) (Some σ' :: Δ').

Definition thage (c : fuel) (Θ Θ' : tenv) : Prop :=
  ∀ o, match Θ !! o, Θ' !! o with
       | None, None => True
       | Some e, Some e' => te_sty e' = te_sty e ∧ te_pt e' = te_pt e ∧ te_tk e' = te_tk e ∧
                            fle c (te_cr e) ∧ te_cr e' = fsub (te_cr e) c
       | _, _ => False
       end.

(** ** Capture at E-Abs is aging

    A closure at credit a captures its context aged by a, each end at its
    own credit minus a (decision of 2026-11-20, per-end capture,
    docs/redesign/check-per-end-capture.md). E-Abs reads [thage] and
    [lage] at a, and no floor is left. *)

(** ** Subtyping

    W ; Γ ⊢ T ≤ T'. Costs are covariant, arguments contravariant,
    results covariant, sessions up to ≈. A credit may fall. At an arrow
    the credit a bounds what the captured counters may lose before a
    call, so it may fall as well (a' ≤ a). A
    product, a sum and an existential compare their parts. An
    existential may weaken its constraint to one that Γ and the
    constraint entail at the bound points (item 2 of 2026-11-21,
    finding 6.7 of docs/redesign/algorithmic-plan.md), so
    e : ∃ιs. C. T types at ∃ιs. C'. T whenever let x = e in x does with
    the same lower bound. The bodies of the two existentials compare
    under Γ extended by C. A box with session variables may change its
    result up to ≈ when both results are contractive, because
    contractive instances keep ≈ ([teq_sinst]). *)
Inductive tsub (W : sworld) : hctx → ty → ty → Prop :=
  | sub_unit Γ : tsub W Γ TUnit TUnit
  | sub_arr Γ ub lb c T1 U a c' T1' U' a' :
      fle c c' → fle a' a →
      tsub W Γ T1' T1 → tsub W Γ U U' →
      tsub W Γ (TLolli ub lb c T1 U a) (TLolli ub lb c' T1' U' a')
  | sub_prod Γ T1 U T1' U' : tsub W Γ T1 T1' → tsub W Γ U U' → tsub W Γ (TProd T1 U) (TProd T1' U')
  | sub_sum Γ T1 U T1' U' : tsub W Γ T1 T1' → tsub W Γ U U' → tsub W Γ (TSum T1 U) (TSum T1' U')
  | sub_box Γ n k C ub c U U' c' :
      fle c c' →
      (match k with 0 => teq U U' | S _ => U = U' ∨ (teq U U' ∧ tcontr U ∧ tcontr U') end) →
      tsub W Γ (TBox n k C ub c U) (TBox n k C ub c' U')
  | sub_sess Γ s s' x a a' mt :
      sequiv s s' → fle a' a → tsub W Γ (TSess s x a mt) (TSess s' x a' mt)
  | sub_ex Γ lb n C C' T T' :
      hold_at W (hc_open n C Γ) (bcs_inst (pshift n) C') (ids n) →
      tsub W (hc_open n C Γ) T T' → tsub W Γ (TEx lb n C T) (TEx lb n C' T').

(** ** Instances of session variables

    At N = ∞ a box body and a force see only session types with the
    annotations of N = ∞, because a derivation at N = ∞ never meets
    another one. *)
Definition sinsts (N : fuel) (ss : list sty) : Prop :=
  (Forall contractive ss ∧ Forall sscoped ss) ∧ (N = None → Forall (λ s, sty_df s = s) ss).

(** ** The annotations of N = ∞ on contexts *)

Definition tentry_df (e : tentry) : tentry := TE (sty_df (te_sty e)) (te_pt e) None None.
Definition tenv_df (Θ : tenv) : tenv := tentry_df <$> Θ.
Definition lenv_df (Δ : lenv) : lenv := fmap (M:=option) ty_df <$> Δ.
