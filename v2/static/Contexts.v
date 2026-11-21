(** * Contexts, futures, the fact theory and the cost relations (stage S2)

    The judgment Θ ; Γ ; Δ ⊢^F_{W,N} e : T ▷ c reads

    - Θ : end ⇀ (S@x)^a_m, one entry per end, with the credit and the
      tickets of the end,
    - Γ, the facts: box constraints in force with their instances,
    - Δ, a de Bruijn list of optional types T,
    - F, the future, a set of points X with a rest, "everything above u"
      or "everything", and the ⊥ flag. There are no future variables
      (entry 14b of docs/redesign/pending.md).

    Every fact the judgment reads comes from Γ ⊢ x ≺ y ([slt]), the least
    transitive relation over the order of W, the facts of the
    hypotheses and u ≺ φ. Aging ([tage]) and subtyping ([tsub]) are the
    cost relations of static/CostTyping.v, restated over types, and the
    capture of E-Abs is aging. Credits sit on ends and closures only, so
    both recurse through products, sums and existentials. *)

From GV Require Export types.Types.

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

(** Γ ⊢ x ≺ y. Program order comes with the order of W. *)
Inductive fl (W : world) (Γ : hctx) : point → point → Prop :=
  | fl_w x y : W ⊢ x ≺ y → fl W Γ x y
  | fl_h x y : hyp_fact (hc_hyps Γ) (FLt x y) → fl W Γ x y
  | fl_trans x y z : fl W Γ x y → fl W Γ y z → fl W Γ x z.

Definition slt (W : world) (Γ : hctx) (x y : point) : Prop := fl W Γ x y.
Definition sle (W : world) (Γ : hctx) (x y : point) : Prop := x = y ∨ slt W Γ x y.

Lemma sl_w W Γ x y : W ⊢ x ≺ y → slt W Γ x y.
Proof. apply fl_w. Qed.
Lemma sl_trans W Γ x y z : slt W Γ x y → slt W Γ y z → slt W Γ x z.
Proof. apply fl_trans. Qed.
Lemma sl_po W Γ x : slt W Γ x x⁺.
Proof. apply sl_w, w_lt_po. Qed.
(** C holds at the instance xs. *)
Definition hold_at (W : world) (Γ : hctx) (C : bcs) (xs : list point) : Prop :=
  ∀ x y, bcs_at C xs (FLt x y) → slt W Γ x y.

(** x ≺ r for a rest: x ≺ "everything above u" iff x ≼ u (entry 14b,
    docs/redesign/check-future-variables.md), and nothing lies below
    "everything". *)
Definition rest_below (W : world) (Γ : hctx) (x : point) (r : frest) : Prop :=
  match r with RAbove u => sle W Γ x u | RAll => False end.

(** {u} ≺ F, for the points of F and its rest. *)
Definition ub_below_s (W : world) (Γ : hctx) (ub : option point) (F : sfuture) : Prop :=
  match ub with
  | None => True
  | Some x => (∀ y, y ∈ F.1 → slt W Γ x y) ∧
              (∀ r, fs_var F.2 = Some r → rest_below W Γ x r) ∧
              fs_bot F.2 = false
  end.

(** u ≺ F for the upper point of an arrow (entry 12, generalized arrows).
    No upper point asks nothing, ⊤ asks the empty future. *)
Definition ub_below_u (W : world) (Γ : hctx) (ub : ubound) (F : sfuture) : Prop :=
  match ub with
  | UNone => True
  | UPt x => ub_below_s W Γ (Some x) F
  | UTop => F = (∅, None)
  end.


Definition lbx_below_h (W : world) (Γ : hctx) (lb : lbound) (H : gset point) (b : bool) : Prop :=
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

(** Conservativity of an opening. The constraint C under m new point
    variables derives no new fact between points of Γ: a fact between
    two shifted outer points in [hc_open m C Γ] holds in Γ already
    (docs/redesign/check-flag-rejection.md, fix (c)). *)
Definition cons_open (W : world) (Γ : hctx) (m : nat) (C : bcs) : Prop :=
  ∀ x y, slt W (hc_open m C Γ) (pt_inst (pshift m) x) (pt_inst (pshift m) y) → slt W Γ x y.

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

    Costs are covariant, arguments contravariant,
    results covariant, sessions up to ≈. A credit may fall. At an arrow
    the credit a bounds what the captured counters may lose before a
    call, so it may fall as well (a' ≤ a). A
    product, a sum and an existential compare their parts. An
    existential may drop facts of its constraint. *)
Inductive tsub : ty → ty → Prop :=
  | sub_unit : tsub TUnit TUnit
  | sub_arr ub lb c T1 U a c' T1' U' a' :
      fle c c' → fle a' a →
      tsub T1' T1 → tsub U U' →
      tsub (TLolli ub lb c T1 U a) (TLolli ub lb c' T1' U' a')
  | sub_prod T1 U T1' U' : tsub T1 T1' → tsub U U' → tsub (TProd T1 U) (TProd T1' U')
  | sub_sum T1 U T1' U' : tsub T1 T1' → tsub U U' → tsub (TSum T1 U) (TSum T1' U')
  | sub_box n k C ub c U U' c' :
      fle c c' → (match k with 0 => teq U U' | S _ => U = U' end) →
      tsub (TBox n k C ub c U) (TBox n k C ub c' U')
  | sub_sess s s' x a a' mt :
      sequiv s s' → fle a' a → tsub (TSess s x a mt) (TSess s' x a' mt)
  | sub_ex lb n C C' T T' :
      bc_env C = bc_env C' → (∀ g, bc_facts C' g → bc_facts C g) →
      tsub T T' → tsub (TEx lb n C T) (TEx lb n C' T').

(** ** Instances of session variables

    At N = ∞ a box body and a force see only session types with the
    annotations of N = ∞, because a derivation at N = ∞ never meets
    another one. *)
Definition sinsts (N : fuel) (ss : list sty) : Prop :=
  (Forall hcontractive ss ∧ Forall sscoped ss) ∧ (N = None → Forall (λ s, sty_df s = s) ss).

(** ** The annotations of N = ∞ on contexts *)

Definition tentry_df (e : tentry) : tentry := TE (sty_df (te_sty e)) (te_pt e) None None.
Definition tenv_df (Θ : tenv) : tenv := tentry_df <$> Θ.
Definition lenv_df (Δ : lenv) : lenv := fmap (M:=option) ty_df <$> Δ.
