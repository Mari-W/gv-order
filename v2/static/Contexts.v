(** * Contexts, futures, the fact theory and the cost relations (stage S2)

    The judgment Θ ; Γ ; Δ ⊢^F_{W,N} e : T ▷ c reads

    - Θ : end ⇀ (S@x)^a_m, one entry per end, with the credit and the
      tickets of the end,
    - Γ, the facts: box constraints in force with their instances,
    - Δ, a de Bruijn list of optional types T,
    - F, the future, a set of points X with a rest, "everything above u"
      or "everything". A hidden end makes the rest "everything". There
      are no future variables
      (entry 14b of docs/redesign/pending.md).

    Every fact the judgment reads comes from Γ ⊢ₛ x ≺ y ([slt]), the least
    transitive relation over the order of W, the facts of the
    hypotheses and u ≺ φ. Aging ([tage]) and subtyping ([tsub]) are the
    cost relations of static/CostTyping.v, restated over types, and the
    capture of E-Abs is aging. Credits sit on ends and closures only, so
    both recurse through products, sums and existentials. *)

From GV Require Export types.SessSub.

(** ** Environments *)

Record tentry := TE { te_sty : sty; te_pt : point; te_cr : fuel; te_tk : fuel }.

Abbreviation tenv := (gmap cend tentry).

(** cr(Θ) ≤ N on the map: every credit of Θ is at most N. *)
Definition cr_le (Θ : tenv) (N : fuel) : Prop := ∀ o te, Θ !! o = Some te → fle (te_cr te) N.

(** Every credit of Θ is at most the tickets of its end. Typing implies
    it ([typed_cr_tk], static/Typing.v): E-Chan asks a ≤ m of the end it
    reads, and aging ([thage]) asks it of each end it ages. *)
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

(** The context of ends that the interface annotations η give Σ. *)
Definition tenv_ofk (η : iann) (Σ : senv) : tenv :=
  map_imap (λ o e, Some (TE e.1 e.2 (η o).1 (η o).2)) Σ.

Lemma lookup_tenv_ofk η Σ o : tenv_ofk η Σ !! o = (λ e, TE e.1 e.2 (η o).1 (η o).2) <$> Σ !! o.
Proof. unfold tenv_ofk. rewrite map_lookup_imap. by destruct (Σ !! o). Qed.

Lemma dom_tenv_ofk η Σ : dom (tenv_ofk η Σ) = dom Σ.
Proof.
  apply set_eq. intros o. rewrite !elem_of_dom, lookup_tenv_ofk.
  destruct (Σ !! o); simpl; split; intros [? ?]; try done; by eexists.
Qed.

Lemma tenv_ofk_half N Σ : tenv_ofk (khalf N) Σ = tenv_of (fhalf N) Σ.
Proof. apply map_eq. intros o. rewrite lookup_tenv_ofk. unfold tenv_of. by rewrite lookup_fmap. Qed.

(** ** Futures and hypotheses *)

(** The unknown rest of a future: everything above u, the future of a
    body below the upper point u ([RAbove]), or everything, the future
    of a body with no upper point ([RAll]). *)
Inductive frest := RAbove (u : point) | RAll.

(** A future is a finite set of points and an optional rest. *)
Abbreviation sfuture := (gset point * option frest)%type.
Abbreviation hyps := (list (bcs * list point)).

(** F extended by X. A hidden end in the extension (b) makes the rest
    everything, which forbids every action. *)
Definition sf_unionb (F : sfuture) (X : gset point) (b : bool) : sfuture :=
  if b then (F.1 ∪ X, Some RAll) else (F.1 ∪ X, F.2).

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
              (∀ r, F.2 = Some r → rest_below W Γ x r)
  end.

(** x ≺ T for the payload T of a send: x lies below the dual points of
    the ends in T, and T holds no end at a hidden point. *)
Definition below_ty (W : sworld) (Γ : hctx) (x : point) (T : ty) : Prop :=
  hbot T = false ∧ ∀ y, y ∈ heads T → slt W Γ x y.

Lemma hbot_payload_at m T x : hbot (payload_at m T x) = hbot T.
Proof. unfold payload_at, ty_inst. apply hbot_pinst. Qed.

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

(** ** The bridge condition

    A constraint C under m bound point variables speaks of the variables
    0, …, m−1, the roots of a tree, and of the variable m + j, the j-th
    point of [bc_env C] outside the binder. A bridge of C from z to y
    joins two outer points, either by a fact of C or by an entry z ≺ v,
    a path of C and program order in the tree from v to u, and an exit
    u ≺ y. The bridge condition asks every bridge derived by Γ. It is
    the premise of E-Open, and with m = 1 the second half of (acyc-new)
    below. It makes an opening conservative: a fact between two outer
    points of [hc_open m C Γ] holds in Γ already ([cons_open_conservative],
    static/PointSubst.v; docs/redesign/check-flag-rejection.md, fix (c)). *)
Definition in_tree (m : nat) (x : point) : Prop := pn_vb m (pt_name x).

Definition cfact_at (m : nat) (C : bcs) (x y : point) : Prop :=
  bc_facts C (FLt x y) ∧ fact_scoped (m + length (bc_env C)) (FLt x y).

Definition tree_step (m : nat) (C : bcs) (x y : point) : Prop :=
  in_tree m x ∧ in_tree m y ∧ (cfact_at m C x y ∨ y = x⁺ ∨ y = x‾⁺).

(** The point of Γ a point of C stands for. The tree points stay. *)
Definition outer_pt (m : nat) (C : bcs) (x : point) : point := pt_inst (plist (ids m ++ bc_env C)) x.

Definition bridge_at (m : nat) (C : bcs) (z y : point) : Prop :=
  ¬ in_tree m z ∧ ¬ in_tree m y ∧
  (cfact_at m C z y ∨ ∃ v u, cfact_at m C z v ∧ in_tree m v ∧ rtc (tree_step m C) v u ∧ cfact_at m C u y).

Definition cons_open (W : sworld) (Γ : hctx) (m : nat) (C : bcs) : Prop :=
  ∀ z y, bridge_at m C z y → slt W Γ (outer_pt m C z) (outer_pt m C y).

(** Conservativity, the declarative form of the bridge condition. A fact
    between two points outside the tree of the m bound variables that
    [hc_open m C Γ] derives, Γ derives already. The points outside the
    tree are the shifted points of Γ. Under constant facts of W it is
    equivalent to [cons_open] ([cons_open_iff], static/PointSubst.v). *)
Definition conserv (W : sworld) (Γ : hctx) (m : nat) (C : bcs) : Prop :=
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

(** ** The most general constraint of a creation (gen-new)

    docs/redesign/check-general-new.md, section 4. A fact of C may also
    end at a context point, an exit u ≺ y. A relation S pairs points of
    the tree of ρ with nonempty finite sets of points of Γ, so that each
    exit has a partner set below y, each point of a partner set of a
    step below lies below some point of the partner set above, and each
    fact z ≺ s into a paired point lies below some point of its partner
    set. Facts between two context points follow from Γ.
    A context point is the instance [ctx_pt] of a variable 1 + j of C at
    the j-th point of its environment. The premise reads [slt], the facts
    of C and program order, and names no rank. *)
Definition ctx_pt (C : bcs) (x : point) : point := pt_inst (plist (pvar 0 :: bc_env C)) x.

Definition cfact (C : bcs) (x y : point) : Prop :=
  bc_facts C (FLt x y) ∧ fact_scoped (1 + length (bc_env C)) (FLt x y).

Definition gen_new_rel (W : sworld) (Γ : hctx) (C : bcs) (Sr : point → list point → Prop) : Prop :=
  (∀ s T, Sr s T → T ≠ []) ∧
  (∀ u y, cfact C u y → in_tree0 u → ¬ in_tree0 y →
     ∃ T, Sr u T ∧ ∀ t, t ∈ T → slt W Γ t (ctx_pt C y)) ∧
  (∀ s T s', Sr s T → new_step C s' s →
     ∃ T', Sr s' T' ∧ ∀ t', t' ∈ T' → ∃ t, t ∈ T ∧ slt W Γ t' t) ∧
  (∀ s T z, Sr s T → cfact C z s → ¬ in_tree0 z → ∃ t, t ∈ T ∧ slt W Γ (ctx_pt C z) t).

Definition gen_new (W : sworld) (Γ : hctx) (C : bcs) : Prop :=
  well_founded (new_step C) ∧
  (∀ x y, cfact C x y → ¬ in_tree0 x → ¬ in_tree0 y → slt W Γ (ctx_pt C x) (ctx_pt C y)) ∧
  ∃ Sr, gen_new_rel W Γ C Sr.

(** (gen-new₁): partners are single points, S a relation into points of
    Γ. It is (gen-new) with singleton sets ([gen_new1_gen]). *)
Definition gen_new1_rel (W : sworld) (Γ : hctx) (C : bcs) (Sr : point → point → Prop) : Prop :=
  (∀ u y, cfact C u y → in_tree0 u → ¬ in_tree0 y → ∃ t, Sr u t ∧ slt W Γ t (ctx_pt C y)) ∧
  (∀ s t s', Sr s t → new_step C s' s → ∃ t', Sr s' t' ∧ slt W Γ t' t) ∧
  (∀ s t z, Sr s t → cfact C z s → ¬ in_tree0 z → slt W Γ (ctx_pt C z) t).

Definition gen_new1 (W : sworld) (Γ : hctx) (C : bcs) : Prop :=
  well_founded (new_step C) ∧
  (∀ x y, cfact C x y → ¬ in_tree0 x → ¬ in_tree0 y → slt W Γ (ctx_pt C x) (ctx_pt C y)) ∧
  ∃ Sr, gen_new1_rel W Γ C Sr.

Lemma gen_new1_gen W Γ C : gen_new1 W Γ C → gen_new W Γ C.
Proof.
  intros (Hwf & Hcc & Sr & Hex & Hst & Hen). split_and!; [done|done|].
  exists (λ s T, ∃ t, Sr s t ∧ T = [t]). split_and!.
  - by intros s T (t & _ & ->).
  - intros u y Hf Hu Hy. destruct (Hex u y Hf Hu Hy) as (t & Ht & Hlt).
    exists [t]. split; [eauto|]. intros t' ->%list_elem_of_singleton. done.
  - intros s T s' (t & Ht & ->) Hs. destruct (Hst s t s' Ht Hs) as (t' & Ht' & Hlt).
    exists [t']. split; [eauto|]. intros t'' ->%list_elem_of_singleton. exists t. split; [by apply list_elem_of_singleton|done].
  - intros s T z (t & Ht & ->) Hf Hz. exists t. split; [by apply list_elem_of_singleton|]. by apply (Hen s t z).
Qed.

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

Lemma wf_new_plus_gen1 W Γ C : wf_new_plus W Γ C → gen_new1 W Γ C.
Proof.
  intros (Hwf & Hin & D & h & HD & Hx & Hs & He). split_and!; [done| |].
  - intros x y Hf Hx' Hy'. by destruct (Hin x y Hf).
  - exists (λ u t, D u ∧ t = h u). split_and!.
    + intros u y Hf Hu Hy. destruct (Hx u y Hf Hu Hy) as [HDu Hlt]. eauto.
    + intros s t s' [HDs ->] Hst. exists (h s'). split; [split; [by eapply HD|done]|]. by apply Hs.
    + intros s t z [HDs ->] Hf Hz. by apply He.
Qed.

Lemma wf_new_plus_gen W Γ C : wf_new_plus W Γ C → gen_new W Γ C.
Proof. intros H. by apply gen_new1_gen, wf_new_plus_gen1. Qed.

Lemma wf_new_gen W Γ C : wf_new C → gen_new W Γ C.
Proof.
  intros [HC Hwf]. apply wf_new_plus_gen. split_and!; [done| |].
  - intros x y [Hf Hs]. right. by apply (HC x y).
  - exists (λ _, False), id. split_and!; try done.
    intros u y [Hf Hs] _ Hy. exfalso. by apply Hy, (HC u y).
Qed.

(** ** The acyclic constraint of a creation (acyc-new)

    docs/redesign/check-df-acyclic.md, section 2.2. A bridge of C from
    z to y joins two context points, either by a fact of C or by an
    entry z ≺ v, a path of C and program order in the tree of ρ from v
    to u, and an exit u ≺ y. (acyc-new) asks C with program order
    acyclic on the tree of ρ and every bridge derived by Γ. Like
    (gen-new) it reads [slt], the facts of C and program order. It names
    no rank, no partner set and no finite set. *)
Definition cbridge (C : bcs) (z y : point) : Prop :=
  ¬ in_tree0 z ∧ ¬ in_tree0 y ∧
  (cfact C z y ∨ ∃ v u, cfact C z v ∧ in_tree0 v ∧ rtc (new_step C) v u ∧ cfact C u y).

Definition tree_acyclic (C : bcs) : Prop := ∀ x, in_tree0 x → ¬ tc (new_step C) x x.

Definition acyc_new (W : sworld) (Γ : hctx) (C : bcs) : Prop :=
  tree_acyclic C ∧ cons_open W Γ 1 C.

(** At one root the bridges of [bridge_at] are those of [cbridge]. *)
Lemma in_tree_1 x : in_tree 1 x ↔ in_tree0 x.
Proof.
  unfold in_tree, in_tree0, pt_root. rewrite pn_vb_root. split.
  - intros (a & -> & Ha). f_equal. lia.
  - intros ->. eexists. split; [done|lia].
Qed.

Lemma tree_step_1 C x y : tree_step 1 C x y ↔ new_step C x y.
Proof. unfold tree_step, new_step, cfact_at. by rewrite !in_tree_1. Qed.

Lemma rtc_tree_step_1 C x y : rtc (tree_step 1 C) x y ↔ rtc (new_step C) x y.
Proof.
  split; intros H; induction H as [|x w y Hs _ IH]; try apply rtc_refl;
    (eapply rtc_l; [apply tree_step_1; exact Hs|exact IH]).
Qed.

Lemma bridge_at_1 C z y : bridge_at 1 C z y ↔ cbridge C z y.
Proof.
  unfold bridge_at, cbridge, cfact_at, cfact. setoid_rewrite in_tree_1.
  setoid_rewrite rtc_tree_step_1. done.
Qed.

Lemma cons_open_1 W Γ C :
  cons_open W Γ 1 C ↔ ∀ z y, cbridge C z y → slt W Γ (ctx_pt C z) (ctx_pt C y).
Proof.
  split; intros H z y Hb.
  - apply bridge_at_1 in Hb. exact (H z y Hb).
  - apply bridge_at_1 in Hb. exact (H z y Hb).
Qed.

(** The steps of C stay in the tree of ρ. *)
Lemma rtc_new_step_tree C v u : in_tree0 v → rtc (new_step C) v u → in_tree0 u.
Proof. intros Hv Hr. induction Hr as [|v w u (_ & Hw & _) _ IH]; [done|by apply IH]. Qed.

(** Lemma C of check-df-acyclic.md: (gen-new) implies (acyc-new),
    constructively. A well-founded relation has no cycle, and the
    partner sets of (gen-new) walk a bridge down to a fact of Γ. *)
Lemma gen_new_acyc W Γ C : gen_new W Γ C → acyc_new W Γ C.
Proof.
  intros (Hwf & Hcc & Sr & Hne & Hex & Hst & Hen). split; [|apply cons_open_1].
  - intros x _ Hx. assert (well_founded (tc (new_step C))) as Htc.
    { intros a. apply (acc_tc (new_step C)), Hwf. }
    induction (Htc x) as [x _ IH]. by apply (IH x).
  - intros z y (Hz & Hy & [Hf|(v & u & Hzv & Hv & Hvu & Huy)]); [by apply Hcc|].
    assert (in_tree0 u) as Hu by by apply (rtc_new_step_tree C v u).
    destruct (Hex u y Huy Hu Hy) as (T & HT & HTy).
    assert (∀ s, rtc (new_step C) v s → ∀ T, Sr s T →
              ∃ T0, Sr v T0 ∧ ∀ t0, t0 ∈ T0 → ∃ t, t ∈ T ∧ sle W Γ t0 t) as Hwalk.
    { clear -Hst. intros s Hs. induction Hs as [v|v v' s Hvv' _ IH]; intros T1 HT1.
      - exists T1. split; [done|]. intros t0 Ht0. exists t0. split; [done|by left].
      - destruct (IH T1 HT1) as (T2 & HT2 & H2).
        destruct (Hst v' T2 v HT2 Hvv') as (T0 & HT0 & H0). exists T0. split; [done|].
        intros t0 Ht0. destruct (H0 t0 Ht0) as (t2 & Ht2 & Hl0).
        destruct (H2 t2 Ht2) as (t & Ht & Hle). exists t. split; [done|]. right.
        destruct Hle as [<-|Hl2]; [done|by eapply sl_trans]. }
    destruct (Hwalk u Hvu T HT) as (T0 & HT0 & H0).
    destruct (Hen v T0 z HT0 Hzv Hz) as (t0 & Ht0 & Hzt0).
    destruct (H0 t0 Ht0) as (t & Ht & Hle). eapply sl_trans; [exact Hzt0|].
    destruct Hle as [<-|Hl]; [by apply HTy|]. eapply sl_trans; [exact Hl|by apply HTy].
Qed.

Lemma wf_new_acyc W Γ C : wf_new C → acyc_new W Γ C.
Proof. intros H. by apply gen_new_acyc, wf_new_gen. Qed.

(** (gen-new) is (acyc-new) plus what ranks need, C with program order
    well-founded on the tree of ρ and a partner relation. The second
    clause of (gen-new) is the bridge clause of (acyc-new) for bridges
    of length zero. *)
Lemma gen_new_iff W Γ C :
  gen_new W Γ C ↔ acyc_new W Γ C ∧ well_founded (new_step C) ∧ ∃ Sr, gen_new_rel W Γ C Sr.
Proof.
  split.
  - intros H. split; [by apply gen_new_acyc|]. destruct H as (Hwf & _ & HS). by split.
  - intros ([_ Hbr] & Hwf & HS). split_and!; [done| |done].
    intros x y Hf Hx Hy. apply (proj1 (cons_open_1 W Γ C) Hbr). split_and!; [done|done|by left].
Qed.

(** ** The mode of a judgment

    One judgment for every bound N. At N = ∞ ([None], the deadlock-free
    and live judgment) E-New asks (acyc-new) and the process rules ask
    the world acyclic. At a finite N (the lock-free judgment) E-New asks
    in addition C well-founded on the tree of ρ with a partner relation,
    which is (gen-new) ([gen_new_iff]), and the process rules ask the
    world well-founded. *)
Definition new_ok (N : fuel) (W : sworld) (Γ : hctx) (C : bcs) : Prop :=
  acyc_new W Γ C ∧ (N ≠ None → well_founded (new_step C) ∧ ∃ Sr, gen_new_rel W Γ C Sr).

Definition wok (N : fuel) (W : sworld) : Prop :=
  match N with None => sacyc W | Some _ => swf W end.

Lemma new_ok_acyc N W Γ C : new_ok N W Γ C → acyc_new W Γ C.
Proof. by intros [H _]. Qed.

Lemma new_ok_gen N W Γ C : N ≠ None → new_ok N W Γ C → gen_new W Γ C.
Proof. intros HN [Ha Hr]. apply gen_new_iff. split; [done|by apply Hr]. Qed.

Lemma acyc_new_ok W Γ C : acyc_new W Γ C → new_ok None W Γ C.
Proof. intros H. split; [done|by intros []]. Qed.

Lemma gen_new_ok N W Γ C : gen_new W Γ C → new_ok N W Γ C.
Proof. intros (Ha & Hwf & HS)%gen_new_iff. split; [done|by intros _]. Qed.

Lemma wok_acyc N W : wok N W → sacyc W.
Proof. destruct N; [apply swf_sacyc|done]. Qed.

Lemma swf_wok N W : swf W → wok N W.
Proof. destruct N; [done|apply swf_sacyc]. Qed.

(** A well-founded world meets the mode premise at every N. The examples
    prove well-foundedness by a measure and use this wrapper. *)
Lemma swf_ok_wok N W : sworld_wf W ∧ swf W → sworld_wf W ∧ wok N W.
Proof. intros [H1 H2]. split; [done|by apply swf_wok]. Qed.

Lemma sw_empty_wok N : sworld_wf sw_empty ∧ wok N sw_empty.
Proof. apply swf_ok_wok, sw_empty_ok. Qed.

(** The rest above an optional upper point. *)
Definition rest_of (ub : option point) : frest :=
  match ub with Some u => RAbove u | None => RAll end.

(** The future of the body of E-Abs and E-Box. Below a point the body
    runs under everything above it, with no upper point under
    everything, and below ⊤ under the empty future. *)
Definition abs_fut (ub : ubound) : sfuture :=
  match ub with
  | UNone => (∅, Some RAll)
  | UPt u => (∅, Some (RAbove u))
  | UTop => (∅, None)
  end.

Lemma abs_fut_of o : abs_fut (ubound_of o) = (∅, Some (rest_of o)).
Proof. by destruct o. Qed.


Definition tentry_pinst (σ : nat → point) (e : tentry) : tentry :=
  TE (pinst_sty σ (te_sty e)) (pt_inst σ (te_pt e)) (te_cr e) (te_tk e).

Definition tenv_pinst (σ : nat → point) (Θ : tenv) : tenv := tentry_pinst σ <$> Θ.

Definition lenv_pinst (σ : nat → point) (Δ : lenv) : lenv :=
  fmap (M:=option) (pinst_ty σ) <$> Δ.

Definition frest_pinst (σ : nat → point) (r : frest) : frest :=
  match r with RAbove u => RAbove (pt_inst σ u) | RAll => RAll end.

Definition sf_pinst (σ : nat → point) (F : sfuture) : sfuture :=
  (set_map (pt_inst σ) F.1, frest_pinst σ <$> F.2).

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

(** Aging a context of ends Θ − c. An end covers c by its credit and
    loses c. An idle end loses c truncated at 0 and need not cover c, as
    in [age_idle]. Every end, idle or not, keeps its credit at most its
    tickets, which [cr_tk] reads. *)
Definition thage (c : fuel) (Θ Θ' : tenv) : Prop :=
  ∀ o, match Θ !! o, Θ' !! o with
       | None, None => True
       | Some e, Some e' => te_sty e' = te_sty e ∧ te_pt e' = te_pt e ∧ te_tk e' = te_tk e ∧
                            (fle c (te_cr e) ∨ idle (te_sty e)) ∧ te_cr e' = fsub (te_cr e) c ∧
                            fle (te_cr e) (te_tk e)
       | _, _ => False
       end.

(** ** Capture at E-Abs is aging

    A closure at credit a captures its context aged by a, each end at its
    own credit minus a (decision of 2026-11-20, per-end capture,
    docs/redesign/check-per-end-capture.md). E-Abs reads [thage] and
    [lage] at a, and no floor is left. *)

(** ** Subtyping

    W ; Γ ⊢ T ≤ T'. Costs are covariant, arguments contravariant,
    results covariant. Sessions compare by ⊑ ([ssub]), which is ≈ except
    that a received payload may fall in credit and a sent payload may
    rise. A credit may fall. At an arrow
    the credit a bounds what the captured counters may lose before a
    call, so it may fall as well (a' ≤ a). A
    product, a sum and an existential compare their parts. An
    existential may weaken its constraint to one that Γ and the
    constraint entail at the bound points (item 2 of 2026-11-21,
    finding 6.7 of docs/redesign/algorithmic-plan.md). The lower bound
    may stay, or fall to any l′ that Γ and C place below the heads of
    the body ([lb_lower]), as E-Pack would after an opening (item 1 of
    2026-11-22). So e : ∃ιs. C. T types at ∃^{l′}ιs. C'. T whenever
    let x = e in x does by opening x and packing it at ιs. The bodies of
    the two existentials compare under Γ extended by C. A box with session variables may change its
    result up to ≈ when both results are contractive, because
    contractive instances keep ≈ ([teq_sinst]). *)
Definition lb_lower (W : sworld) (Γ : hctx) (n : nat) (C : bcs) (lb lb' : lbound) (T : ty) : Prop :=
  lb' = lb ∨ lbx_below_h W (hc_open n C Γ) (lb_map (pt_inst (pshift n)) lb') (heads T) (hbot T).

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
      ssub s s' → fle a' a → tsub W Γ (TSess s x a mt) (TSess s' x a' mt)
  | sub_ex Γ lb lb' n C C' T T' :
      hold_at W (hc_open n C Γ) (bcs_inst (pshift n) C') (ids n) →
      lb_lower W Γ n C lb lb' T →
      tsub W (hc_open n C Γ) T T' → tsub W Γ (TEx lb n C T) (TEx lb' n C' T').

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
