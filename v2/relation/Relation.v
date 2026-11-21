(** * The generic relation R^κ (stage S3, proposal §2.8)

    One step-indexed relation, parametric in a cost table κ, gives the
    deadlock-freedom relation (κ_DF) and the live relation (κ_L).

      v ∈ V[κ]^W _ n⟦Θ ⊢ T⟧       [Vrel κ n W Θ T v]
      e ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^F     [Erel κ n W Θ T F e]
      p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧       [Prel κ n W Σ T p]

    A step of cost c taken at level n carries its obligation at level
    n − c. A step of cost 0 is read inductively inside the level: E and
    P are least fixpoints over those steps ([Eind], [Pind]). In κ_DF the
    steps of cost 0 are send, select, close and link, which shrink the
    term, and in κ_L they are the τ steps β, new, spawn and link. The
    arrow reads its body at every level j with j + κ(β) ≤ n, so the body
    sits at n − κ(β). For κ_L that is the current level, so V at level n
    is defined together with E at level n, by fuel on the size of the
    type ([Vbody]). The step index itself is one generic course-of-values
    fixpoint ([sfix], relation/Sfix.v).

    Every unfolding of E holds in every world W1 ⊒ W, and every unfolding
    of P in every strict world W1 ⊒ W (decision Q9, and S4.16), so E and P
    are monotone in the world by definition.

    The relation reads no syntax of a term but the labels of its steps,
    and from a label only the value a send or a spawn moves. V fixes the
    ends of that value (Q14), so O-Spawn and O-Send read no transfer set,
    and Q-Send reads the ends [fends w] of the value it extrudes. Its
    environments map an end to a session type at a
    point ([senv]) and carry no credit. The relation reads no annotation
    of a type. A session type is compared after erasing its annotations
    ([seqv]), and costs, credits and tickets are never read.
    The session types of the environments keep their annotations, so the
    fuel layer of stage S6 reads each end's cost protocol from the
    environment of the live relation at the same index. *)

From GV Require Export relation.Sfix relation.CostTable relation.Readiness.

Local Set Warnings "-register-all".

(** ** Sizes of types

    The size counts the constructors outside session types. A box counts
    three, so that V of a box can read V of its thunk type ∗ ⊸ U. *)
Fixpoint tsize (T : ty) : nat :=
  match T with
  | TUnit | TSess _ _ _ _ => 1
  | TLolli _ _ _ T1 U _ | TProd T1 U | TSum T1 U => S (tsize T1 + tsize U)
  | TBox _ _ _ _ _ U => 3 + tsize U
  | TEx _ _ _ T1 => S (tsize T1)
  end.

Lemma tsize_pos T : 1 ≤ tsize T.
Proof. destruct T; simpl; lia. Qed.

Lemma tsize_pinst σ T : tsize (pinst_ty σ T) = tsize T.
Proof. induction T in σ |- *; simpl; auto. Qed.

Lemma tsize_sinst σ T : tsize (sinst_ty σ T) = tsize T.
Proof. induction T in σ |- *; simpl; auto. Qed.

(** The type of a thunk ∗ ⊸^u U, with the annotations of N = ∞, which
    the relation does not read. *)
Definition tthunk (ub : option point) (U : ty) : ty :=
  TLolli (ubound_of ub) LNone None TUnit U None.

Lemma tsize_tthunk ub U : tsize (tthunk ub U) = 2 + tsize U.
Proof. simpl. lia. Qed.

(** The thunk a box !e stands for. Applied to ∗ it unrolls once. *)
Definition thunk (e : expr) : expr := Lam (rename S (subst1 (EBox e) e)).

Lemma thunk_app w e : subst1 w (rename S (subst1 (EBox e) e)) = subst1 (EBox e) e.
Proof.
  unfold subst1 at 1. rewrite subst_rename. rewrite <-(subst_ids (subst1 _ e)) at 2.
  by apply subst_ext.
Qed.

(** ** Environments *)

(** Session types up to annotations. *)
Definition seqv (S S' : sty) : Prop := sequiv (sty_df S) (sty_df S').

(** S' is the dual of S, up to annotations. *)
Definition sdual (S S' : sty) : Prop := seqv S' (dual S).

(** The continuation of branch i. *)
Definition bsel (i : bool) (S1 S2 : sty) : sty := if i then S2 else S1.

(** The two ends of a new channel c at x and x‾. *)
Definition new_env (c : chan) (S : sty) (x : point) (Θ : senv) : senv :=
  <[EPos c := (S, x)]> (<[ENeg c := (dual S, x‾)]> Θ).

Definition cfresh (c : chan) (Θ : senv) : Prop := (EPos c ∉ dom Θ) ∧ (ENeg c ∉ dom Θ).

(** The generated root g of family ℓ is the root of no point of Θ. *)
Definition gfresh (ℓ : family) (g : nat) (Θ : senv) : Prop :=
  ∀ o S x, Θ !! o = Some (S, x) → pt_root x ≠ NGen ℓ g.

(** The environment of the relation for a typing environment. The
    credits go. *)
Definition tenv_erase (Θ : tenv) : senv := (λ e, (te_sty e, te_pt e)) <$> Θ.

(** ** Renamings and fusions of held ends (decision Q16, refined)

    A map h of ends renames an environment ([kren h Θ], the paper's
    kmap h Θ, for an h injective on the ends of Θ) and a process
    ([pmap h p], its restricted channels through [gch h]). A fusion
    renames by h and restricts the channels D, whose two ends h makes
    a dual pair of the interface ([pfuse h D p], [sdrop D Σ]). P is
    closed under every fusion that commutes with duality, is injective
    on the held ends (the ends of Σ and both ends of every restricted
    channel) and creates partner pairs only on D ([fuse_ok]). D = ∅ is
    a renaming ([pren_ok]), h = id internalizes pairs of Σ. *)

(** The channel of the image of c⁺. *)
Definition gch (g : cend → cend) (c : chan) : chan := ech (g (EPos c)).

(** g commutes with duality. *)
Definition dcomm (g : cend → cend) : Prop := ∀ o, g (edual o) = edual (g o).

Definition kren (h : cend → cend) (Θ : senv) : senv :=
  list_to_map ((λ p : cend * (sty * point), (h p.1, p.2)) <$> map_to_list Θ).

Definition pmap (h : cend → cend) (p : proc) : proc := (set_map (gch h) p.1, emapE h p.2).

(** The held ends of a process with interface Σ. *)
Definition pheld (Σ : senv) (p : proc) (o : cend) : Prop := o ∈ dom Σ ∨ ech o ∈ p.1.

(** A renaming: injective on the held ends, and no two held ends
    become partners unless they are. *)
Definition pren_ok (h : cend → cend) (Σ : senv) (p : proc) : Prop :=
  dcomm h ∧ (∀ o1 o2, pheld Σ p o1 → pheld Σ p o2 → h o1 = h o2 → o1 = o2) ∧
  (∀ o1 o2, pheld Σ p o1 → pheld Σ p o2 → h o2 = edual (h o1) → o2 = edual o1).

(** The interface without the ends of the channels D. *)
Definition sdrop (D : gset chan) (Σ : senv) : senv :=
  filter (λ oe : cend * (sty * point), ech oe.1 ∉ D) Σ.

Definition pfuse (h : cend → cend) (D : gset chan) (p : proc) : proc :=
  (set_map (gch h) p.1 ∪ D, emapE h p.2).

(** The two ends of every channel of D are a dual pair at dual points. *)
Definition dpairs (D : gset chan) (Σ : senv) : Prop :=
  ∀ o, ech o ∈ D → ∃ S x S', Σ !! o = Some (S, x) ∧ Σ !! edual o = Some (S', x‾) ∧ sdual S S'.

Definition fuse_ok (h : cend → cend) (D : gset chan) (Σ : senv) (p : proc) : Prop :=
  dcomm h ∧ (∀ o1 o2, pheld Σ p o1 → pheld Σ p o2 → h o1 = h o2 → o1 = o2) ∧
  (∀ o1 o2, pheld Σ p o1 → pheld Σ p o2 → h o2 = edual (h o1) → o2 = edual o1 ∨ ech (h o1) ∈ D) ∧
  D ## set_map (gch h) p.1 ∧ dpairs D (kren h Σ).

Lemma kren_empty (h : cend → cend) : kren h ∅ = (∅ : senv).
Proof. unfold kren. by rewrite map_to_list_empty. Qed.

Lemma kren_id_map (Θ : senv) : kren id Θ = Θ.
Proof.
  unfold kren. rewrite <-(list_to_map_to_list Θ) at 2. f_equal.
  etrans; [|apply list_fmap_id]. apply list_fmap_ext. by intros i [o v] _.
Qed.

Lemma emapE_id_map (E : gmultiset expr) : emapE id E = E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; [apply gmultiset_map_empty|].
  by rewrite emapE_disj_union, emapE_singleton, IH, emap_id.
Qed.

Lemma pmap_id (p : proc) : pmap id p = p.
Proof.
  destruct p as [C E]. unfold pmap. simpl. rewrite emapE_id_map. f_equal.
  apply set_eq. intros c. rewrite elem_of_map. unfold gch. simpl. split; [by intros (? & -> & ?)|eauto].
Qed.

Lemma sdrop_empty (Σ : senv) : sdrop ∅ Σ = Σ.
Proof. unfold sdrop. apply map_filter_id. intros i x _. simpl. set_solver. Qed.

Lemma pfuse_empty (h : cend → cend) (p : proc) : pfuse h ∅ p = pmap h p.
Proof. unfold pfuse, pmap. by rewrite (right_id_L ∅ (∪)). Qed.

Lemma fuse_ok_id (Σ : senv) (p : proc) : fuse_ok id ∅ Σ p.
Proof.
  split_and!; [done|by intros ? ? _ _|by intros ? ? _ _ ?; left|apply disjoint_empty_l|].
  intros o Ho. set_solver.
Qed.

Lemma dpairs_empty D : dpairs D ∅ → D = ∅.
Proof.
  intros H. apply set_eq. intros c. split; [|set_solver]. intros Hc.
  destruct (H (EPos c) Hc) as (S & x & S' & Hl & _). by rewrite lookup_empty in Hl.
Qed.

Lemma fuse_ok_empty h D p : fuse_ok h D ∅ p → D = ∅.
Proof. intros (_ & _ & _ & _ & H). apply dpairs_empty. by rewrite kren_empty in H. Qed.

Lemma pren_fuse_ok h Σ p : pren_ok h Σ p → fuse_ok h ∅ Σ p.
Proof.
  intros (Hd & Hi & Hp). split_and!; [done|done| |apply disjoint_empty_l|intros o Ho; set_solver].
  intros o1 o2 H1 H2 H. left. by apply Hp.
Qed.

(** ** Messages at the process level

    Q-Send. Θe holds the ends of restricted channels that leave with the
    message, and Σe the partners of those of them whose partner stays.
    Those partners join the interface, at the dual type and point. *)
Definition send_split (Σ Σe Θe : senv) : Prop :=
  (∀ o, o ∈ dom Θe → (o ∉ dom Σ) ∧ (edual o ∉ dom Σ)) ∧
  (∀ o, o ∈ dom Σe ↔ edual o ∈ dom Θe ∧ (o ∉ dom Θe)) ∧
  (∀ o S y, Θe !! o = Some (S, y) →
     ∃ S', (Σe ∪ Θe) !! edual o = Some (S', y‾) ∧ sdual S S').

(** Q-Recv. The ends Θ2 a message brings are new to the receiver, and
    those whose partner the receiver holds or receives with them are
    dual to it. The receiver then holds both ends of the channels
    [recv_back], which become restricted, and their ends leave the
    interface. *)
Definition recv_ok (Σ Θ2 : senv) : Prop :=
  (∀ o, o ∈ dom Θ2 → o ∉ dom Σ) ∧
  (∀ o S y S' y', Θ2 !! o = Some (S, y) → (Σ ∪ Θ2) !! edual o = Some (S', y') →
     y' = y‾ ∧ sdual S S').

Definition recv_back (Σ Θ2 : senv) : gset chan :=
  set_map ech (filter (λ o, edual o ∈ dom Σ ∨ edual o ∈ dom Θ2) (dom Θ2)).

Definition recv_env (Σ Θ2 : senv) : senv :=
  filter (λ oe : cend * (sty * point), edual oe.1 ∉ dom Θ2) Σ ∪
  filter (λ oe : cend * (sty * point), (edual oe.1 ∉ dom Σ) ∧ (edual oe.1 ∉ dom Θ2)) Θ2.

(** ** Readers

    The bodies below are stated over readers: [Vl j], [El j], [Pl j] the
    relations at a level j < n, [VN] the value relation at level n
    itself, and [X] the least fixpoint being defined. *)

(** The relation after a step of cost c at level n is X at cost 0 and
    the relation at level n − c otherwise. They are stated as two
    implications, so that X occurs strictly positively. *)
Definition at_cost_V (n c : nat) (Vl : nat → vrel) (VN : vrel)
    (W : world) (Θ : senv) (T : ty) (v : expr) : Prop :=
  (c = 0 → VN W Θ T v) ∧ (c ≠ 0 → Vl (n - c) W Θ T v).

Definition at_cost_E (n c : nat) (El : nat → erel) (X : erel)
    (W : world) (Θ : senv) (T : ty) (F : gset point) (e : expr) : Prop :=
  (c = 0 → X W Θ T F e) ∧ (c ≠ 0 → El (n - c) W Θ T F e).

Definition at_cost_P (n c : nat) (Pl : nat → prel) (X : prel)
    (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
  (c = 0 → X W Σ T p) ∧ (c ≠ 0 → Pl (n - c) W Σ T p).

Section bodies.
  Context (κ : ctable).

  (** The arrow T1 ⊸^ub_lb U at level n. Its body is read at every level
      j with j + κ(β) ≤ n, below n through [Vl] and [El], at n itself
      through [VNa] and [ENb]. The environment holds exactly the ends
      the λ mentions (decision Q14). *)
  Definition Varr (n : nat) (Vl : nat → vrel) (El : nat → erel)
      (VNa : world → senv → expr → Prop) (ENb : world → senv → gset point → expr → Prop)
      (T1 U : ty) (ub : ubound) (lb : lbound) (W : world) (Θ : senv) (v : expr) : Prop :=
    ∃ e, v = Lam e ∧ dom Θ = fends e ∧ lbx_le W lb (senv_heads Θ) ∧
      ∀ W' j Θ' w F, W ⊑ W' → j + c_beta κ ≤ n → Θ ##ₘ Θ' → ub_ltu W' ub F →
        (j < n → Vl j W' Θ' T1 w → El j W' (Θ ∪ Θ') U F (subst1 w e)) ∧
        (j = n → VNa W' Θ' w → ENb W' (Θ ∪ Θ') F (subst1 w e)).

  (** ** The obligations of the steps of a term (§2.8)

      One per label, at level n, for the step e --α--> e' in Θ with
      future F. *)
  Section obligations.
    Context (n : nat) (Vl : nat → vrel) (El : nat → erel) (VN : vrel) (X : erel)
      (W : world) (Θ : senv) (T : ty) (F : gset point).

    Definition o_beta (e' : expr) : Prop :=
      at_cost_E n (c_beta κ) El X W Θ T F e'.

    Definition o_new (ℓ : family) (c : chan) (e' : expr) : Prop :=
      cfresh c Θ → ∀ g, gfresh ℓ g Θ →
        ∃ S, at_cost_E n (c_new κ) El X W (new_env c S (pgen ℓ g) Θ) T F e'.

    Definition o_new_at (κf : field) (o : cend) (c : chan) (e' : expr) : Prop :=
      cfresh c Θ → ∃ S0 x, Θ !! o = Some (S0, x) ∧
        ∃ S, at_cost_E n (c_new κ) El X W (new_env c S (x·κf) Θ) T F e'.

    Definition o_spawn (v e' : expr) : Prop :=
      ∃ ΘM Θr, ΘM ##ₘ Θr ∧ Θ = ΘM ∪ Θr ∧
        Varr n Vl El (λ _ Θ' w, Θ' = ∅ ∧ w = EUnit) (λ W' Θ' F' e0, X W' Θ' TUnit F' e0)
          TUnit TUnit UTop LBot W ΘM v ∧
        at_cost_E n (c_spawn κ) El X W Θr T F e'.

    Definition o_send (o : cend) (w e' : expr) : Prop :=
      ∃ S0 x m U S ΘM Θr, Θ !! o = Some (S0, x) ∧ unfoldS S0 = SSeq (SSnd m U) S ∧
        ΘM ##ₘ Θr ∧ delete o Θ = ΘM ∪ Θr ∧
        at_cost_V n (c_give κ) Vl VN W ΘM (payload_at m U x) w ∧
        at_cost_E n (c_give κ) El X W (<[o := (S, x⁺)]> Θr) T F e'.

    Definition o_recv (o : cend) (w e' : expr) : Prop :=
      ∃ S0 x m U S, Θ !! o = Some (S0, x) ∧ unfoldS S0 = SSeq (SRcv m U) S ∧
        ∀ j Θin, j + c_take κ ≤ n → Θ ##ₘ Θin →
          Vl j W Θin (payload_at m U x) w →
          El j W (<[o := (S, x⁺)]> Θ ∪ Θin) T F e'.

    Definition o_close (o : cend) (e' : expr) : Prop :=
      ∃ S0 x, Θ !! o = Some (S0, x) ∧ unfoldS S0 = SEnd ∧
        at_cost_E n (c_give κ) El X W (delete o Θ) T F e'.

    Definition o_select (o : cend) (i : bool) (e' : expr) : Prop :=
      ∃ S0 x S1 S2, Θ !! o = Some (S0, x) ∧ unfoldS S0 = SPlus S1 S2 ∧
        at_cost_E n (c_give κ) El X W (<[o := (bsel i S1 S2, sel_pt x i)]> Θ) T F e'.

    Definition o_branch (o : cend) (i : bool) (e' : expr) : Prop :=
      ∃ S0 x S1 S2, Θ !! o = Some (S0, x) ∧ unfoldS S0 = SWith S1 S2 ∧
        at_cost_E n (c_take κ) El X W (<[o := (bsel i S1 S2, bra_pt x i)]> Θ) T F e'.

    Definition o_link (os : gset cend) (e' : expr) : Prop :=
      ∃ o1 o2 S1 S2 x, os = {[o1]} ∪ {[o2]} ∧ o1 ≠ o2 ∧
        Θ !! o1 = Some (S1, x) ∧ Θ !! o2 = Some (S2, x‾) ∧ sdual S1 S2 ∧
        at_cost_E n (c_link κ) El X W (delete o1 (delete o2 Θ)) T F e'.

    (** All of them, read off the label. *)
    Definition Eobl (α : tlabel) (e' : expr) : Prop :=
      match α with
      | LBeta => o_beta e'
      | LNew ℓ c => o_new ℓ c e'
      | LNewAt κf o c => o_new_at κf o c e'
      | LSpawn v => o_spawn v e'
      | LSess (SSend o w) => o_send o w e'
      | LSess (SRecv o w) => o_recv o w e'
      | LSess (SClose o) => o_close o e'
      | LSess (SSel o i) => o_select o i e'
      | LSess (SBra o i) => o_branch o i e'
      | LSess (SLink os) => o_link os e'
      end.

    (** The step clause, one conjunct per label, so that X occurs
        strictly positively. *)
    Definition Esteps (e : expr) : Prop :=
      (∀ e', tstep e LBeta e' → o_beta e') ∧                          (* O-Beta *)
      (∀ ℓ c e', tstep e (LNew ℓ c) e' → o_new ℓ c e') ∧              (* O-New *)
      (∀ κf o c e', tstep e (LNewAt κf o c) e' → o_new_at κf o c e') ∧ (* O-NewAt *)
      (∀ v e', tstep e (LSpawn v) e' → o_spawn v e') ∧              (* O-Spawn *)
      (∀ o w e', tstep e (LSess (SSend o w)) e' → o_send o w e') ∧  (* O-Send *)
      (∀ o w e', tstep e (LSess (SRecv o w)) e' → o_recv o w e') ∧    (* O-Recv *)
      (∀ o e', tstep e (LSess (SClose o)) e' → o_close o e') ∧        (* O-Close *)
      (∀ o i e', tstep e (LSess (SSel o i)) e' → o_select o i e') ∧   (* O-Select *)
      (∀ o i e', tstep e (LSess (SBra o i)) e' → o_branch o i e') ∧   (* O-Branch *)
      (∀ os e', tstep e (LSess (SLink os)) e' → o_link os e').        (* O-Link *)

    Lemma Esteps_iff e : Esteps e ↔ ∀ α e', tstep e α e' → Eobl α e'.
    Proof.
      split.
      - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) α e' Hst.
        destruct α as [|ℓ c|κf o c|v|[o w|o w|o|o i|o i|os]]; simpl; eauto.
      - intros H. split_and!; intros; match goal with Hs : tstep _ ?α ?e' |- _ => exact (H α e' Hs) end.
    Qed.
  End obligations.

  (** One unfolding of E at level n, in every W1 ⊒ W. *)
  Definition Ebody (n : nat) (Vl : nat → vrel) (El : nat → erel) (VN : vrel) (X : erel)
      (W : world) (Θ : senv) (T : ty) (F : gset point) (e : expr) : Prop :=
    ∀ W1, W ⊑ W1 →
      (irred e → VN W1 Θ T e) ∧                                 (* (stop) *)
      (¬ irred e → ready _ W1(Θ ∣ F, e)) ∧                      (* (ready) *)
      Esteps n Vl El VN X W1 Θ T F e.                           (* (step) *)

  Inductive Eind (n : nat) (Vl : nat → vrel) (El : nat → erel) (VN : vrel) : erel :=
    | EIntro W Θ T F e :
        Ebody n Vl El VN (Eind n Vl El VN) W Θ T F e → Eind n Vl El VN W Θ T F e.

  (** E at level 0 holds every term. *)
  Definition Etop (n : nat) (Vl : nat → vrel) (El : nat → erel) (VN : vrel) : erel :=
    λ W Θ T F e, match n with 0 => True | S _ => Eind n Vl El VN W Θ T F e end.

  (** V at level n by fuel on the size of the type. *)
  Fixpoint Vbody (n : nat) (Vl : nat → vrel) (El : nat → erel) (k : nat)
      (W : world) (Θ : senv) (T : ty) (v : expr) {struct k} : Prop :=
    match k with
    | 0 => False
    | S k' =>
      match T with
      | TUnit => Θ = ∅ ∧ v = EUnit
      | TSess s x _ _ => ∃ o s', v = Chan o ∧ Θ = {[o := (s', x)]} ∧ seqv s' s
      | TLolli ub lb _ T1 U _ =>
          Varr n Vl El (λ W' Θ' w, Vbody n Vl El k' W' Θ' T1 w)
            (λ W' Θ' F e, Etop n Vl El (Vbody n Vl El k') W' Θ' U F e) T1 U ub lb W Θ v
      | TProd T1 U =>
          ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ Θ1 ##ₘ Θ2 ∧ Θ = Θ1 ∪ Θ2 ∧
            Vbody n Vl El k' W Θ1 T1 v1 ∧ Vbody n Vl El k' W Θ2 U v2
      | TSum T1 U =>
          (∃ v', v = Inj false v' ∧ Vbody n Vl El k' W Θ T1 v') ∨
          (∃ v', v = Inj true v' ∧ Vbody n Vl El k' W Θ U v')
      | TBox m kk C ub _ U =>
          Θ = ∅ ∧ ∃ e, v = EBox e ∧ fends e = ∅ ∧                 (* Q14 *)
            ∀ W' xs ss, W ⊑ W' → length xs = m → length ss = kk → Forall hcontractive ss →
              wholds W' C xs →
              Vbody n Vl El k' W' ∅
                (tthunk (pt_inst (plist xs) <$> ub) (sinst_ty (slist ss) (ty_inst xs U))) (thunk e)
      | TEx lb m C T1 =>
          lbx_le W lb (senv_heads Θ) ∧
          ∃ xs, length xs = m ∧ wholds W C xs ∧ Vbody n Vl El k' W Θ (ty_inst xs T1) v
      end
    end.

  Definition Vtop (n : nat) (Vl : nat → vrel) (El : nat → erel) : vrel :=
    λ W Θ T v, Vbody n Vl El (S (tsize T)) W Θ T v.

  (** ** The obligations of the steps of a process

      One per kind of step, at level n, for the step p → p' with
      interface Σ. *)
  Section qobligations.
    Context (n : nat) (Vl : nat → vrel) (Pl : nat → prel) (VN : vrel) (X : prel)
      (W : world) (Σ : senv) (T : ty) (p : proc).

    (** Q-Admin and Q-Comm. A τ step keeps the interface. *)
    Definition q_tau (ev : event) (p' : proc) : Prop :=
      p'.1 ## chans_of Σ → at_cost_P n (ev_cost κ ev) Pl X W Σ T p'.

    Definition q_send (o : cend) (w : expr) (p' : proc) : Prop :=
      ∃ S0 x m U S Σv Σr Θe Σe, Σ !! o = Some (S0, x) ∧
        unfoldS S0 = SSeq (SSnd m U) S ∧
        Σv ##ₘ Σr ∧ delete o Σ = Σv ∪ Σr ∧
        (∀ o', o' ∈ dom Θe ↔ o' ∈ fends w ∧ ech o' ∈ p.1) ∧
        send_split Σ Σe Θe ∧
        at_cost_V n (c_give κ) Vl VN W (Σv ∪ Θe) (payload_at m U x) w ∧
        at_cost_P n (c_give κ) Pl X W (<[o := (S, x⁺)]> (Σr ∪ Σe)) T p'.

    Definition q_recv (o : cend) (w : expr) (p' : proc) : Prop :=
      ∃ S0 x m U S, Σ !! o = Some (S0, x) ∧ unfoldS S0 = SSeq (SRcv m U) S ∧
        ∀ j Θ2, j + c_take κ ≤ n → set_map ech (dom Θ2) ## p.1 →
          recv_ok (<[o := (S, x⁺)]> Σ) Θ2 → Vl j W Θ2 (payload_at m U x) w →
          Pl j W (recv_env (<[o := (S, x⁺)]> Σ) Θ2) T
            (p'.1 ∪ recv_back (<[o := (S, x⁺)]> Σ) Θ2, p'.2).

    Definition q_close (o : cend) (p' : proc) : Prop :=
      ∃ S0 x, Σ !! o = Some (S0, x) ∧ unfoldS S0 = SEnd ∧
        at_cost_P n (c_give κ) Pl X W (delete o Σ) T p'.

    Definition q_select (o : cend) (i : bool) (p' : proc) : Prop :=
      ∃ S0 x S1 S2, Σ !! o = Some (S0, x) ∧ unfoldS S0 = SPlus S1 S2 ∧
        at_cost_P n (c_give κ) Pl X W (<[o := (bsel i S1 S2, sel_pt x i)]> Σ) T p'.

    Definition q_branch (o : cend) (i : bool) (p' : proc) : Prop :=
      ∃ S0 x S1 S2, Σ !! o = Some (S0, x) ∧ unfoldS S0 = SWith S1 S2 ∧
        at_cost_P n (c_take κ) Pl X W (<[o := (bsel i S1 S2, bra_pt x i)]> Σ) T p'.

    Definition q_link (os : gset cend) (p' : proc) : Prop :=
      ∃ o1 o2 S1 S2 x, os = {[o1]} ∪ {[o2]} ∧ o1 ≠ o2 ∧
        Σ !! o1 = Some (S1, x) ∧ Σ !! o2 = Some (S2, x‾) ∧ sdual S1 S2 ∧
        at_cost_P n (c_link κ) Pl X W (delete o1 (delete o2 Σ)) T p'.

    (** All of them, read off the event. *)
    Definition Pobl (ev : event) (p' : proc) : Prop :=
      match ev with
      | EvOffer _ (SSend o w) => q_send o w p'
      | EvOffer _ (SRecv o w) => q_recv o w p'
      | EvOffer _ (SClose o) => q_close o p'
      | EvOffer _ (SSel o i) => q_select o i p'
      | EvOffer _ (SBra o i) => q_branch o i p'
      | EvOffer _ (SLink os) => q_link os p'
      | _ => q_tau ev p'
      end.

    (** The step clause, one conjunct per kind of step. *)
    Definition Psteps : Prop :=
      (∀ q ev q', erase q = p → istep q ev q' → ev_tau ev → q_tau ev (erase q')) ∧
      (∀ q i o w q', erase q = p → istep q (EvOffer i (SSend o w)) q' →
         q_send o w (erase q')) ∧                                    (* Q-Send *)
      (∀ q i o w q', erase q = p → istep q (EvOffer i (SRecv o w)) q' →
         q_recv o w (erase q')) ∧                                      (* Q-Recv *)
      (∀ q i o q', erase q = p → istep q (EvOffer i (SClose o)) q' →
         q_close o (erase q')) ∧                                       (* Q-Close *)
      (∀ q i o b q', erase q = p → istep q (EvOffer i (SSel o b)) q' →
         q_select o b (erase q')) ∧                                    (* Q-Select *)
      (∀ q i o b q', erase q = p → istep q (EvOffer i (SBra o b)) q' →
         q_branch o b (erase q')) ∧                                    (* Q-Branch *)
      (∀ q i os q', erase q = p → istep q (EvOffer i (SLink os)) q' →
         q_link os (erase q')).                                        (* Q-Link *)

  End qobligations.

  (** The clauses of P at level n in the world W1. *)
  Definition Pclauses (n : nat) (Vl : nat → vrel) (Pl : nat → prel) (VN : vrel) (X : prel)
      (W1 : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
    (pirred p → ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ VN W1 Σ T v ∧    (* P-Stop *)
                       ∀ e, e ∈ E → e = EUnit) ∧
    (¬ pirred p → ready _ W1(Σ, p)) ∧                           (* P-Ready *)
    Psteps n Vl Pl VN X W1 Σ T p.                               (* P-Step *)

  (** One unfolding of P at level n, in every strict W1 ⊒ W and under
      every fusion of the held ends (decision Q16, refined). A later world with
      a cycle would let Q-Recv bring ends that only a cyclic order
      accepts, and composition would fail (progress.md, S4.15). *)
  Definition Pbody (n : nat) (Vl : nat → vrel) (Pl : nat → prel) (VN : vrel) (X : prel)
      (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
    ∀ W1, W ⊑ W1 → strict W1 → ∀ h D, fuse_ok h D Σ p →       (* (fuse) *)
      Pclauses n Vl Pl VN X W1 (sdrop D (kren h Σ)) T (pfuse h D p).

  Inductive Pind (n : nat) (Vl : nat → vrel) (Pl : nat → prel) (VN : vrel) : prel :=
    | PIntro W Σ T p :
        Pbody n Vl Pl VN (Pind n Vl Pl VN) W Σ T p → Pind n Vl Pl VN W Σ T p.

  Definition Ptop (n : nat) (Vl : nat → vrel) (Pl : nat → prel) (VN : vrel) : prel :=
    λ W Σ T p, match n with 0 => True | S _ => Pind n Vl Pl VN W Σ T p end.

  (** ** Levels *)

  Definition dummy_level : level :=
    Level (λ _ _ _ _, False) (λ _ _ _ _ _, False) (λ _ _ _ _, False).

  Definition mk_level (below : nat → level) (n : nat) : level :=
    Level (Vtop n (λ j, lV (below j)) (λ j, lE (below j)))
      (Etop n (λ j, lV (below j)) (λ j, lE (below j)) (Vtop n (λ j, lV (below j)) (λ j, lE (below j))))
      (Ptop n (λ j, lV (below j)) (λ j, lP (below j)) (Vtop n (λ j, lV (below j)) (λ j, lE (below j)))).

  Definition Rel (n : nat) : level := sfix dummy_level mk_level n.
End bodies.

Definition Vrel (κ : ctable) (n : nat) : vrel := lV (Rel κ n).
Definition Erel (κ : ctable) (n : nat) : erel := lE (Rel κ n).
Definition Prel (κ : ctable) (n : nat) : prel := lP (Rel κ n).

(** ** Notations (Appendix A) *)

Notation "v ∈ V[ κ ]^ W '_' n ⟦ Θ ⊢ T ⟧" := (Vrel κ n W Θ T v)
  (at level 70, W at level 0, n at level 0, Θ at level 60,
   format "v  ∈  V[ κ ]^ W  '_'  n ⟦ Θ  ⊢  T ⟧").
Notation "e ∈ E[ κ ]^ W '_' n ⟦ Θ ⊢ T ⟧^ F" := (Erel κ n W Θ T F e)
  (at level 70, W at level 0, n at level 0, F at level 0, Θ at level 60,
   format "e  ∈  E[ κ ]^ W  '_'  n ⟦ Θ  ⊢  T ⟧^ F").
Notation "p ∈ P[ κ ]^ W '_' n ⟦ Σ ⊢ T ⟧" := (Prel κ n W Σ T p)
  (at level 70, W at level 0, n at level 0, Σ at level 60,
   format "p  ∈  P[ κ ]^ W  '_'  n ⟦ Σ  ⊢  T ⟧").

(** κ_DF is omitted. *)
Notation "v ∈ V^ W '_' n ⟦ Θ ⊢ T ⟧" := (Vrel κ_DF n W Θ T v)
  (at level 70, W at level 0, n at level 0, Θ at level 60,
   format "v  ∈  V^ W  '_'  n ⟦ Θ  ⊢  T ⟧").
Notation "e ∈ E^ W '_' n ⟦ Θ ⊢ T ⟧^ F" := (Erel κ_DF n W Θ T F e)
  (at level 70, W at level 0, n at level 0, F at level 0, Θ at level 60,
   format "e  ∈  E^ W  '_'  n ⟦ Θ  ⊢  T ⟧^ F").
Notation "p ∈ P^ W '_' n ⟦ Σ ⊢ T ⟧" := (Prel κ_DF n W Σ T p)
  (at level 70, W at level 0, n at level 0, Σ at level 60,
   format "p  ∈  P^ W  '_'  n ⟦ Σ  ⊢  T ⟧").

(** ** Maps of one unfolding in the fixpoint

    Transparent, so that the guard checker sees through them in the
    induction principles [Eind_ind'] and [Pind_ind']. *)

Section maps.
  Context (κ : ctable).

  Definition Varr_mapB n Vl El VNa (B1 B2 : world → senv → gset point → expr → Prop)
      (f : ∀ W Θ F e, B1 W Θ F e → B2 W Θ F e) T1 U ub lb W Θ v :
    Varr κ n Vl El VNa B1 T1 U ub lb W Θ v → Varr κ n Vl El VNa B2 T1 U ub lb W Θ v.
  Proof.
    intros (e & Hv & Hfe & Hlb & H). exists e. split; [exact Hv|]. split; [exact Hfe|].
    split; [exact Hlb|].
    intros W' j Θ' w F HW Hj Hd Hub. destruct (H W' j Θ' w F HW Hj Hd Hub) as [H1 H2].
    split; [exact H1|]. intros Hjn Hw. exact (f _ _ _ _ (H2 Hjn Hw)).
  Defined.

  Definition at_cost_E_map n c El (X1 X2 : erel) W Θ T F e
      (f : X1 W Θ T F e → X2 W Θ T F e) :
    at_cost_E n c El X1 W Θ T F e → at_cost_E n c El X2 W Θ T F e.
  Proof. intros [H1 H2]. split; [intros Hc; exact (f (H1 Hc))|exact H2]. Defined.

  Definition at_cost_P_map n c Pl (X1 X2 : prel) W Σ T p
      (f : X1 W Σ T p → X2 W Σ T p) :
    at_cost_P n c Pl X1 W Σ T p → at_cost_P n c Pl X2 W Σ T p.
  Proof. intros [H1 H2]. split; [intros Hc; exact (f (H1 Hc))|exact H2]. Defined.

  Definition Esteps_mapX n Vl El VN (X1 X2 : erel)
      (f : ∀ W Θ T F e, X1 W Θ T F e → X2 W Θ T F e) W Θ T F e :
    Esteps κ n Vl El VN X1 W Θ T F e → Esteps κ n Vl El VN X2 W Θ T F e.
  Proof.
    intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    split; [intros e' Hs; exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) (H1 e' Hs))|].
    split.
    { intros ℓ c e' Hs Hc g Hg. destruct (H2 ℓ c e' Hs Hc g Hg) as [S HS].
      exists S. exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) HS). }
    split.
    { intros κf o c e' Hs Hc. destruct (H3 κf o c e' Hs Hc) as (S0 & x & Ho & S & HS).
      exists S0, x. split; [exact Ho|]. exists S.
      exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) HS). }
    split.
    { intros v e' Hs. destruct (H4 v e' Hs) as (ΘM & Θr & A1 & A2 & A4 & A5).
      exists ΘM, Θr. split; [exact A1|]. split; [exact A2|].
      split; [exact (Varr_mapB _ _ _ _ _ _ (λ W Θ F e, f W Θ TUnit F e) _ _ _ _ _ _ _ A4)|].
      exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) A5). }
    split.
    { intros o w e' Hs.
      destruct (H5 o w e' Hs) as (S0 & x & m & U & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      exists S0, x, m, U, S, ΘM, Θr. split; [exact A1|]. split; [exact A2|].
      split; [exact A3|]. split; [exact A4|]. split; [exact A6|].
      exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) A7). }
    split; [exact H6|].
    split.
    { intros o e' Hs. destruct (H7 o e' Hs) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split; [exact A1|]. split; [exact A2|].
      exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) A3). }
    split.
    { intros o i e' Hs. destruct (H8 o i e' Hs) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split; [exact A1|]. split; [exact A2|].
      exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) A3). }
    split.
    { intros o i e' Hs. destruct (H9 o i e' Hs) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split; [exact A1|]. split; [exact A2|].
      exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) A3). }
    { intros os e' Hs. destruct (H10 os e' Hs) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      split; [exact A4|]. split; [exact A5|].
      exact (at_cost_E_map _ _ _ _ _ _ _ _ _ _ (f _ _ _ _ _) A6). }
  Defined.

  Definition Ebody_mapX n Vl El VN (X1 X2 : erel)
      (f : ∀ W Θ T F e, X1 W Θ T F e → X2 W Θ T F e) W Θ T F e :
    Ebody κ n Vl El VN X1 W Θ T F e → Ebody κ n Vl El VN X2 W Θ T F e.
  Proof.
    intros H W1 HW. destruct (H W1 HW) as (A & B & C).
    split; [exact A|]. split; [exact B|]. exact (Esteps_mapX n Vl El VN X1 X2 f W1 Θ T F e C).
  Defined.

  Lemma Eind_ind' n Vl El VN (Φ : erel) :
    (∀ W Θ T F e,
       Ebody κ n Vl El VN (λ W Θ T F e, Eind κ n Vl El VN W Θ T F e ∧ Φ W Θ T F e) W Θ T F e →
       Φ W Θ T F e) →
    ∀ W Θ T F e, Eind κ n Vl El VN W Θ T F e → Φ W Θ T F e.
  Proof.
    intros Hind. fix IH 6. intros W Θ T F e H. destruct H as [W Θ T F e H].
    apply Hind. refine (Ebody_mapX n Vl El VN _ _ _ W Θ T F e H).
    intros ? ? ? ? ? HX. exact (conj HX (IH _ _ _ _ _ HX)).
  Qed.

  Definition Psteps_mapX n Vl Pl VN (X1 X2 : prel)
      (f : ∀ W Σ T p, X1 W Σ T p → X2 W Σ T p) W Σ T p :
    Psteps κ n Vl Pl VN X1 W Σ T p → Psteps κ n Vl Pl VN X2 W Σ T p.
  Proof.
    intros (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    split.
    { intros q ev q' Hq Hs Hτ Hd.
      exact (at_cost_P_map _ _ _ _ _ _ _ _ _ (f _ _ _ _) (H1 q ev q' Hq Hs Hτ Hd)). }
    split.
    { intros q i o w q' Hq Hs.
      destruct (H2 q i o w q' Hq Hs)
        as (S0 & x & m & U & S & Σv & Σr & Θe & Σe & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A9).
      exists S0, x, m, U, S, Σv, Σr, Θe, Σe. split; [exact A1|]. split; [exact A2|].
      split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
      split; [exact A7|].
      exact (at_cost_P_map _ _ _ _ _ _ _ _ _ (f _ _ _ _) A9). }
    split; [exact H3|].
    split.
    { intros q i o q' Hq Hs. destruct (H4 q i o q' Hq Hs) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split; [exact A1|]. split; [exact A2|].
      exact (at_cost_P_map _ _ _ _ _ _ _ _ _ (f _ _ _ _) A3). }
    split.
    { intros q i o b q' Hq Hs. destruct (H5 q i o b q' Hq Hs) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split; [exact A1|]. split; [exact A2|].
      exact (at_cost_P_map _ _ _ _ _ _ _ _ _ (f _ _ _ _) A3). }
    split.
    { intros q i o b q' Hq Hs. destruct (H6 q i o b q' Hq Hs) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split; [exact A1|]. split; [exact A2|].
      exact (at_cost_P_map _ _ _ _ _ _ _ _ _ (f _ _ _ _) A3). }
    { intros q i os q' Hq Hs.
      destruct (H7 q i os q' Hq Hs) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      split; [exact A4|]. split; [exact A5|].
      exact (at_cost_P_map _ _ _ _ _ _ _ _ _ (f _ _ _ _) A6). }
  Defined.

  Definition Pbody_mapX n Vl Pl VN (X1 X2 : prel)
      (f : ∀ W Σ T p, X1 W Σ T p → X2 W Σ T p) W Σ T p :
    Pbody κ n Vl Pl VN X1 W Σ T p → Pbody κ n Vl Pl VN X2 W Σ T p.
  Proof.
    intros H W1 HW HS h D Hh. destruct (H W1 HW HS h D Hh) as (A & B & C).
    split; [exact A|]. split; [exact B|].
    exact (Psteps_mapX n Vl Pl VN X1 X2 f W1 (sdrop D (kren h Σ)) T (pfuse h D p) C).
  Defined.

  Lemma Pind_ind' n Vl Pl VN (Φ : prel) :
    (∀ W Σ T p,
       Pbody κ n Vl Pl VN (λ W Σ T p, Pind κ n Vl Pl VN W Σ T p ∧ Φ W Σ T p) W Σ T p →
       Φ W Σ T p) →
    ∀ W Σ T p, Pind κ n Vl Pl VN W Σ T p → Φ W Σ T p.
  Proof.
    intros Hind. fix IH 5. intros W Σ T p H. destruct H as [W Σ T p H].
    apply Hind. refine (Pbody_mapX n Vl Pl VN _ _ _ W Σ T p H).
    intros ? ? ? ? HX. exact (conj HX (IH _ _ _ _ HX)).
  Qed.
End maps.

(** ** Monotonicity of one unfolding in its readers

    The readers below n are read at j < n only, the value relation at
    level n at the type of the term and, when a send is free, at a
    payload, and the fixpoint at the type of the term and at ∗ (the
    spawned thunk). *)

Section mono.
  Context (κ : ctable).

  Lemma Varr_mono n Vl1 Vl2 El1 El2 VNa1 VNa2 (B1 B2 : world → senv → gset point → expr → Prop)
      T1 U ub lb W Θ v :
    (∀ j, j < n → ∀ W Θ T v, Vl2 j W Θ T v → Vl1 j W Θ T v) →
    (∀ j, j < n → ∀ W Θ T F e, El1 j W Θ T F e → El2 j W Θ T F e) →
    (c_beta κ = 0 → ∀ W Θ w, VNa2 W Θ w → VNa1 W Θ w) →
    (c_beta κ = 0 → ∀ W Θ F e, B1 W Θ F e → B2 W Θ F e) →
    Varr κ n Vl1 El1 VNa1 B1 T1 U ub lb W Θ v → Varr κ n Vl2 El2 VNa2 B2 T1 U ub lb W Θ v.
  Proof.
    intros HVl HEl HVa HB (e & -> & Hfe & Hlb & H). exists e. split_and!; [done|done|done|].
    intros W' j Θ' w F HW Hj Hd Hub. destruct (H W' j Θ' w F HW Hj Hd Hub) as [H1 H2].
    split.
    - intros Hjn Hw. apply HEl; [done|]. apply H1; [done|]. by apply HVl.
    - intros -> Hw. assert (c_beta κ = 0) as Hb by lia.
      apply HB; [done|]. apply H2; [done|]. by apply HVa.
  Qed.

  (** An arrow is an arrow at upper point ⊤ and lower point ⊥: ⊥ claims
      no bound, and ⊤ admits only the empty future, which lies above
      every upper point. O-Spawn reads its thunk there (entry 12). *)
  Lemma Varr_top n Vl El VNa ENb T1 U ub lb W Θ v :
    Varr κ n Vl El VNa ENb T1 U ub lb W Θ v → Varr κ n Vl El VNa ENb T1 U UTop LBot W Θ v.
  Proof.
    intros (e & -> & Hfe & _ & H). exists e. split_and!; [done|done|done|].
    intros W' j Θ' w F HW Hj Hd Hub. simpl in Hub. subst F.
    apply H; [done|done|done|apply ub_ltu_empty].
  Qed.

  Lemma at_cost_E_mono n c El1 El2 X1 X2 W Θ T F e :
    n ≠ 0 → (∀ j, j < n → El1 j W Θ T F e → El2 j W Θ T F e) →
    (X1 W Θ T F e → X2 W Θ T F e) →
    at_cost_E n c El1 X1 W Θ T F e → at_cost_E n c El2 X2 W Θ T F e.
  Proof. intros Hn HEl HX [H1 H2]. split; [auto|]. intros Hc. apply HEl; [lia|auto]. Qed.

  Lemma at_cost_P_mono n c Pl1 Pl2 X1 X2 W Σ T p :
    n ≠ 0 → (∀ j, j < n → Pl1 j W Σ T p → Pl2 j W Σ T p) →
    (X1 W Σ T p → X2 W Σ T p) →
    at_cost_P n c Pl1 X1 W Σ T p → at_cost_P n c Pl2 X2 W Σ T p.
  Proof. intros Hn HPl HX [H1 H2]. split; [auto|]. intros Hc. apply HPl; [lia|auto]. Qed.

  Lemma at_cost_V_mono n c Vl1 Vl2 VN1 VN2 W Θ T v :
    n ≠ 0 → (∀ j, j < n → Vl1 j W Θ T v → Vl2 j W Θ T v) →
    (c = 0 → VN1 W Θ T v → VN2 W Θ T v) →
    at_cost_V n c Vl1 VN1 W Θ T v → at_cost_V n c Vl2 VN2 W Θ T v.
  Proof. intros Hn HVl HV [H1 H2]. split; [auto|]. intros Hc. apply HVl; [lia|auto]. Qed.

  Lemma Esteps_mono n Vl1 Vl2 El1 El2 VN1 VN2 X1 X2 W Θ T F e :
    n ≠ 0 →
    (∀ j, j < n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
    (∀ j, j < n → ∀ W Θ T F e, El1 j W Θ T F e → El2 j W Θ T F e) →
    (c_give κ = 0 → ∀ W Θ T v, VN1 W Θ T v → VN2 W Θ T v) →
    (∀ W Θ F e, X1 W Θ T F e → X2 W Θ T F e) →
    (∀ W Θ F e, X1 W Θ TUnit F e → X2 W Θ TUnit F e) →
    Esteps κ n Vl1 El1 VN1 X1 W Θ T F e → Esteps κ n Vl2 El2 VN2 X2 W Θ T F e.
  Proof.
    intros Hn HVl HEl HVN HX HXu (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (∀ c W Θ F e, at_cost_E n c El1 X1 W Θ T F e → at_cost_E n c El2 X2 W Θ T F e) as Hac.
    { intros c W0 Θ0 F0 e0. apply at_cost_E_mono; [done| |apply HX]. intros j Hj. by apply HEl. }
    split_and!.
    - intros e' Hs. apply Hac, H1, Hs.
    - intros ℓ c e' Hs Hc g Hg. destruct (H2 ℓ c e' Hs Hc g Hg) as [S HS]. exists S. by apply Hac.
    - intros κf o c e' Hs Hc. destruct (H3 κf o c e' Hs Hc) as (S0 & x & Ho & S & HS).
      exists S0, x. split; [done|]. exists S. by apply Hac.
    - intros v e' Hs. destruct (H4 v e' Hs) as (ΘM & Θr & A1 & A2 & A4 & A5).
      exists ΘM, Θr. split_and!; [done|done| |by apply Hac].
      revert A4. apply Varr_mono.
      + intros j Hj W0 Θ0 T0 v0. by apply HVl.
      + intros j Hj. by apply HEl.
      + by intros.
      + intros _ W0 Θ0 F0 e0. apply HXu.
    - intros o w e' Hs.
      destruct (H5 o w e' Hs) as (S0 & x & m & U & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      exists S0, x, m, U, S, ΘM, Θr. split_and!; [done..| |by apply Hac].
      eapply at_cost_V_mono; [done| |intros; by apply HVN|exact A6].
      intros j Hj. by apply HVl.
    - intros o w e' Hs. destruct (H6 o w e' Hs) as (S0 & x & m & U & S & A1 & A2 & A3).
      exists S0, x, m, U, S. split_and!; [done|done|].
      intros j Θin Hj Hd Hw. pose proof (c_take_pos κ). apply HEl; [lia|].
      apply A3; [done|done|]. apply HVl; [lia|done].
    - intros o e' Hs. destruct (H7 o e' Hs) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split_and!; [done|done|by apply Hac].
    - intros o i e' Hs. destruct (H8 o i e' Hs) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros o i e' Hs. destruct (H9 o i e' Hs) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros os e' Hs. destruct (H10 os e' Hs) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split_and!; [done..|by apply Hac].
  Qed.

  Lemma Ebody_mono n Vl1 Vl2 El1 El2 VN1 VN2 X1 X2 W Θ T F e :
    n ≠ 0 →
    (∀ j, j < n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
    (∀ j, j < n → ∀ W Θ T F e, El1 j W Θ T F e → El2 j W Θ T F e) →
    (∀ W Θ v, VN1 W Θ T v → VN2 W Θ T v) →
    (c_give κ = 0 → ∀ W Θ T v, VN1 W Θ T v → VN2 W Θ T v) →
    (∀ W Θ F e, X1 W Θ T F e → X2 W Θ T F e) →
    (∀ W Θ F e, X1 W Θ TUnit F e → X2 W Θ TUnit F e) →
    Ebody κ n Vl1 El1 VN1 X1 W Θ T F e → Ebody κ n Vl2 El2 VN2 X2 W Θ T F e.
  Proof.
    intros Hn HVl HEl HVT HVN HX HXu H W1 HW. destruct (H W1 HW) as (A & B & C).
    split_and!; [auto|done|]. by eapply Esteps_mono.
  Qed.

  Lemma Psteps_mono n Vl1 Vl2 Pl1 Pl2 VN1 VN2 X1 X2 W Σ T p :
    n ≠ 0 →
    (∀ j, j < n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
    (∀ j, j < n → ∀ W Σ T p, Pl1 j W Σ T p → Pl2 j W Σ T p) →
    (∀ W Θ T v, VN1 W Θ T v → VN2 W Θ T v) →
    (∀ W Σ p, X1 W Σ T p → X2 W Σ T p) →
    Psteps κ n Vl1 Pl1 VN1 X1 W Σ T p → Psteps κ n Vl2 Pl2 VN2 X2 W Σ T p.
  Proof.
    intros Hn HVl HPl HVN HX (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    assert (∀ c W Σ p, at_cost_P n c Pl1 X1 W Σ T p → at_cost_P n c Pl2 X2 W Σ T p) as Hac.
    { intros c W0 Σ0 p0. apply at_cost_P_mono; [done| |apply HX]. intros j Hj. by apply HPl. }
    split_and!.
    - intros q ev q' Hq Hs Hτ Hd. apply Hac. exact (H1 q ev q' Hq Hs Hτ Hd).
    - intros q i o w q' Hq Hs.
      destruct (H2 q i o w q' Hq Hs)
        as (S0 & x & m & U & S & Σv & Σr & Θe & Σe & A1 & A2 & A3 & A4 & A5 & A7 & A8 & A9).
      exists S0, x, m, U, S, Σv, Σr, Θe, Σe. split_and!; [done..| |by apply Hac].
      eapply at_cost_V_mono; [done| |intros; by apply HVN|exact A8].
      intros j Hj. by apply HVl.
    - intros q i o w q' Hq Hs. destruct (H3 q i o w q' Hq Hs) as (S0 & x & m & U & S & A1 & A2 & A3).
      exists S0, x, m, U, S. split_and!; [done|done|].
      intros j Θ2 Hj Hd Hok Hw. pose proof (c_take_pos κ). apply HPl; [lia|].
      apply A3; [done|done|done|]. apply HVl; [lia|done].
    - intros q i o q' Hq Hs. destruct (H4 q i o q' Hq Hs) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split_and!; [done|done|by apply Hac].
    - intros q i o b q' Hq Hs. destruct (H5 q i o b q' Hq Hs) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros q i o b q' Hq Hs. destruct (H6 q i o b q' Hq Hs) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros q i os q' Hq Hs.
      destruct (H7 q i os q' Hq Hs) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split_and!; [done..|by apply Hac].
  Qed.

  Lemma Pbody_mono n Vl1 Vl2 Pl1 Pl2 VN1 VN2 X1 X2 W Σ T p :
    n ≠ 0 →
    (∀ j, j < n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
    (∀ j, j < n → ∀ W Σ T p, Pl1 j W Σ T p → Pl2 j W Σ T p) →
    (∀ W Θ T v, VN1 W Θ T v → VN2 W Θ T v) →
    (∀ W Σ p, X1 W Σ T p → X2 W Σ T p) →
    Pbody κ n Vl1 Pl1 VN1 X1 W Σ T p → Pbody κ n Vl2 Pl2 VN2 X2 W Σ T p.
  Proof.
    intros Hn HVl HPl HVN HX H W1 HW HS h D Hh. destruct (H W1 HW HS h D Hh) as (A & B & C).
    split_and!; [|done|by eapply Psteps_mono].
    intros Hirr. destruct (A Hirr) as (v & E & Hp & Hv & HE).
    exists v, E. split_and!; [done|by apply HVN|done].
  Qed.

  (** E at level n depends on V at level n only at its type, at ∗ and,
      when a send is free, at payloads. *)
  Lemma Etop_mono n Vl1 Vl2 El1 El2 VN1 VN2 W Θ T F e :
    (∀ j, j < n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
    (∀ j, j < n → ∀ W Θ T F e, El1 j W Θ T F e → El2 j W Θ T F e) →
    (∀ W Θ v, VN1 W Θ T v → VN2 W Θ T v) →
    (∀ W Θ v, VN1 W Θ TUnit v → VN2 W Θ TUnit v) →
    (c_give κ = 0 → ∀ W Θ T v, VN1 W Θ T v → VN2 W Θ T v) →
    Etop κ n Vl1 El1 VN1 W Θ T F e → Etop κ n Vl2 El2 VN2 W Θ T F e.
  Proof.
    intros HVl HEl HVT HVu HVN. destruct n as [|n]; [done|]. simpl.
    intros H.
    assert (∀ W Θ T' F e, Eind κ (S n) Vl1 El1 VN1 W Θ T' F e →
              (T' = T ∨ T' = TUnit) → Eind κ (S n) Vl2 El2 VN2 W Θ T' F e) as Hgen.
    2: { by apply Hgen; [|left]. }
    refine (Eind_ind' κ (S n) Vl1 El1 VN1
      (λ W Θ T' F e, (T' = T ∨ T' = TUnit) → Eind κ (S n) Vl2 El2 VN2 W Θ T' F e) _).
    intros W0 Θ0 T' F0 e0 H0 HT'. constructor.
    revert H0. apply Ebody_mono; [done|done|done| |done| |].
    - intros W1 Θ1 v1. destruct HT' as [->| ->]; auto.
    - intros W1 Θ1 F1 e1 [_ HΦ]. by apply HΦ.
    - intros W1 Θ1 F1 e1 [_ HΦ]. by apply HΦ; right.
  Qed.
End mono.

(** ** Fuel and readers of V at level n *)

Section fuel.
  Context (κ : ctable).

  Lemma Vbody_ext n Vl1 Vl2 El1 El2 k W Θ T v :
    (∀ j, j < n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
    (∀ j, j < n → ∀ W Θ T F e, El1 j W Θ T F e ↔ El2 j W Θ T F e) →
    Vbody κ n Vl1 El1 k W Θ T v ↔ Vbody κ n Vl2 El2 k W Θ T v.
  Proof.
    intros HVl HEl. revert W Θ T v. induction k as [|k IH]; intros W Θ T v; [done|].
    destruct T as [|ub lb c T1 U a|T1 U|T1 U|m kk C ub c U|s x a mt|lb m C T1];
      cbn [Vbody].
    - done.
    - split; (apply Varr_mono; [intros; by apply HVl|intros; by apply HEl|intros; by apply IH|]);
        intros _ W0 Θ0 F0 e0;
        (apply Etop_mono; [intros; first [by apply HVl|symmetry; by apply HVl]|intros; by apply HEl|..]);
        intros; by apply IH.
    - by setoid_rewrite IH.
    - by setoid_rewrite IH.
    - by setoid_rewrite IH.
    - done.
    - by setoid_rewrite IH.
  Qed.

  Lemma Vbody_fuel n Vl El k1 : ∀ k2 W Θ T v, tsize T < k1 → tsize T < k2 →
    Vbody κ n Vl El k1 W Θ T v ↔ Vbody κ n Vl El k2 W Θ T v.
  Proof.
    induction k1 as [|k1 IH]; intros k2 W Θ T v H1 H2; [lia|].
    destruct k2 as [|k2]; [lia|].
    destruct T as [|ub lb c T1 U a|T1 U|T1 U|m kk C ub c U|s x a mt|lb m C T1];
      cbn [Vbody tsize] in *.
    - done.
    - pose proof (tsize_pos T1). pose proof (tsize_pos U).
      assert (∀ W Θ T v, tsize T ≤ tsize T1 + tsize U →
                Vbody κ n Vl El k1 W Θ T v ↔ Vbody κ n Vl El k2 W Θ T v) as IH'.
      { intros. apply IH; lia. }
      split; (eapply Varr_mono; [done|done|intros; apply IH'; [lia|done]|]);
        intros Hb W0 Θ0 F0 e0;
        (eapply Etop_mono; [done|done|intros; apply IH'; [lia|done]|intros; apply IH'; [simpl; lia|done]|]);
        intros Hg; pose proof (c_give_pos κ Hb) as Hgp; lia.
    - split; intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & Hv1 & Hv2);
        (exists v1, v2, Θ1, Θ2); split_and!; try done; (eapply IH; [..|eassumption]; lia).
    - split; (intros [(v' & -> & Hv)|(v' & -> & Hv)]; [left|right]);
        (exists v'); split; try done; (eapply IH; [..|eassumption]; lia).
    - assert (∀ xs ss, tsize (tthunk (pt_inst (plist xs) <$> ub) (sinst_ty (slist ss) (ty_inst xs U)))
                = 2 + tsize U) as Hts.
      { intros xs ss. rewrite tsize_tthunk. unfold ty_inst. by rewrite tsize_sinst, tsize_pinst. }
      split; intros (-> & e & -> & Hfe & H); split; try done; (exists e); split_and!; try done;
        intros W' xs ss HW Hxs Hss Hsc HC; specialize (H W' xs ss HW Hxs Hss Hsc HC);
        (eapply IH; [..|exact H]); rewrite Hts; lia.
    - done.
    - assert (∀ xs, tsize (ty_inst xs T1) = tsize T1) as Hts.
      { intros xs. unfold ty_inst. by rewrite tsize_pinst. }
      apply and_iff_compat_l. split; intros (xs & ? & ? & Hv); (exists xs); split_and!; try done;
        (eapply IH; [..|exact Hv]); rewrite Hts; lia.
  Qed.
End fuel.

(** ** Characteristic equations

    Unfoldings of the three relations that never mention the encoding:
    one per type constructor for V, and one per positive level for E and
    P with an induction principle over the steps of cost 0. Later proofs
    use only these. *)

Section equations.
  Context (κ : ctable).

  Local Definition BL (n : nat) : nat → level := sfix_below dummy_level (mk_level κ) n.

  Local Lemma Rel_unfold n : Rel κ n = mk_level κ (BL n) n.
  Proof. apply sfix_unfold. Qed.

  Local Lemma BL_lt n j : j < n → BL n j = Rel κ j.
  Proof. apply sfix_below_lt. Qed.

  Local Lemma BL_V n : ∀ j, j < n → ∀ W Θ T v, lV (BL n j) W Θ T v ↔ Vrel κ j W Θ T v.
  Proof. intros j Hj. unfold Vrel. by rewrite BL_lt. Qed.
  Local Lemma BL_E n : ∀ j, j < n → ∀ W Θ T F e, lE (BL n j) W Θ T F e ↔ Erel κ j W Θ T F e.
  Proof. intros j Hj. unfold Erel. by rewrite BL_lt. Qed.
  Local Lemma BL_E1 n j W Θ T F e : j < n → lE (BL n j) W Θ T F e → Erel κ j W Θ T F e.
  Proof. intros Hj. by apply BL_E. Qed.
  Local Lemma BL_E2 n j W Θ T F e : j < n → Erel κ j W Θ T F e → lE (BL n j) W Θ T F e.
  Proof. intros Hj. by apply BL_E. Qed.
  Local Lemma BL_P1 n j W Σ T p : j < n → lP (BL n j) W Σ T p → Prel κ j W Σ T p.
  Proof. intros Hj. unfold Prel. by rewrite BL_lt. Qed.
  Local Lemma BL_P2 n j W Σ T p : j < n → Prel κ j W Σ T p → lP (BL n j) W Σ T p.
  Proof. intros Hj. unfold Prel. by rewrite BL_lt. Qed.
  Lemma Vrel_fuel n k W Θ T v :
    tsize T < k → Vrel κ n W Θ T v ↔ Vbody κ n (Vrel κ) (Erel κ) k W Θ T v.
  Proof.
    intros Hk. unfold Vrel at 1. rewrite Rel_unfold. cbn [mk_level lV]. unfold Vtop.
    rewrite (Vbody_fuel κ n _ _ (S (tsize T)) k) by lia.
    apply Vbody_ext; [apply BL_V|apply BL_E].
  Qed.

  Lemma Vrel_unfold n W Θ T v :
    Vrel κ n W Θ T v ↔ Vbody κ n (Vrel κ) (Erel κ) (S (tsize T)) W Θ T v.
  Proof. apply Vrel_fuel. lia. Qed.

  Lemma Erel_unfold n W Θ T F e :
    Erel κ n W Θ T F e ↔ Etop κ n (Vrel κ) (Erel κ) (Vrel κ n) W Θ T F e.
  Proof.
    unfold Erel at 1. rewrite Rel_unfold. cbn [mk_level lE].
    assert (∀ W Θ T v, Vtop κ n (λ j, lV (BL n j)) (λ j, lE (BL n j)) W Θ T v ↔ Vrel κ n W Θ T v)
      as HV.
    { intros. rewrite Vrel_unfold. apply Vbody_ext; [apply BL_V|apply BL_E]. }
    split; apply Etop_mono.
    all: intros; first [by apply BL_V|symmetry; by apply BL_V|by eapply BL_E1|by eapply BL_E2
                        |by apply HV].
  Qed.

  Lemma Prel_unfold n W Σ T p :
    Prel κ n W Σ T p ↔ Ptop κ n (Vrel κ) (Prel κ) (Vrel κ n) W Σ T p.
  Proof.
    unfold Prel at 1. rewrite Rel_unfold. cbn [mk_level lP Ptop].
    assert (∀ W Θ T v, Vtop κ n (λ j, lV (BL n j)) (λ j, lE (BL n j)) W Θ T v ↔ Vrel κ n W Θ T v)
      as HV.
    { intros. rewrite Vrel_unfold. apply Vbody_ext; [apply BL_V|apply BL_E]. }
    destruct n as [|n]; [done|].
    assert (∀ (Pl1 Pl2 : nat → prel) VN1 VN2,
      (∀ j, j < S n → ∀ W Θ T v, lV (BL (S n) j) W Θ T v ↔ Vrel κ j W Θ T v) →
      (∀ j, j < S n → ∀ W Σ T p, Pl1 j W Σ T p → Pl2 j W Σ T p) →
      (∀ W Θ T v, VN1 W Θ T v → VN2 W Θ T v) →
      ∀ Vl1 Vl2, (∀ j, j < S n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
      ∀ W Σ T p, Pind κ (S n) Vl1 Pl1 VN1 W Σ T p → Pind κ (S n) Vl2 Pl2 VN2 W Σ T p) as Hgen.
    { intros Pl1 Pl2 VN1 VN2 _ HPl HVN Vl1 Vl2 HVl.
      refine (Pind_ind' κ (S n) Vl1 Pl1 VN1 _ _).
      intros W0 Σ0 T0 p0 H0. constructor. revert H0. apply Pbody_mono; [done|done|done|done|].
      by intros ? ? ? [_ ?]. }
    split; apply Hgen; try done; intros; first [by eapply BL_P1|by eapply BL_P2|by apply HV
      |by apply BL_V|symmetry; by apply BL_V].
  Qed.

  Lemma Erel_0 W Θ T F e : Erel κ 0 W Θ T F e.
  Proof. by apply Erel_unfold. Qed.

  Lemma Prel_0 W Σ T p : Prel κ 0 W Σ T p.
  Proof. by apply Prel_unfold. Qed.

  (** *** V, one equation per type constructor *)

  Lemma Vrel_unit_iff n W Θ v : Vrel κ n W Θ TUnit v ↔ Θ = ∅ ∧ v = EUnit.
  Proof. by rewrite Vrel_unfold. Qed.

  Lemma Vrel_sess_iff n W Θ s x a v mt :
    Vrel κ n W Θ (TSess s x a mt) v ↔ ∃ o s', v = Chan o ∧ Θ = {[o := (s', x)]} ∧ seqv s' s.
  Proof. by rewrite Vrel_unfold. Qed.

  Lemma Vrel_prod_iff n W Θ T1 U v :
    Vrel κ n W Θ (TProd T1 U) v ↔
    ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ Θ1 ##ₘ Θ2 ∧ Θ = Θ1 ∪ Θ2 ∧
      Vrel κ n W Θ1 T1 v1 ∧ Vrel κ n W Θ2 U v2.
  Proof.
    rewrite Vrel_unfold. cbn [Vbody tsize].
    assert (∀ W Θ v, Vbody κ n (Vrel κ) (Erel κ) (S (tsize T1 + tsize U)) W Θ T1 v ↔
              Vrel κ n W Θ T1 v) as H1 by (intros; symmetry; apply Vrel_fuel; lia).
    assert (∀ W Θ v, Vbody κ n (Vrel κ) (Erel κ) (S (tsize T1 + tsize U)) W Θ U v ↔
              Vrel κ n W Θ U v) as H2 by (intros; symmetry; apply Vrel_fuel; lia).
    by setoid_rewrite H1; setoid_rewrite H2.
  Qed.

  Lemma Vrel_sum_iff n W Θ T1 U v :
    Vrel κ n W Θ (TSum T1 U) v ↔
    (∃ v', v = Inj false v' ∧ Vrel κ n W Θ T1 v') ∨ (∃ v', v = Inj true v' ∧ Vrel κ n W Θ U v').
  Proof.
    rewrite Vrel_unfold. cbn [Vbody tsize].
    assert (∀ W Θ v, Vbody κ n (Vrel κ) (Erel κ) (S (tsize T1 + tsize U)) W Θ T1 v ↔
              Vrel κ n W Θ T1 v) as H1 by (intros; symmetry; apply Vrel_fuel; lia).
    assert (∀ W Θ v, Vbody κ n (Vrel κ) (Erel κ) (S (tsize T1 + tsize U)) W Θ U v ↔
              Vrel κ n W Θ U v) as H2 by (intros; symmetry; apply Vrel_fuel; lia).
    by setoid_rewrite H1; setoid_rewrite H2.
  Qed.

  (** The arrow reads its body at every level j with j + κ(β) ≤ n. *)
  Definition Varr_rel (n : nat) (T1 U : ty) (ub : ubound) (lb : lbound) (W : world) (Θ : senv)
      (v : expr) : Prop :=
    ∃ e, v = Lam e ∧ dom Θ = fends e ∧ lbx_le W lb (senv_heads Θ) ∧
      ∀ W' j Θ' w F, W ⊑ W' → j + c_beta κ ≤ n → Θ ##ₘ Θ' → ub_ltu W' ub F →
        Vrel κ j W' Θ' T1 w → Erel κ j W' (Θ ∪ Θ') U F (subst1 w e).

  Lemma Varr_rel_iff n T1 U ub lb W Θ v :
    Varr κ n (Vrel κ) (Erel κ) (λ W Θ w, Vrel κ n W Θ T1 w) (λ W Θ F e, Erel κ n W Θ U F e)
      T1 U ub lb W Θ v ↔ Varr_rel n T1 U ub lb W Θ v.
  Proof.
    split; intros (e & -> & Hfe & Hlb & H); exists e; (split; [done|]); (split; [done|]); (split; [done|]).
    - intros W' j Θ' w F HW Hj Hd Hub Hw. destruct (H W' j Θ' w F HW Hj Hd Hub) as [H1 H2].
      destruct (decide (j < n)); [by apply H1|]. assert (j = n) as -> by lia. by apply H2.
    - intros W' j Θ' w F HW Hj Hd Hub. split; [intros Hjn Hw; by apply H|]. intros -> Hw. by apply H.
  Qed.

  Lemma Vrel_lolli_iff n W Θ ub lb c T1 U a v :
    Vrel κ n W Θ (TLolli ub lb c T1 U a) v ↔ Varr_rel n T1 U ub lb W Θ v.
  Proof.
    rewrite Vrel_unfold, <-Varr_rel_iff.
    remember (tsize (TLolli ub lb c T1 U a)) as k eqn:Hk. cbn [Vbody].
    cbn [tsize] in Hk. pose proof (tsize_pos T1). pose proof (tsize_pos U).
    assert (∀ W Θ T v, tsize T < k → Vbody κ n (Vrel κ) (Erel κ) k W Θ T v ↔ Vrel κ n W Θ T v)
      as HF.
    { intros. symmetry. by apply Vrel_fuel. }
    assert (c_beta κ = 0 → ∀ W Θ F e,
      Etop κ n (Vrel κ) (Erel κ) (Vbody κ n (Vrel κ) (Erel κ) k) W Θ U F e ↔ Erel κ n W Θ U F e)
      as HE.
    { intros Hb W0 Θ0 F0 e0. rewrite Erel_unfold. pose proof (c_give_pos κ Hb).
      split; (apply Etop_mono;
        [intros; reflexivity|intros; done|intros; apply HF; [lia|done]
        |intros; apply HF; [simpl; lia|done]|intros; lia]). }
    split; (apply Varr_mono;
      [intros; done|intros; done|intros _ ? ? ? ?; apply HF; [lia|done]|intros Hb ? ? ? ? ?; by apply HE]).
  Qed.

  Lemma Vrel_box_iff n W Θ m kk C ub c U v :
    Vrel κ n W Θ (TBox m kk C ub c U) v ↔
    Θ = ∅ ∧ ∃ e, v = EBox e ∧ fends e = ∅ ∧
      ∀ W' xs ss, W ⊑ W' → length xs = m → length ss = kk → Forall hcontractive ss →
        wholds W' C xs →
        Vrel κ n W' ∅ (tthunk (pt_inst (plist xs) <$> ub) (sinst_ty (slist ss) (ty_inst xs U)))
          (thunk e).
  Proof.
    rewrite Vrel_unfold. cbn [Vbody tsize].
    assert (∀ xs ss W' v, Vbody κ n (Vrel κ) (Erel κ) (S (S (S (tsize U)))) W' ∅
                (tthunk (pt_inst (plist xs) <$> ub) (sinst_ty (slist ss) (ty_inst xs U))) v ↔
              Vrel κ n W' ∅ (tthunk (pt_inst (plist xs) <$> ub) (sinst_ty (slist ss) (ty_inst xs U))) v)
      as HF.
    { intros. symmetry. apply Vrel_fuel. rewrite tsize_tthunk. unfold ty_inst.
      rewrite tsize_sinst, tsize_pinst. lia. }
    by setoid_rewrite HF.
  Qed.

  Lemma Vrel_ex_iff n W Θ lb m C T1 v :
    Vrel κ n W Θ (TEx lb m C T1) v ↔
    lbx_le W lb (senv_heads Θ) ∧ ∃ xs, length xs = m ∧ wholds W C xs ∧ Vrel κ n W Θ (ty_inst xs T1) v.
  Proof.
    rewrite Vrel_unfold. cbn [Vbody tsize].
    assert (∀ xs, Vbody κ n (Vrel κ) (Erel κ) (S (tsize T1)) W Θ (ty_inst xs T1) v ↔
              Vrel κ n W Θ (ty_inst xs T1) v) as HF.
    { intros. symmetry. apply Vrel_fuel. unfold ty_inst. rewrite tsize_pinst. lia. }
    by setoid_rewrite HF.
  Qed.

  (** *** E and P at a positive level *)

  Lemma Erel_S_iff n W Θ T F e :
    Erel κ (S n) W Θ T F e ↔
    Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) (Erel κ (S n)) W Θ T F e.
  Proof.
    rewrite Erel_unfold. cbn [Etop]. split.
    - intros H. destruct H as [W Θ T F e H]. revert H.
      apply Ebody_mono; [lia|intros; reflexivity|intros ? ? ? ? ? ? ? H; exact H
        |intros ? ? ? H; exact H|intros _ ? ? ? ? H; exact H|..].
      all: intros ? ? ? ? H; exact (proj2 (Erel_unfold (S n) _ _ _ _ _) H).
    - intros H. constructor. revert H.
      apply Ebody_mono; [lia|intros; reflexivity|intros ? ? ? ? ? ? ? H; exact H
        |intros ? ? ? H; exact H|intros _ ? ? ? ? H; exact H|..].
      all: intros ? ? ? ? H; exact (proj1 (Erel_unfold (S n) _ _ _ _ _) H).
  Qed.

  (** Induction over the steps of cost 0 at a positive level. *)
  Lemma Erel_S_ind n (Φ : erel) :
    (∀ W Θ T F e,
       Ebody κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n))
         (λ W Θ T F e, Erel κ (S n) W Θ T F e ∧ Φ W Θ T F e) W Θ T F e →
       Φ W Θ T F e) →
    ∀ W Θ T F e, Erel κ (S n) W Θ T F e → Φ W Θ T F e.
  Proof.
    intros Hind W Θ T F e H. apply (proj1 (Erel_unfold (S n) _ _ _ _ _)) in H. cbn [Etop] in H.
    revert W Θ T F e H.
    apply Eind_ind'. intros W Θ T F e H. apply Hind. revert H.
    apply Ebody_mono; [lia|intros; reflexivity|intros ? ? ? ? ? ? ? H; exact H
      |intros ? ? ? H; exact H|intros _ ? ? ? ? H; exact H|..].
    all: intros ? ? ? ? [H1 H2]; split; [exact (proj2 (Erel_unfold (S n) _ _ _ _ _) H1)|exact H2].
  Qed.

  Lemma Prel_S_iff n W Σ T p :
    Prel κ (S n) W Σ T p ↔
    Pbody κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) (Prel κ (S n)) W Σ T p.
  Proof.
    rewrite Prel_unfold. cbn [Ptop]. split.
    - intros H. destruct H as [W Σ T p H]. revert H.
      apply Pbody_mono; [lia|intros; reflexivity|intros ? ? ? ? ? ? H; exact H
        |intros ? ? ? ? H; exact H|].
      intros ? ? ? H; exact (proj2 (Prel_unfold (S n) _ _ _ _) H).
    - intros H. constructor. revert H.
      apply Pbody_mono; [lia|intros; reflexivity|intros ? ? ? ? ? ? H; exact H
        |intros ? ? ? ? H; exact H|].
      intros ? ? ? H; exact (proj1 (Prel_unfold (S n) _ _ _ _) H).
  Qed.

  Lemma Prel_S_ind n (Φ : prel) :
    (∀ W Σ T p,
       Pbody κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n))
         (λ W Σ T p, Prel κ (S n) W Σ T p ∧ Φ W Σ T p) W Σ T p →
       Φ W Σ T p) →
    ∀ W Σ T p, Prel κ (S n) W Σ T p → Φ W Σ T p.
  Proof.
    intros Hind W Σ T p H. apply (proj1 (Prel_unfold (S n) _ _ _ _)) in H. cbn [Ptop] in H.
    revert W Σ T p H.
    apply Pind_ind'. intros W Σ T p H. apply Hind. revert H.
    apply Pbody_mono; [lia|intros; reflexivity|intros ? ? ? ? ? ? H; exact H
      |intros ? ? ? ? H; exact H|].
    intros ? ? ? [H1 H2]; split; [exact (proj2 (Prel_unfold (S n) _ _ _ _) H1)|exact H2].
  Qed.
  (** The clauses at the identity renaming. *)
  Lemma Pbody_id n Vl Pl VN X W Σ T p :
    Pbody κ n Vl Pl VN X W Σ T p → ∀ W1, W ⊑ W1 → strict W1 → Pclauses κ n Vl Pl VN X W1 Σ T p.
  Proof.
    intros H W1 HW HS. pose proof (H W1 HW HS id ∅ (fuse_ok_id Σ p)) as H'.
    by rewrite pfuse_empty, sdrop_empty, kren_id_map, pmap_id in H'.
  Qed.

  Lemma Prel_S_clauses n W Σ T p :
    Prel κ (S n) W Σ T p → ∀ W1, W ⊑ W1 → strict W1 →
    Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) (Prel κ (S n)) W1 Σ T p.
  Proof. intros H. apply Pbody_id. by apply Prel_S_iff. Qed.
End equations.
