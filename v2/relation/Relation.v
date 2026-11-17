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

    Every unfolding of E and P holds in every world W1 ⊒ W (decision Q9),
    so E and P are monotone in the world by definition.

    The relation reads no syntax of a term but the labels of its steps,
    and from a label only the transfer set M of a send and a spawn
    (decision Q3). Its environments map an end to a session type at a
    point ([senv]) and carry no credit. The relation reads no annotation
    of a type: a session type is compared after erasing its annotations
    ([seqv]), and costs, transformers, floors and credits are never read.
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
  | TUnit | TSess _ _ => 1
  | TLolli _ _ _ _ _ T1 _ U _ | TProd T1 _ U _ | TSum T1 _ U _ => S (tsize T1 + tsize U)
  | TBox _ _ _ _ _ _ U _ => 3 + tsize U
  | TEx _ _ _ T1 _ => S (tsize T1)
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
  TLolli ub None None tinf None TUnit None U None.

Lemma tsize_tthunk ub U : tsize (tthunk ub U) = 2 + tsize U.
Proof. simpl. lia. Qed.

(** The thunk a box !e stands for: applied to ∗ it unrolls once. *)
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

(** The environment of the relation for a typing environment: the
    credits go. *)
Definition tenv_erase (Θ : tenv) : senv := (λ e, (te_sty e, te_pt e)) <$> Θ.

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

(** The relation after a step of cost c at level n: X at cost 0, the
    relation at level n − c otherwise. They are stated as two
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
      through [VNa] and [ENb]. *)
  Definition Varr (n : nat) (Vl : nat → vrel) (El : nat → erel)
      (VNa : world → senv → expr → Prop) (ENb : world → senv → gset point → expr → Prop)
      (T1 U : ty) (ub lb : option point) (W : world) (Θ : senv) (v : expr) : Prop :=
    ∃ e, v = Lam e ∧ lb_le W lb (senv_heads Θ) ∧
      ∀ W' j Θ' w F, W ⊑ W' → j + c_beta κ ≤ n → Θ ##ₘ Θ' → ub_lt W' ub F →
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

    Definition o_spawn (M : gset cend) (v e' : expr) : Prop :=
      ∃ ΘM Θr ub lb, ΘM ##ₘ Θr ∧ Θ = ΘM ∪ Θr ∧ dom ΘM = M ∧
        Varr n Vl El (λ _ Θ' w, Θ' = ∅ ∧ w = EUnit) (λ W' Θ' F' e0, X W' Θ' TUnit F' e0)
          TUnit TUnit ub lb W ΘM v ∧
        at_cost_E n (c_spawn κ) El X W Θr T F e'.

    Definition o_send (o : cend) (M : gset cend) (w e' : expr) : Prop :=
      ∃ S0 x m U b S ΘM Θr, Θ !! o = Some (S0, x) ∧ unfoldS S0 = SSeq (SSnd m U b) S ∧
        ΘM ##ₘ Θr ∧ delete o Θ = ΘM ∪ Θr ∧ dom ΘM = M ∧
        at_cost_V n (c_give κ) Vl VN W ΘM (payload_at m U x) w ∧
        at_cost_E n (c_give κ) El X W (<[o := (S, x⁺)]> Θr) T F e'.

    Definition o_recv (o : cend) (w e' : expr) : Prop :=
      ∃ S0 x m U b S, Θ !! o = Some (S0, x) ∧ unfoldS S0 = SSeq (SRcv m U b) S ∧
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
      | LSpawn M v => o_spawn M v e'
      | LSess (SSend o M w) => o_send o M w e'
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
      (∀ M v e', tstep e (LSpawn M v) e' → o_spawn M v e') ∧          (* O-Spawn *)
      (∀ o M w e', tstep e (LSess (SSend o M w)) e' → o_send o M w e') ∧ (* O-Send *)
      (∀ o w e', tstep e (LSess (SRecv o w)) e' → o_recv o w e') ∧    (* O-Recv *)
      (∀ o e', tstep e (LSess (SClose o)) e' → o_close o e') ∧        (* O-Close *)
      (∀ o i e', tstep e (LSess (SSel o i)) e' → o_select o i e') ∧   (* O-Select *)
      (∀ o i e', tstep e (LSess (SBra o i)) e' → o_branch o i e') ∧   (* O-Branch *)
      (∀ os e', tstep e (LSess (SLink os)) e' → o_link os e').        (* O-Link *)

    Lemma Esteps_iff e : Esteps e ↔ ∀ α e', tstep e α e' → Eobl α e'.
    Proof.
      split.
      - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) α e' Hst.
        destruct α as [|ℓ c|κf o c|M v|[o M w|o w|o|o i|o i|os]]; simpl; eauto.
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
      | TSess s x => ∃ o s', v = Chan o ∧ Θ = {[o := (s', x)]} ∧ seqv s' s
      | TLolli ub lb _ _ _ T1 _ U _ =>
          Varr n Vl El (λ W' Θ' w, Vbody n Vl El k' W' Θ' T1 w)
            (λ W' Θ' F e, Etop n Vl El (Vbody n Vl El k') W' Θ' U F e) T1 U ub lb W Θ v
      | TProd T1 _ U _ =>
          ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ Θ1 ##ₘ Θ2 ∧ Θ = Θ1 ∪ Θ2 ∧
            Vbody n Vl El k' W Θ1 T1 v1 ∧ Vbody n Vl El k' W Θ2 U v2
      | TSum T1 _ U _ =>
          (∃ v', v = Inj1 v' ∧ Vbody n Vl El k' W Θ T1 v') ∨
          (∃ v', v = Inj2 v' ∧ Vbody n Vl El k' W Θ U v')
      | TBox m kk C ub _ _ U _ =>
          Θ = ∅ ∧ ∃ e, v = EBox e ∧
            ∀ W' xs ss, W ⊑ W' → length xs = m → length ss = kk → Forall hcontractive ss →
              wholds W' C xs →
              Vbody n Vl El k' W' ∅
                (tthunk (pt_inst (plist xs) <$> ub) (sinst_ty (slist ss) (ty_inst xs U))) (thunk e)
      | TEx lb m C T1 _ =>
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

    (** Q-Admin and Q-Comm: a τ step keeps the interface. *)
    Definition q_tau (ev : event) (p' : proc) : Prop :=
      p'.1 ## chans_of Σ → at_cost_P n (ev_cost κ ev) Pl X W Σ T p'.

    Definition q_send (o : cend) (M : gset cend) (w : expr) (p' : proc) : Prop :=
      ∃ S0 x m U b S Σv Σr Θe Σe, Σ !! o = Some (S0, x) ∧
        unfoldS S0 = SSeq (SSnd m U b) S ∧
        Σv ##ₘ Σr ∧ delete o Σ = Σv ∪ Σr ∧
        (∀ o', o' ∈ dom Θe ↔ o' ∈ M ∧ ech o' ∈ p.1) ∧ M = dom Σv ∪ dom Θe ∧
        send_split Σ Σe Θe ∧
        at_cost_V n (c_give κ) Vl VN W (Σv ∪ Θe) (payload_at m U x) w ∧
        at_cost_P n (c_give κ) Pl X W (<[o := (S, x⁺)]> (Σr ∪ Σe)) T p'.

    Definition q_recv (o : cend) (w : expr) (p' : proc) : Prop :=
      ∃ S0 x m U b S, Σ !! o = Some (S0, x) ∧ unfoldS S0 = SSeq (SRcv m U b) S ∧
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
      | EvSess _ (SSend o M w) => q_send o M w p'
      | EvSess _ (SRecv o w) => q_recv o w p'
      | EvSess _ (SClose o) => q_close o p'
      | EvSess _ (SSel o i) => q_select o i p'
      | EvSess _ (SBra o i) => q_branch o i p'
      | EvSess _ (SLink os) => q_link os p'
      | _ => q_tau ev p'
      end.

    (** The step clause, one conjunct per kind of step. *)
    Definition Psteps : Prop :=
      (∀ q ev q', erase q = p → istep q ev q' → ev_tau ev → q_tau ev (erase q')) ∧
      (∀ q i o M w q', erase q = p → istep q (EvSess i (SSend o M w)) q' →
         q_send o M w (erase q')) ∧                                    (* Q-Send *)
      (∀ q i o w q', erase q = p → istep q (EvSess i (SRecv o w)) q' →
         q_recv o w (erase q')) ∧                                      (* Q-Recv *)
      (∀ q i o q', erase q = p → istep q (EvSess i (SClose o)) q' →
         q_close o (erase q')) ∧                                       (* Q-Close *)
      (∀ q i o b q', erase q = p → istep q (EvSess i (SSel o b)) q' →
         q_select o b (erase q')) ∧                                    (* Q-Select *)
      (∀ q i o b q', erase q = p → istep q (EvSess i (SBra o b)) q' →
         q_branch o b (erase q')) ∧                                    (* Q-Branch *)
      (∀ q i os q', erase q = p → istep q (EvSess i (SLink os)) q' →
         q_link os (erase q')).                                        (* Q-Link *)

    Lemma Psteps_iff :
      Psteps ↔ ∀ q ev q', erase q = p → istep q ev q' → Pobl ev (erase q').
    Proof.
      split.
      - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) q ev q' Hq Hst.
        destruct ev as [| | | | | | | |i [o M w|o w|o|o b|o b|os]]; simpl;
          first [eapply H1; [exact Hq|exact Hst|reflexivity] | eauto].
      - intros H. split_and!.
        + intros q ev q' Hq Hst Hτ. specialize (H q ev q' Hq Hst).
          destruct ev; try done; by unfold ev_tau in Hτ.
        + intros q i o M w q' Hq Hst. exact (H _ _ _ Hq Hst).
        + intros q i o w q' Hq Hst. exact (H _ _ _ Hq Hst).
        + intros q i o q' Hq Hst. exact (H _ _ _ Hq Hst).
        + intros q i o b q' Hq Hst. exact (H _ _ _ Hq Hst).
        + intros q i o b q' Hq Hst. exact (H _ _ _ Hq Hst).
        + intros q i os q' Hq Hst. exact (H _ _ _ Hq Hst).
    Qed.
  End qobligations.

  (** One unfolding of P at level n, in every W1 ⊒ W. *)
  Definition Pbody (n : nat) (Vl : nat → vrel) (Pl : nat → prel) (VN : vrel) (X : prel)
      (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
    ∀ W1, W ⊑ W1 →
      (pirred p → ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ VN W1 Σ T v ∧    (* P-Stop *)
                         ∀ e, e ∈ E → e = EUnit) ∧
      (¬ pirred p → ready _ W1(Σ, p)) ∧                           (* P-Ready *)
      Psteps n Vl Pl VN X W1 Σ T p.                               (* P-Step *)

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
