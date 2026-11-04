(** * The logical relation (§7) and semantic typing

    V^W_n⟦Θ ⊢ T⟧ ([Vrel]), E^W_n⟦Θ ⊢ T ≺ F⟧ ([Erel]) and P^W_n⟦Σ ⊢ T⟧
    ([Prel]), indexed by a world W and a step index n, and [adequacy].
    Θ may hold both ends of a channel, Σ only one.

    The step index uses course-of-values recursion ([levels],
    [mk_level]). Inside a level, E and P recur on the size of the term
    or the soup through fuel ([Efuel], [Pfuel]). Later proofs use only
    [Erel_S_iff], [Prel_S_iff], [Erel_S_ind] and [Prel_S_ind].
    [proc_progress] decides reducibility, so adequacy needs no excluded
    middle. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lang.Semantics lang.Safety types.Types types.SessionEquiv relation.Worlds relation.Readiness types.LinearEnv.

(** ** Types up to aliases

    T ≈_W U: T ≈ U up to aliases of ground points in W. The constants'
    signatures are read up to it (V-Const), because a payload type
    P[x] names the points x[i] of the channel's own point x, and aliased
    points must type the same values. Points that are not ground
    (point variables, possibly bound) are compared by equality, so
    instantiating them preserves the relation. *)
Definition pt_ground (x : point) : Prop := ∃ a, pn_root (pt_name x) = NConst a.

Definition pteqW (W : world) (x y : point) : Prop :=
  x = y ∨ (pt_ground x ∧ pt_ground y ∧ w_eq W x y).

Definition opt_rel (R : point → point → Prop) (o o' : option point) : Prop :=
  match o, o' with
  | Some x, Some y => R x y
  | None, None => True
  | _, _ => False
  end.

Definition lb_rel (R : point → point → Prop) (lb lb' : lbound) : Prop :=
  match lb, lb' with
  | LPt x, LPt y => R x y
  | LTop, LTop | LBot, LBot => True
  | _, _ => False
  end.

(** Box constraints under a binder of n point variables: every fact of
    one has a fact of the other of the same kind with related points
    (sharp edges 65). *)
Definition bcs_rel (R : point → point → Prop) (n : nat) (C C' : bcs) : Prop :=
  (∀ g, bcs_open n C g → ∃ g', bcs_open n C' g' ∧ fact_rel R g g') ∧
  (∀ g', bcs_open n C' g' → ∃ g, bcs_open n C g ∧ fact_rel R g g').

Fixpoint teqW (W : world) (T U : ty) : Prop :=
  match T, U with
  | TUnit, TUnit => True
  | TLolli ub lb T1 T2, TLolli ub' lb' U1 U2 =>
      opt_rel (pteqW W) ub ub' ∧ opt_rel (pteqW W) lb lb' ∧
      teqW W T1 U1 ∧ teqW W T2 U2
  | TProd T1 T2, TProd U1 U2 => teqW W T1 U1 ∧ teqW W T2 U2
  | TSum T1 T2, TSum U1 U2 => teqW W T1 U1 ∧ teqW W T2 U2
  | TBox n C T1, TBox n' C' U1 =>
      n = n' ∧ bcs_rel (pteqW W) n C C' ∧ teqW W T1 U1

  | TSess s x, TSess r y => pteqW W x y ∧ seq s r
  | TEx lb n C T1, TEx lb' n' C' U1 =>
      lb_rel (pteqW W) lb lb' ∧ n = n' ∧ bcs_rel (pteqW W) n C C' ∧ teqW W T1 U1
  | _, _ => False
  end.

(** ** The three relations, level by level *)

Record level := Level {
  lV : world → tenv → ty → expr → Prop;
  lE : world → tenv → ty → gset point → expr → Prop;
  lP : world → senv → ty → proc → Prop
}.

(** Value relation at level n, given the family [below] of levels < n.
    Recursive on the type; lower levels are accessed through [below]
    (the ∀ j < n quantification in the ⊸ and □ cases).

    - V-Chan: the channel's current point x is an alias of the point
      the type names.
    - V-Abs: the closure holds only above its lower point
      ({λ} ≼ heads(Θ)); applied in any future world to an argument,
      it is a good term under any frame above its upper point. The
      argument's environment may hold the other ends of channels the
      closure holds ([tenv_comp]).
    - V-Const: the constant's signature is read in W, up to ≈_W.
    - V-Box / V-All: ∀ appears only under □; a box is the thunk
      λ_. fix x.e, and it is good when the thunk is in V at every
      instance of its point variables that meets its constraint C, in
      every future world (sharp edges 58, 63).
    - V-Ex: the value is in V at some known instance of the bound
      points that meets C, and its channels lie at or above the lower
      point (sharp edges 97). *)

(** The thunk a box !e stands for: applied to ∗ it unrolls once. *)
Definition thunk (eb : expr) : expr := Lam (rename S (subst1 (EBox eb) eb)).

Lemma thunk_app w eb : subst1 w (rename S (subst1 (EBox eb) eb)) = subst1 (EBox eb) eb.
Proof.
  unfold subst1 at 1. rewrite subst_rename. rewrite <-(subst_ids (subst1 _ eb)) at 2.
  by apply subst_ext.
Qed.

(** V at an arrow type. It reads the argument and the result only at
    lower levels, so V-Box can use it at an instance of its type. *)
Definition Vfun (below : nat → level) (n : nat)
    (W : world) (Θ : tenv) (T : ty) (v : expr) : Prop :=
  match T with
  | TLolli ub lb T1 U =>
      (∃ eb, v = Lam eb ∧ fchans eb = dom Θ ∧ lb_below W lb (tenv_heads Θ) ∧
         ∀ W' j Θ' Θ'' w F, wext W W' → j < n →
           tenv_comp (w_eq W') Θ'' Θ Θ' →
           lV (below j) W' Θ' T1 w →
           ub_below W' ub F →
           lE (below j) W' Θ'' U F (subst1 w eb))
      ∨ (∃ k T0, v = Konst k ∧ Θ = ∅ ∧ konst_ty (w_eq W) (w_lt W) (pt_known W) k T0 ∧
           teqW W T0 (TLolli ub lb T1 U))
  | _ => False
  end.

(** [Vdef] reads T under a point substitution σ, so that a binder
    passes its instance to its body and the definition stays structural
    (sharp edges 97). [Vrel] is [Vdef] at σ = pvar. *)
Fixpoint Vdef (below : nat → level) (n : nat)
    (W : world) (Θ : tenv) (σ : nat → point) (T : ty) (v : expr) {struct T} : Prop :=
  match T with
  | TUnit => Θ = ∅ ∧ v = EUnit
  | TSess s x =>
      ∃ c s0 k, v = Chan c ∧ Θ = {[c := One (s0, k)]} ∧ seq s0 s ∧
        w_eq W k (pt_inst σ x)
  | TLolli ub lb T1 U => Vfun below n W Θ (pinst_ty σ (TLolli ub lb T1 U)) v
  | TProd T1 U =>
      ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ tenv_comp (w_eq W) Θ Θ1 Θ2 ∧
        Vdef below n W Θ1 σ T1 v1 ∧ Vdef below n W Θ2 σ U v2
  | TSum T1 U =>
      (∃ v', v = Inj1 v' ∧ Vdef below n W Θ σ T1 v')
      ∨ (∃ v', v = Inj2 v' ∧ Vdef below n W Θ σ U v')
  | TBox m C T1 =>
      (* V of the thunk at every instance of the ∀ that meets C and
         that the world knows, in every future world (sharp edges 63) *)
      Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
        ∀ W' xs, wext W W' → length xs = m →
          bcs_hold (w_eq W') (w_lt W') (bcs_inst σ C) xs → Forall (pt_known W') xs →
          Vdef below n W' ∅ (pt_inst (plist xs) ∘ pup m σ) T1 (thunk eb)
  | TEx lb m C T1 =>
      (* V-Ex: a known instance meets C, the value lies in the body at
         it, and its channels lie at or above the lower point *)
      lbx_below W (lb_map (pt_inst σ) lb) (tenv_heads Θ) false ∧
      ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧
        bcs_hold (w_eq W) (w_lt W) (bcs_inst σ C) xs ∧
        Vdef below n W Θ (pt_inst (plist xs) ∘ pup m σ) T1 v
  end.

(** ** The cost of a step (sharp edges 45)

    Send, close and link are giving steps: they cost nothing and keep
    the index. Every other step costs one. A step taken at index n
    carries its obligation at index n − cost. *)
Definition scost (σ : slabel) : nat := match σ with SRecv _ _ => 1 | _ => 0 end.
Definition tcost (α : tlabel) : nat := match α with LSess σ => scost σ | _ => 1 end.
Definition pcost (π : plabel) : nat := match π with PSess σ => scost σ | PTau => 1 end.

(** n − c, by recursion on c, so that it computes at a variable n. *)
Fixpoint nlower (n c : nat) : nat := match c with 0 => n | S c' => pred (nlower n c') end.

(** The relation at index n − c, from the relations [low] below n and
    the relation [top] at n. *)
Definition at_cost {A} (low : nat → A) (top : A) (n c : nat) : A :=
  match c with 0 => top | S _ => low (nlower n c) end.

(** ** The size of a term and of a soup (sharp edges 46, 47)

    Every giving step shrinks the thread that takes it
    ([tstep_giving_size]), so inside one index the term and process
    relations recur on the size. *)

Fixpoint esize (e : expr) : nat :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ => 1
  | Lam e | Inj1 e | Inj2 e | EBox e => S (esize e)
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => S (esize e1 + esize e2)
  | Case e e1 e2 => S (esize e + esize e1 + esize e2)
  end.

Definition msize (E : gmultiset expr) : nat := sum_list (esize <$> elements E).

Lemma msize_disj_union E1 E2 : msize (E1 ⊎ E2) = msize E1 + msize E2.
Proof.
  unfold msize. rewrite gmultiset_elements_disj_union, fmap_app, sum_list_with_app.
  done.
Qed.

Lemma msize_singleton e : msize {[+ e +]} = esize e.
Proof. unfold msize. rewrite gmultiset_elements_singleton. simpl. lia. Qed.

Lemma esize_chsubst c d e : esize (chsubst c d e) = esize e.
Proof. induction e; simpl; lia. Qed.

Lemma msize_echsubst c d E : msize (echsubst c d E) = msize E.
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold echsubst. by rewrite gmultiset_map_empty.
  - rewrite echsubst_disj_union, echsubst_singleton, !msize_disj_union, !msize_singleton.
    by rewrite esize_chsubst, IH.
Qed.

(** Giving steps of a thread shrink it. *)
Definition giving (σ : slabel) : Prop :=
  match σ with SRecv _ _ => False | _ => True end.

Lemma tstep_giving_size e σ e' : tstep e (LSess σ) e' → giving σ → esize e' < esize e.
Proof.
  intros H Hg. remember (LSess σ) as α eqn:Hα. revert Hα.
  induction H as [e α e' Hh| | | | | | | | | ]; intros ->; simpl;
    try (specialize (IHtstep eq_refl); lia).
  inversion Hh; subst; simpl; try done; lia.
Qed.

(** A step that costs nothing shrinks the term. *)
Lemma tcost_giving α e e' : tstep e α e' → tcost α = 0 → esize e' < esize e.
Proof.
  intros Hst Hc. destruct α as [|[c w|c w|c|cd]|c|w]; try discriminate Hc;
    by apply (tstep_giving_size _ _ _ Hst).
Qed.

(** The obligation of a step e --α--> e' at index n, given the value
    and term relations below n ([Vlow], [Elow]) and at n ([Vn], [En]).
    At new, the created channel gets a point (a, 0) with a fresh for W
    and for the points of Θ, T and F, and W grows by a fresh extension
    placing a. The name c is only required to be new to Θ, so that the
    continuation environment can be formed. A link with c = d is a
    self-link: Θ holds both ends of c, and both entries leave. *)
Definition Eobl (Vlow : nat → world → tenv → ty → expr → Prop)
    (Vn : world → tenv → ty → expr → Prop)
    (Elow : nat → world → tenv → ty → gset point → expr → Prop)
    (En : world → tenv → ty → gset point → expr → Prop)
    (n : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point)
    (α : tlabel) (e' : expr) : Prop :=
  match α with
  | LBeta =>                                           (* O-Beta *)
      at_cost Elow En n (tcost α) W Θ T F e'
  | LNew c =>                                          (* O-New *)
      c ∉ dom Θ →
      ∃ a s s' W', NConst a ∉ tenv_roots Θ ∪ ty_roots T ∪ frame_roots F ∧
        sdual s s' ∧ wext_fresh W {[NConst a]} W' ∧
        at_cost Elow En n (tcost α) W'
          (<[c := Both (s, pconst a) (s', pconst a)]> Θ) T F e'
  | LSpawn w =>                                        (* O-Spawn *)
      ∃ Θ1 Θ2 ub lb, tenv_comp (w_eq W) Θ Θ1 Θ2 ∧
        Vn W Θ1 (TLolli ub lb TUnit TUnit) w ∧
        at_cost Elow En n (tcost α) W Θ2 T F e'
  | LSess (SRecv c w) =>                               (* O-Recv *)
      ∃ Θ1 m U s k,
        tenv_hd Θ c (SRcv m U s) k Θ1 ∧
        ∀ W' j Θ2 Θ1c Θ', wext W W' → j ≤ nlower n (tcost α) →
          tenv_ext Θ1 c (s, pt_shift 1 k) Θ1c →
          tenv_comp (w_eq W') Θ' Θ1c Θ2 →
          Vlow j W' Θ2 (payload_at m U k) w →
          Elow j W' Θ' T F e'
  | LSess (SSend c w) =>                               (* O-Send *)
      ∃ Θr Θ1 Θ2 m U s k Θ',
        tenv_hd Θ c (SSnd m U s) k Θr ∧ tenv_comp (w_eq W) Θr Θ1 Θ2 ∧
        Vn W Θ2 (payload_at m U k) w ∧
        tenv_ext Θ1 c (s, pt_shift 1 k) Θ' ∧
        at_cost Elow En n (tcost α) W Θ' T F e'
  | LSess (SClos c) =>                                 (* O-Close *)
      ∃ Θ1 k, tenv_hd Θ c SEnd k Θ1 ∧ at_cost Elow En n (tcost α) W Θ1 T F e'
  | LSess (SLink cd) =>                                (* O-Link *)
      ∃ c d Θ1 Θm sc sd kc kd,
        cd = {[c; d]} ∧
        tenv_ext Θ1 d (sd, kd) Θm ∧ tenv_ext Θm c (sc, kc) Θ ∧
        sdual sd sc ∧ w_eq W kc kd ∧
        at_cost Elow En n (tcost α) W Θ1 T F e'
  end.

(** Term relation at level n' + 1 with fuel k, given [below] and the
    level-(n'+1) value relation [Vn]. A term that can step must be
    ready in Θ ∣ F (one condition, sharp edges 63). A giving
    successor of e is smaller than e, so fuel above esize e does not
    matter ([Efuel_fuel]). Fuel replaces stdlib Fix, whose unfolding
    equation needs functional extensionality (sharp edges 62). *)
Fixpoint Efuel (below : nat → level) (Vn : world → tenv → ty → expr → Prop)
    (n' k : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point) (e : expr)
    : Prop :=
  (irred e → Vn W Θ T e) ∧                             (* E-Stop *)
  (¬ irred e → ready_t W Θ F e) ∧                     (* E-Step *)
  ∀ α e', tstep e α e' →
    Eobl (λ j, lV (below j)) Vn (λ j, lE (below j))
      (match k with 0 => λ _ _ _ _ _, False | S k' => Efuel below Vn n' k' end)
      (S n') W Θ T F α e'.

Definition Edef (below : nat → level) (Vn : world → tenv → ty → expr → Prop)
    (n : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point) (e : expr)
    : Prop :=
  match n with
  | 0 => True
  | S n' => Efuel below Vn n' (S (esize e)) W Θ T F e
  end.

(** ** Messages at the process level

    Q-Recv: the payload's environment Θ2 is term-level, so a message
    may carry both ends of one channel. B ([recv_back]) is the set of
    channels the receiver ends up holding both ends of: those whose
    other end it already holds, and those whose both ends arrive in
    one message. They are restricted in the continuation, because an
    interface entry of Σ holds one end only. *)

Definition tenv_ones (Θ : tenv) : senv :=
  omap (λ o, match o with One e => Some e | Both _ _ => None end) Θ.

Definition recv_back (Σr : senv) (Θ2 : tenv) : gset chan :=
  (dom Θ2 ∩ dom Σr) ∪ (dom Θ2 ∖ dom (tenv_ones Θ2)).

Definition recv_ok (W : world) (Σr : senv) (Θ2 : tenv) : Prop :=
  senv_dual_on (w_eq W) Σr (tenv_ones Θ2) ∧ tenv_dual (w_eq W) Θ2 ∧
  (dom Θ2 ∖ dom (tenv_ones Θ2)) ## dom Σr.

Definition recv_env (Σr : senv) (Θ2 : tenv) : senv :=
  (Σr ∖ tenv_ones Θ2) ∪ (tenv_ones Θ2 ∖ Σr).

(** Q-Send: the restricted channels a message carries. Θe holds the
    ends that leave with the message (one end, or both), Σe the ends
    that stay, dual at aliased points. *)
Definition send_split (W : world) (Σe : senv) (Θe : tenv) : Prop :=
  dom Σe ⊆ dom Θe ∧
  ∀ r o, Θe !! r = Some o →
    match o with
    | One e' => ∃ e, Σe !! r = Some e ∧ w_eq W e.2 e'.2 ∧ sdual e.1 e'.1
    | Both e1 e2 => Σe !! r = None ∧ w_eq W e1.2 e2.2 ∧ sdual e1.1 e2.1
    end.

Lemma send_split_mono W W' Σe Θe :
  (∀ x y, w_eq W x y → w_eq W' x y) → send_split W Σe Θe → send_split W' Σe Θe.
Proof.
  intros Hp [Hd H]. split; [done|]. intros r o Hr. specialize (H r o Hr).
  destruct o; naive_solver.
Qed.

(** The τ of P-Act-Link: a giving step (sharp edges 45). *)
Definition ptau_link (p p' : proc) : Prop :=
  ∃ C E e c d e', p = (C, E ⊎ {[+ e +]}) ∧ tstep e (LSess (SLink {[c; d]})) e' ∧
    c ∈ C ∧ p' = (C ∖ {[c]}, echsubst c d (E ⊎ {[+ e' +]})).

Definition Ptau_case (X : world → senv → ty → proc → Prop)
    (W : world) (Σ : senv) (T : ty) (p' : proc) : Prop :=
  p'.1 ## dom Σ →
  ∃ N W', N ## senv_roots Σ ∪ ty_roots T ∧ wext_fresh W N W' ∧ X W' Σ T p'.

(** A link creates no points: its τ keeps the world. *)
Definition Plinktau_case (X : world → senv → ty → proc → Prop)
    (W : world) (Σ : senv) (T : ty) (p' : proc) : Prop :=
  p'.1 ## dom Σ → X W Σ T p'.

Definition Psend_case (Vn : world → tenv → ty → expr → Prop)
    (X : world → senv → ty → proc → Prop)
    (W : world) (Σ : senv) (T : ty) (p : proc) (c : chan) (w : expr) (p' : proc)
    : Prop :=
  ∃ Σ0 Σv m U s k (Σe : senv) (Θe : tenv),
    senv_hd Σ c (SSnd m U s) k (Σ0 ∪ Σv) ∧
    Σ0 ##ₘ Σv ∧ c ∉ dom Σ0 ∧ c ∉ dom Σv ∧
    dom Θe = fchans w ∩ p.1 ∧ send_split W Σe Θe ∧
    dom Θe ## dom Σ ∧
    Vn W (tenv_of Σv ∪ Θe) (payload_at m U k) w ∧
    X W (<[c := (s, pt_shift 1 k)]> (Σ0 ∪ Σe)) T p'.

Definition Pclos_case (X : world → senv → ty → proc → Prop)
    (W : world) (Σ : senv) (T : ty) (c : chan) (p' : proc) : Prop :=
  ∃ Σ1 k, senv_hd Σ c SEnd k Σ1 ∧ c ∉ dom Σ1 ∧ X W Σ1 T p'.

(** c = d cannot reach the interface: Σ holds one end per channel. *)
Definition Plink_case (X : world → senv → ty → proc → Prop)
    (W : world) (Σ : senv) (T : ty) (cd : gset chan) (p' : proc) : Prop :=
  ∃ c d Σ1 sc sd kc kd,
    cd = {[c; d]} ∧ c ≠ d ∧
    Σ = <[c := (sc, kc)]> (<[d := (sd, kd)]> Σ1) ∧
    c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧
    sdual sd sc ∧ w_eq W kc kd ∧
    X W Σ1 T p'.

(** The giving steps of a process shrink its soup: a giving step of a
    thread, and the τ of P-Act-Link. *)
Lemma pcost_giving π p p' :
  proc_step p π p' → pcost π = 0 ∨ ptau_link p p' → msize p'.2 < msize p.2.
Proof.
  intros Hst [Hc|(C & E & e & c & d & e' & -> & Hst' & _ & ->)]; simpl.
  - destruct π as [|σ]; [discriminate Hc|].
    inversion Hst; subst; simpl. rewrite !msize_disj_union, !msize_singleton.
    destruct σ; try discriminate Hc;
      match goal with H : tstep _ (LSess _) _ |- _ => pose proof (tstep_giving_size _ _ _ H I) end; lia.
  - rewrite msize_echsubst, !msize_disj_union, !msize_singleton.
    pose proof (tstep_giving_size _ _ _ Hst' I). lia.
Qed.

(** The obligation of a process step p --π--> p' at index n, given the
    value and process relations below n ([Vlow], [Plow]) and at n ([Vn],
    [Pn]). A τ of P-Act-Link costs one as a τ, and as a giving step it
    carries in addition the obligation at n itself. *)
Definition Pobl (Vlow : nat → world → tenv → ty → expr → Prop)
    (Vn : world → tenv → ty → expr → Prop)
    (Plow : nat → world → senv → ty → proc → Prop)
    (Pn : world → senv → ty → proc → Prop)
    (n : nat) (W : world) (Σ : senv) (T : ty) (p : proc)
    (π : plabel) (p' : proc) : Prop :=
  match π with
  | PTau =>                                            (* Q-Tau *)
      Ptau_case (at_cost Plow Pn n (pcost π)) W Σ T p' ∧
      (ptau_link p p' → Plinktau_case Pn W Σ T p')
  | PSess (SRecv c w) =>                               (* Q-Recv *)
      ∃ Σ1 m U s k,
        senv_hd Σ c (SRcv m U s) k Σ1 ∧ c ∉ dom Σ1 ∧
        ∀ W' j Θ2, wext W W' → j ≤ nlower n (pcost π) → dom Θ2 ## p.1 →
          recv_ok W' (<[c := (s, pt_shift 1 k)]> Σ1) Θ2 →
          Vlow j W' Θ2 (payload_at m U k) w →
          Plow j W' (recv_env (<[c := (s, pt_shift 1 k)]> Σ1) Θ2) T
            (p'.1 ∪ recv_back (<[c := (s, pt_shift 1 k)]> Σ1) Θ2, p'.2)
  | PSess (SSend c w) =>                               (* Q-Send *)
      Psend_case Vn (at_cost Plow Pn n (pcost π)) W Σ T p c w p'
  | PSess (SClos c) =>                                 (* Q-Close *)
      Pclos_case (at_cost Plow Pn n (pcost π)) W Σ T c p'
  | PSess (SLink cd) =>                                (* Q-Link *)
      Plink_case (at_cost Plow Pn n (pcost π)) W Σ T cd p'
  end.

(** Process relation at level n' + 1 with fuel k. Every clause is
    stated for the successor itself. Differences from the term
    relation:

    - Q-Tau: the world may grow by a fresh extension, placing the
      points of channels the step creates, fresh for the points of Σ
      and T. Only successors whose restricted channels stay clear of
      Σ are constrained (configurations whose restricted names clash
      with their interface are not well formed; sharp edges 41).
      The paper's Q-Tau is W′ = W.
    - Q-Recv: received channels are not restricted names of the
      process (the same hygiene).
    - Q-Recv: channels B the receiver ends up holding both ends of
      ("migration", or both ends in one message) come back: the
      obligation is stated for the successor with B restricted, and
      their entries leave both environments. If the carrier c is in B,
      its continuation entry leaves as well.
    - Q-Send: the restricted channels the message carries,
      dom Θe = fchans w ∩ C, split into the ends that leave with the
      message (Θe, possibly both ends) and the ends that stay (Σe). *)
Fixpoint Pfuel (below : nat → level) (Vn : world → tenv → ty → expr → Prop)
    (n' k : nat) (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
  (pirred p →                                          (* P-Stop *)
    ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vn W (tenv_of Σ) T v ∧
           (∀ e, e ∈ E → e = EUnit)) ∧
  (¬ pirred p → ready_p W Σ p) ∧                       (* P-Step *)
  ∀ π p', proc_step p π p' →
    Pobl (λ j, lV (below j)) Vn (λ j, lP (below j))
      (match k with 0 => λ _ _ _ _, False | S k' => Pfuel below Vn n' k' end)
      (S n') W Σ T p π p'.

Definition Pdef (below : nat → level) (Vn : world → tenv → ty → expr → Prop)
    (n : nat) (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
  match n with
  | 0 => True
  | S n' => Pfuel below Vn n' (S (msize p.2)) W Σ T p
  end.

Definition mk_level (below : nat → level) (n : nat) : level :=
  {| lV := λ W Θ T v, Vdef below n W Θ pvar T v;
     lE := Edef below (λ W Θ T v, Vdef below n W Θ pvar T v) n;
     lP := Pdef below (λ W Θ T v, Vdef below n W Θ pvar T v) n |}.

Definition dummy_level : level :=
  {| lV := λ _ _ _ _, False; lE := λ _ _ _ _ _, False;
     lP := λ _ _ _ _, False |}.

(** [levels n j] is level j, for every j < n (garbage above). *)
Fixpoint levels (n : nat) : nat → level :=
  match n with
  | 0 => λ _, dummy_level
  | S n' => λ j, if decide (j < n') then levels n' j else mk_level (levels n') n'
  end.

Definition level_at (n : nat) : level := levels (S n) n.

Definition Vrel (n : nat) : world → tenv → ty → expr → Prop := lV (level_at n).
Definition Erel (n : nat) : world → tenv → ty → gset point → expr → Prop :=
  lE (level_at n).
Definition Prel (n : nat) : world → senv → ty → proc → Prop := lP (level_at n).

(** ** Interface to the encoding *)

Lemma level_at_eq n : level_at n = mk_level (levels n) n.
Proof. unfold level_at. simpl. by destruct (decide (n < n)); [lia|]. Qed.

Lemma levels_at n j : j < n → levels n j = level_at j.
Proof.
  revert j. induction n as [|n' IH]; intros j Hj; [lia|].
  simpl. destruct (decide (j < n')) as [H|H].
  - by apply IH.
  - assert (j = n') as -> by lia. by rewrite level_at_eq.
Qed.

Lemma Erel_0 W Θ T F e : Erel 0 W Θ T F e.
Proof. unfold Erel. rewrite level_at_eq. simpl. exact I. Qed.

Lemma Prel_0 W Σ T p : Prel 0 W Σ T p.
Proof. unfold Prel. rewrite level_at_eq. simpl. exact I. Qed.

(** Members of the value relation are values. *)
Lemma Vdef_val below n W Θ σ T v : Vdef below n W Θ σ T v → is_val v.
Proof.
  induction T in Θ, v, σ |- *; simpl.
  - by intros [_ ->].
  - by intros [(eb & -> & _ & _)|(k & T0 & -> & _)].
  - intros (v1 & v2 & Θ1 & Θ2 & -> & _ & H1 & H2).
    simpl. apply andb_True. eauto.
  - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
  - by intros (-> & eb & -> & _).
  - by intros (c & s0 & k & -> & _).
  - intros (_ & xs & _ & _ & _ & H). eauto.
Qed.

Lemma Vrel_val n W Θ T v : Vrel n W Θ T v → is_val v.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_val. Qed.

(** Values in the relation mention exactly the channels of Θ: the
    linear discipline has no weakening, so a value owns precisely the
    channels occurring in it. Tightness (⊇) is essential for the
    compositionality of outputs — a component's decomposition may not
    park a restricted channel inside a value that never mentions it,
    or the channel's end would leak out of the composite unaccounted. *)
Lemma Vdef_fchans below n W Θ σ T v :
  Vdef below n W Θ σ T v → fchans v = dom Θ.
Proof.
  induction T in Θ, v, σ |- *; simpl.
  - intros [-> ->]. simpl. by rewrite dom_empty_L.
  - intros [(eb & -> & Hsup & _)|(k & T0 & -> & -> & _)]; simpl;
      [done|by rewrite dom_empty_L].
  - intros (v1 & v2 & Θ1 & Θ2 & -> & [Hj _] & H1 & H2). simpl.
    rewrite (IHT1 _ _ _ H1), (IHT2 _ _ _ H2). by rewrite (tenv_join_dom _ _ _ Hj).
  - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
  - intros (-> & eb & -> & Hfc & _). simpl.
    rewrite Hfc. by rewrite dom_empty_L.
  - intros (c & s0 & k & -> & -> & _). simpl. by rewrite dom_singleton_L.
  - intros (_ & xs & _ & _ & _ & H). eauto.
Qed.

Lemma Vrel_fchans n W Θ T v : Vrel n W Θ T v → fchans v = dom Θ.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_fchans. Qed.

(** Values of primitive type own no channels. *)
Lemma Vdef_prim_empty below n W Θ σ T v :
  prim T → Vdef below n W Θ σ T v → Θ = ∅.
Proof.
  intros Hp. revert Θ v σ. induction Hp; simpl.
  - by intros ? ? ? [-> _].
  - intros Θ v σ (v1 & v2 & Θ1 & Θ2 & -> & [Hj _] & H1 & H2).
    rewrite (IHHp1 _ _ _ H1), (IHHp2 _ _ _ H2) in Hj.
    by apply tenv_join_empty.
  - intros Θ v σ [(v' & -> & H)|(v' & -> & H)]; eauto.
  - by intros Θ v σ (-> & _).
Qed.

Lemma Vrel_prim_empty n W Θ T v : prim T → Vrel n W Θ T v → Θ = ∅.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_prim_empty. Qed.

(** ** Characteristic equations

    Encoding-free unfoldings of the three relations: [Vrel_*_iff] per
    type constructor, [Erel_S_iff] / [Prel_S_iff] per positive step
    index (via the case predicates [Ecase] / [Pcase]). All later
    proofs go through these and never touch [levels]/[level_at]. *)

Lemma Vrel_unit_iff n W Θ v : Vrel n W Θ TUnit v ↔ Θ = ∅ ∧ v = EUnit.
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_sess_iff n W Θ s x v :
  Vrel n W Θ (TSess s x) v ↔
  ∃ c s0 k, v = Chan c ∧ Θ = {[c := One (s0, k)]} ∧ seq s0 s ∧
    w_eq W k x.
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. by rewrite tpt_inst_pvar. Qed.

Lemma Vrel_prod_iff n W Θ T U v :
  Vrel n W Θ (TProd T U) v ↔
  ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ tenv_comp (w_eq W) Θ Θ1 Θ2 ∧
    Vrel n W Θ1 T v1 ∧ Vrel n W Θ2 U v2.
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_sum_iff n W Θ T U v :
  Vrel n W Θ (TSum T U) v ↔
  (∃ v', v = Inj1 v' ∧ Vrel n W Θ T v')
  ∨ (∃ v', v = Inj2 v' ∧ Vrel n W Θ U v').
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

(** [Vdef] at σ is [Vdef] at the instance (sharp edges 97). *)
Lemma Vdef_ext below n T : ∀ W Θ σ σ' v,
  (∀ a, σ a = σ' a) → Vdef below n W Θ σ T v ↔ Vdef below n W Θ σ' T v.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | m C T1 IH | s x
                 | lb m C T1 IH]; intros W Θ σ σ' v Hs; cbn [Vdef].
  - done.
  - by rewrite (tinst_ext _ σ σ').
  - setoid_rewrite (IH1 _ _ σ σ'); [|done..]. by setoid_rewrite (IH2 _ _ σ σ').
  - setoid_rewrite (IH1 _ _ σ σ'); [|done..]. by setoid_rewrite (IH2 _ _ σ σ').
  - rewrite (tbcs_ext σ σ') by done. apply and_iff_compat_l. f_equiv. intros eb.
    do 2 apply and_iff_compat_l. 
    do 6 (apply forall_proper; intros ?). apply IH. intros a. simpl. by rewrite (tpup_ext m σ σ').
  - by rewrite (tpt_inst_ext σ σ').
  - assert (lb_map (pt_inst σ) lb = lb_map (pt_inst σ') lb) as ->
      by (apply lb_map_ext; intros; by apply tpt_inst_ext).
    rewrite (tbcs_ext σ σ') by done. apply and_iff_compat_l. f_equiv. intros xs.
    do 3 apply and_iff_compat_l. apply IH.
    intros a. simpl. by rewrite (tpup_ext m σ σ').
Qed.

Lemma Vdef_comp below n T : ∀ W Θ σ τ v,
  Vdef below n W Θ τ (pinst_ty σ T) v ↔ Vdef below n W Θ (pt_inst τ ∘ σ) T v.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | m C T1 IH | s x
                 | lb m C T1 IH]; intros W Θ σ τ v; cbn [Vdef pinst_ty].
  - done.
  - transitivity (Vfun below n W Θ (pinst_ty τ (pinst_ty σ (TLolli ub lb T1 U))) v); [done|].
    by rewrite tinst_comp.
  - setoid_rewrite IH1. by setoid_rewrite IH2.
  - setoid_rewrite IH1. by setoid_rewrite IH2.
  - rewrite tbcs_comp. apply and_iff_compat_l. f_equiv. intros eb.
    do 2 apply and_iff_compat_l. 
    do 6 (apply forall_proper; intros ?). rewrite IH. apply Vdef_ext.
    intros a. simpl. rewrite <-tpup_comp, tpt_inst_comp. done.
  - by rewrite tpt_inst_comp.
  - assert (lb_map (pt_inst τ) (lb_map (pt_inst σ) lb) = lb_map (pt_inst (pt_inst τ ∘ σ)) lb) as ->
      by (rewrite lb_map_comp; apply lb_map_ext; intros; apply tpt_inst_comp).
    rewrite tbcs_comp. apply and_iff_compat_l. f_equiv. intros xs.
    do 3 apply and_iff_compat_l. rewrite IH. apply Vdef_ext.
    intros a. simpl. rewrite <-tpup_comp, tpt_inst_comp. done.
Qed.

Lemma Vdef_inst below n W T Θ σ v :
  Vdef below n W Θ σ T v ↔ Vdef below n W Θ pvar (pinst_ty σ T) v.
Proof.
  rewrite Vdef_comp. apply Vdef_ext. intros a. simpl. by rewrite tpt_inst_pvar.
Qed.

Lemma Vdef_plist below n W Θ σ m xs T v :
  Vdef below n W Θ (pt_inst (plist xs) ∘ pup m σ) T v ↔
  Vdef below n W Θ pvar (ty_inst xs (pinst_ty (pup m σ) T)) v.
Proof. rewrite Vdef_inst. unfold ty_inst. by rewrite tinst_comp. Qed.

(** V-Box: the thunk is in V at every admissible instance. *)
Lemma Vrel_box_iff n W Θ m C T v :
  Vrel n W Θ (TBox m C T) v ↔
  Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
    ∀ W' xs, wext W W' → length xs = m →
      bcs_hold (w_eq W') (w_lt W') C xs → Forall (pt_known W') xs →
      Vrel n W' ∅ (ty_inst xs T) (thunk eb).
Proof.
  unfold Vrel. rewrite !(level_at_eq n). cbn [mk_level lV Vdef].
  rewrite tbcs_pvar. apply and_iff_compat_l. f_equiv. intros eb.
  do 2 apply and_iff_compat_l. 
  do 6 (apply forall_proper; intros ?). rewrite Vdef_plist.
  by rewrite (tinst_ext T (pup m pvar) pvar), tinst_pvar by apply tpup_pvar.
Qed.

(** V-Ex (sharp edges 97). *)
Lemma Vrel_ex_iff n W Θ lb m C T v :
  Vrel n W Θ (TEx lb m C T) v ↔
  lbx_below W lb (tenv_heads Θ) false ∧
  ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧ bcs_hold (w_eq W) (w_lt W) C xs ∧
    Vrel n W Θ (ty_inst xs T) v.
Proof.
  unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef].
  assert (lb_map (pt_inst pvar) lb = lb) as -> by (destruct lb; simpl; [done|done|by rewrite tpt_inst_pvar]).
  rewrite tbcs_pvar. apply and_iff_compat_l. f_equiv. intros xs.
  do 3 (apply and_iff_compat_l). rewrite Vdef_plist.
  by rewrite (tinst_ext T (pup m pvar) pvar), tinst_pvar by apply tpup_pvar.
Qed.

Lemma Vrel_box_empty n W Θ m C T v : Vrel n W Θ (TBox m C T) v → Θ = ∅.

Proof. intros [-> _]%Vrel_box_iff. done. Qed.

(** Values at an unlimited type own no channels. One case per
    modality; the structural rules only ever need this much. *)
Lemma Vrel_unl_empty n W Θ T v : unlimited T → Vrel n W Θ T v → Θ = ∅.
Proof. destruct T; try done. intros _. apply Vrel_box_empty. Qed.

Lemma Vrel_lolli_iff n W Θ ub lb T U v :
  Vrel n W Θ (TLolli ub lb T U) v ↔
  (∃ eb, v = Lam eb ∧ fchans eb = dom Θ ∧ lb_below W lb (tenv_heads Θ) ∧
     ∀ W' j Θ' Θ'' w F, wext W W' → j < n →
       tenv_comp (w_eq W') Θ'' Θ Θ' →
       Vrel j W' Θ' T w →
       ub_below W' ub F →
       Erel j W' Θ'' U F (subst1 w eb))
  ∨ (∃ k T0, v = Konst k ∧ Θ = ∅ ∧ konst_ty (w_eq W) (w_lt W) (pt_known W) k T0 ∧
       teqW W T0 (TLolli ub lb T U)).
Proof.
  unfold Vrel, Erel. rewrite (level_at_eq n). cbn [mk_level lV Vdef].
  rewrite tinst_pvar. cbn [Vfun].
  apply or_iff_compat_r.
  split; intros (eb & -> & Hsup & Hlb & H); exists eb; (split_and!; [done..|]);
    intros W' j Θ' Θ'' w F HW Hj Hc HV Hub.
  - rewrite <-(levels_at n j Hj). apply (H W' j Θ' Θ'' w F); auto.
    rewrite (levels_at n j Hj). exact HV.
  - rewrite (levels_at n j Hj). apply (H W' j Θ' Θ'' w F); auto.
    rewrite <-(levels_at n j Hj). exact HV.
Qed.

(** ** The obligations read at the levels

    [Ecase_gen X n'] is the obligation of a step at index S n', with X
    for the relation at S n' itself. [Ecase n'] takes X = E_{n'+1}. *)
Definition Ecase_gen (X : world → tenv → ty → gset point → expr → Prop)
    (n' : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point)
    (α : tlabel) (e' : expr) : Prop :=
  Eobl Vrel (Vrel (S n')) Erel X (S n') W Θ T F α e'.

Notation Ecase n' := (Ecase_gen (Erel (S n')) n').

Definition Pcase_gen (X : world → senv → ty → proc → Prop)
    (n' : nat) (W : world) (Σ : senv) (T : ty) (p : proc)
    (π : plabel) (p' : proc) : Prop :=
  Pobl Vrel (Vrel (S n')) Prel X (S n') W Σ T p π p'.

Notation Pcase n' := (Pcase_gen (Prel (S n')) n').

(** An obligation reads the relations below n at indices up to n, and
    the relation at n only at the successor of a giving step. *)
Lemma Eobl_mono Vl1 Vl2 V1 V2 El1 El2 E1 E2 n W Θ T F α e' :
  (∀ j W Θ T v, j ≤ n → Vl2 j W Θ T v → Vl1 j W Θ T v) →
  (∀ W Θ T v, V1 W Θ T v → V2 W Θ T v) →
  (∀ j W Θ T F, j ≤ n → El1 j W Θ T F e' → El2 j W Θ T F e') →
  (tcost α = 0 → ∀ W Θ T F, E1 W Θ T F e' → E2 W Θ T F e') →
  Eobl Vl1 V1 El1 E1 (S n) W Θ T F α e' → Eobl Vl2 V2 El2 E2 (S n) W Θ T F α e'.
Proof.
  intros HVl HV HEl HE.
  destruct α as [|[c w|c w|c|cd]|c|w]; cbn [Eobl at_cost tcost scost nlower pred] in *.
  - intros H. apply HEl; [lia|exact H].
  - intros (Θ1 & m & U & s & k & Hhd & H). exists Θ1, m, U, s, k. split; [done|].
    intros W' j Θ2 Θ1c Θ' HW Hj Hext Hc HV'.
    apply HEl; [lia|]. apply (H W' j Θ2 Θ1c Θ'); try done. apply HVl; [lia|done].
  - intros (Θr&Θ1&Θ2&m&U&s&k&Θ'&?&?&?&?&HX).
    exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; auto.
  - intros (Θ1&k&?&HX). exists Θ1, k. split; auto.
  - intros (c&d&Θ1&Θm&sc&sd&kc&kd&?&?&?&?&?&HX).
    exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; auto.
  - intros H Hc. destruct (H Hc) as (a&s&s'&W'&?&?&?&HX).
    exists a, s, s', W'. split_and!; try done. apply HEl; [lia|exact HX].
  - intros (Θ1&Θ2&ub&lb&?&?&HX). exists Θ1, Θ2, ub, lb.
    split_and!; [done|auto|apply HEl; [lia|exact HX]].
Qed.

Lemma Plinktau_case_mono (X Y : world → senv → ty → proc → Prop) W Σ T p' :
  (∀ W Σ T p, X W Σ T p → Y W Σ T p) →
  Plinktau_case X W Σ T p' → Plinktau_case Y W Σ T p'.
Proof. intros HXY H Hd. auto. Qed.

Lemma Pobl_mono Vl1 Vl2 V1 V2 Pl1 Pl2 P1 P2 n W Σ T p π p' :
  (∀ j W Θ T v, j ≤ n → Vl2 j W Θ T v → Vl1 j W Θ T v) →
  (∀ W Θ T v, V1 W Θ T v → V2 W Θ T v) →
  (∀ j W Σ T q, j ≤ n → Pl1 j W Σ T q → Pl2 j W Σ T q) →
  (pcost π = 0 ∨ ptau_link p p' → ∀ W Σ T, P1 W Σ T p' → P2 W Σ T p') →
  Pobl Vl1 V1 Pl1 P1 (S n) W Σ T p π p' → Pobl Vl2 V2 Pl2 P2 (S n) W Σ T p π p'.
Proof.
  intros HVl HV HPl HP.
  destruct π as [|[c w|c w|c|cd]]; cbn [Pobl at_cost pcost scost nlower pred] in *.
  - intros [H1 H2]. split.
    + intros Hd. destruct (H1 Hd) as (N&W'&?&?&HX). exists N, W'.
      split_and!; [done|done|]. apply HPl; [lia|exact HX].
    + intros Hl Hd. apply HP; [by right|]. exact (H2 Hl Hd).
  - intros (Σ1 & m & U & s & k & Hhd & Hc & H). exists Σ1, m, U, s, k.
    split_and!; [done|done|]. intros W' j Θ2 HW Hj Hfr Hdu HV'.
    apply HPl; [lia|]. apply (H W' j Θ2); try done. apply HVl; [lia|done].
  - intros (Σ0&Σv&m&U&s&k&Σe&Θe&?&?&?&?&?&?&?&?&HX).
    exists Σ0, Σv, m, U, s, k, Σe, Θe.
    split_and!; try done; first [apply HP; [by left|exact HX]|auto].
  - intros (Σ1&k&?&?&HX). exists Σ1, k. split_and!; try done; first [apply HP; [by left|exact HX]|auto].
  - intros (c&d&Σ1&sc&sd&kc&kd&?&?&?&?&?&?&?&HX).
    exists c, d, Σ1, sc, sd, kc, kd.
    split_and!; try done; first [apply HP; [by left|exact HX]|auto].
Qed.

Lemma Ecase_gen_mono X Y n' W Θ T F α e' :
  (∀ W Θ T F e, X W Θ T F e → Y W Θ T F e) →
  Ecase_gen X n' W Θ T F α e' → Ecase_gen Y n' W Θ T F α e'.
Proof. intros HXY. apply Eobl_mono; auto. Qed.

Lemma Pcase_gen_mono X Y n' W Σ T p π p' :
  (∀ W Σ T p, X W Σ T p → Y W Σ T p) →
  Pcase_gen X n' W Σ T p π p' → Pcase_gen Y n' W Σ T p π p'.
Proof. intros HXY. apply Pobl_mono; auto. Qed.

(** The fuel does not matter above the size. *)
Lemma Efuel_fuel below Vn n' k1 k2 W Θ T F e :
  esize e < k1 → esize e < k2 →
  Efuel below Vn n' k1 W Θ T F e → Efuel below Vn n' k2 W Θ T F e.
Proof.
  revert k2 W Θ T F e. induction k1 as [|k1 IH]; intros k2 W Θ T F e H1 H2; [lia|].
  destruct k2 as [|k2]; [lia|]. intros (Hs & Hr & Ht). split_and!; [done|done|].
  intros α e' Hst. eapply Eobl_mono; [..|exact (Ht α e' Hst)]; [done|done|done|].
  intros Hc W' Θ' T' F' HX. pose proof (tcost_giving _ _ _ Hst Hc).
  apply (IH k2); [lia|lia|exact HX].
Qed.

Lemma Pfuel_fuel below Vn n' k1 k2 W Σ T p :
  msize p.2 < k1 → msize p.2 < k2 →
  Pfuel below Vn n' k1 W Σ T p → Pfuel below Vn n' k2 W Σ T p.
Proof.
  revert k2 W Σ T p. induction k1 as [|k1 IH]; intros k2 W Σ T p H1 H2; [lia|].
  destruct k2 as [|k2]; [lia|]. intros (Hs & Hr & Ht). split_and!; [done|done|].
  intros π p' Hst. eapply Pobl_mono; [..|exact (Ht π p' Hst)]; [done|done|done|].
  intros Hc W' Σ' T' HX. pose proof (pcost_giving _ _ _ Hst Hc).
  apply (IH k2); [lia|lia|exact HX].
Qed.

Lemma Erel_S_unfold n W Θ T F e :
  Erel (S n) W Θ T F e ↔ Efuel (levels (S n)) (Vrel (S n)) n (S (esize e)) W Θ T F e.
Proof.
  unfold Erel, Vrel. rewrite (level_at_eq (S n)). cbn [mk_level lV lE Edef].
  done.
Qed.

Lemma Prel_S_unfold n W Σ T p :
  Prel (S n) W Σ T p ↔ Pfuel (levels (S n)) (Vrel (S n)) n (S (msize p.2)) W Σ T p.
Proof.
  unfold Prel, Vrel. rewrite (level_at_eq (S n)). cbn [mk_level lV lP Pdef].
  done.
Qed.

Lemma Erel_S_iff n W Θ T F e :
  Erel (S n) W Θ T F e ↔
    (irred e → Vrel (S n) W Θ T e) ∧
    (¬ irred e → ready_t W Θ F e) ∧
    (∀ α e', tstep e α e' → Ecase n W Θ T F α e').
Proof.
  rewrite Erel_S_unfold. cbn [Efuel].
  split; intros (H1 & H2 & H3); (split_and!; [done|done|]); intros α e' Hst;
    (eapply Eobl_mono; [..|exact (H3 α e' Hst)]); try done.
  - intros j W' Θ' T' v Hj HV. cbv beta. by rewrite (levels_at (S n) j) by lia.
  - intros j W' Θ' T' F' Hj HE. cbv beta in HE. by rewrite (levels_at (S n) j) in HE by lia.
  - intros Hc W' Θ' T' F' HX. pose proof (tcost_giving _ _ _ Hst Hc).
    apply Erel_S_unfold. apply (Efuel_fuel _ _ _ (esize e)); [lia|lia|exact HX].
  - intros j W' Θ' T' v Hj HV. cbv beta in HV. by rewrite (levels_at (S n) j) in HV by lia.
  - intros j W' Θ' T' F' Hj HE. cbv beta. by rewrite (levels_at (S n) j) by lia.
  - intros Hc W' Θ' T' F' HX. pose proof (tcost_giving _ _ _ Hst Hc).
    apply Erel_S_unfold in HX. apply (Efuel_fuel _ _ _ (S (esize e'))); [lia|lia|exact HX].
Qed.

Lemma Prel_S_iff n W Σ T p :
  Prel (S n) W Σ T p ↔
    (pirred p →
      ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) W (tenv_of Σ) T v ∧
             (∀ e, e ∈ E → e = EUnit)) ∧
    (¬ pirred p → ready_p W Σ p) ∧
    (∀ π p', proc_step p π p' → Pcase n W Σ T p π p').
Proof.
  rewrite Prel_S_unfold. cbn [Pfuel].
  split; intros (H1 & H2 & H3); (split_and!; [done|done|]); intros π p' Hst;
    (eapply Pobl_mono; [..|exact (H3 π p' Hst)]); try done.
  - intros j W' Θ' T' v Hj HV. cbv beta. by rewrite (levels_at (S n) j) by lia.
  - intros j W' Σ' T' q Hj HP. cbv beta in HP. by rewrite (levels_at (S n) j) in HP by lia.
  - intros Hc W' Σ' T' HX. pose proof (pcost_giving _ _ _ Hst Hc).
    apply Prel_S_unfold. apply (Pfuel_fuel _ _ _ (msize p.2)); [lia|lia|exact HX].
  - intros j W' Θ' T' v Hj HV. cbv beta in HV. by rewrite (levels_at (S n) j) in HV by lia.
  - intros j W' Σ' T' q Hj HP. cbv beta. by rewrite (levels_at (S n) j) by lia.
  - intros Hc W' Σ' T' HX. pose proof (pcost_giving _ _ _ Hst Hc).
    apply Prel_S_unfold in HX. apply (Pfuel_fuel _ _ _ (S (msize p'.2))); [lia|lia|exact HX].
Qed.

(** Induction over the giving steps at a fixed level S n, on the size
    of the term: the giving successors carry the property being
    proved. *)
Lemma Erel_S_ind n (Φ : world → tenv → ty → gset point → expr → Prop) :
  (∀ W Θ T F e,
     (irred e → Vrel (S n) W Θ T e) →
     (¬ irred e → ready_t W Θ F e) →
     (∀ α e', tstep e α e' →
        Ecase_gen (λ W Θ T F e, Erel (S n) W Θ T F e ∧ Φ W Θ T F e) n W Θ T F α e') →
     Φ W Θ T F e) →
  ∀ W Θ T F e, Erel (S n) W Θ T F e → Φ W Θ T F e.
Proof.
  intros Hind W Θ T F e. remember (esize e) as k eqn:Hk. revert W Θ T F e Hk.
  induction k as [k IH] using lt_wf_ind. intros W Θ T F e Hk HE.
  apply Erel_S_iff in HE as (H1 & H2 & H3). apply Hind; [done|done|].
  intros α e' Hst. eapply Eobl_mono; [..|exact (H3 α e' Hst)]; [done|done|done|].
  intros Hc W' Θ' T' F' HX. split; [done|].
  pose proof (tcost_giving _ _ _ Hst Hc). by apply (IH (esize e')); [lia| |].
Qed.

(** Induction over the giving steps at a fixed level S n, on the size
    of the soup. *)
Lemma Prel_S_ind n (Φ : world → senv → ty → proc → Prop) :
  (∀ W Σ T p,
     (pirred p →
       ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) W (tenv_of Σ) T v ∧
              (∀ e, e ∈ E → e = EUnit)) →
     (¬ pirred p → ready_p W Σ p) →
     (∀ π p', proc_step p π p' →
        Pcase_gen (λ W Σ T p, Prel (S n) W Σ T p ∧ Φ W Σ T p) n W Σ T p π p') →
     Φ W Σ T p) →
  ∀ W Σ T p, Prel (S n) W Σ T p → Φ W Σ T p.
Proof.
  intros Hind W Σ T p. remember (msize p.2) as k eqn:Hk. revert W Σ T p Hk.
  induction k as [k IH] using lt_wf_ind. intros W Σ T p Hk HP.
  apply Prel_S_iff in HP as (H1 & H2 & H3). apply Hind; [done|done|].
  intros π p' Hst. eapply Pobl_mono; [..|exact (H3 π p' Hst)]; [done|done|done|].
  intros Hc W' Σ' T' HX. split; [done|].
  pose proof (pcost_giving _ _ _ Hst Hc). by apply (IH (msize p'.2)); [lia| |].
Qed.

(** Convenient corollaries of the characteristic equations. *)
Lemma Prel_S_intro n W Σ T p :
  (pirred p →
    ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) W (tenv_of Σ) T v ∧
           (∀ e, e ∈ E → e = EUnit)) →
  (¬ pirred p → ready_p W Σ p) →
  (∀ π p', proc_step p π p' → Pcase n W Σ T p π p') →
  Prel (S n) W Σ T p.
Proof. intros. apply Prel_S_iff. done. Qed.

Lemma Prel_S_step n W Σ T p π p' :
  Prel (S n) W Σ T p → proc_step p π p' → Pcase n W Σ T p π p'.
Proof. intros HP Hst. apply Prel_S_iff in HP as (_ & _ & H). auto. Qed.

Lemma Erel_S_step n W Θ T F e α e' :
  Erel (S n) W Θ T F e → tstep e α e' → Ecase n W Θ T F α e'.
Proof. intros HE Hst. apply Erel_S_iff in HE as (_ & _ & H). auto. Qed.

(** TLR-VAL: values in V are in E, under any frame: a value does not
    step, so neither readiness nor the frame is asked of it. *)
Lemma Vrel_Erel n W Θ T F v : Vrel n W Θ T v → Erel n W Θ T F v.
Proof.
  intros HV. assert (is_val v) by eauto using Vrel_val.
  destruct n as [|n']; [apply Erel_0|].
  apply Erel_S_iff. split_and!.
  - by intros _.
  - intros Hirr. exfalso. by apply Hirr, val_irred.
  - intros α e' Hst. exfalso. eauto using val_no_tstep.
Qed.

(** Terminated shape of irreducible related processes. *)
Lemma Prel_S_irred n W Σ T p :
  Prel (S n) W Σ T p → pirred p →
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) W (tenv_of Σ) T v ∧
         (∀ e, e ∈ E → e = EUnit).
Proof. intros (H1 & _)%Prel_S_iff Hirr. exact (H1 Hirr). Qed.

(** Every τ step lowers the index by at most one and may grow the
    world by a fresh extension. *)
Lemma Prel_S_tau n W Σ T p p' :
  Prel (S n) W Σ T p → preduction p p' → p'.1 ## dom Σ →
  ∃ N W', N ## senv_roots Σ ∪ ty_roots T ∧ wext_fresh W N W' ∧ Prel n W' Σ T p'.
Proof.
  intros HP Hred Hd. pose proof (Prel_S_step _ _ _ _ _ _ _ HP Hred) as [H _].
  exact (H Hd).
Qed.

(** With an empty session environment, no session-labelled transition
    is allowed by the relation. *)
Lemma Prel_S_empty_no_sess n W T p σ p' :
  Prel (S n) W ∅ T p → proc_step p (PSess σ) p' → False.
Proof.
  intros HP Hp. pose proof (Prel_S_step _ _ _ _ _ _ _ HP Hp) as Hstep.
  destruct σ as [c w|c w|c|cd]; simpl in Hstep.
  - destruct Hstep as (Σ1 & m & U & s & k & Heq & _).
    exact (senv_hd_not_empty _ _ _ _ Heq).
  - destruct Hstep as (?&?&?&?&?&?&?&?&Heq&_).
    exact (senv_hd_not_empty _ _ _ _ Heq).
  - destruct Hstep as (Σ1 & k & Heq & _).
    exact (senv_hd_not_empty _ _ _ _ Heq).
  - (* link: both ends must be in Σ *)
    destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd & _ & _ & Heq & _).
    exact (insert_non_empty _ _ _ (eq_sym Heq)).
Qed.

(** ** Semantic judgments (Defs. 3.2 and 3.3) *)

(** Grounding substitutions G^W_n⟦Θ; Δ⟧: substitutions assigning to
    each available variable of Δ a value in the value relation,
    splitting Θ among them. *)
Fixpoint grounding (n : nat) (W : world) (Θ : tenv) (Δ : lenv)
    (γ : nat → expr) : Prop :=
  match Δ with
  | [] => Θ = ∅
  | None :: Δ' => grounding n W Θ Δ' (γ ∘ S)
  | Some T :: Δ' =>
      ∃ Θ1 Θ2, tenv_comp (w_eq W) Θ Θ1 Θ2 ∧ Vrel n W Θ1 T (γ 0) ∧
               grounding n W Θ2 Δ' (γ ∘ S)
  end.

(** Free variables available in Δ: x is bound to a [Some] entry. *)
Definition lenv_avail (Δ : lenv) (x : nat) : Prop :=
  ∃ T, Δ !! x = Some (Some T).

(** Availability at a linear (non-unlimited) type: the variables
    constrained by relevance — unlimited variables may be discarded
    (weakening), so only linear availability forces occurrence. *)
Definition lenv_avail_lin (Δ : lenv) (x : nat) : Prop :=
  ∃ T, Δ !! x = Some (Some T) ∧ ¬ unlimited T.

Lemma lenv_avail_lin_avail Δ x :
  lenv_avail_lin Δ x → lenv_avail Δ x.
Proof. intros (T & ? & _). by exists T. Qed.

(** Syntactic well-formedness of e against Θ; Δ: the channels of e are
    exactly dom Θ, the free variables of e are available in Δ, and —
    relevance, i.e. absence of weakening — every linearly available
    variable of Δ occurs in e.

    None of this is part of the semantic judgment below. It is a
    separate, purely syntactic predicate, established once and for all
    for syntactically typed terms ([typed_term_wf_s]) and consumed
    as an explicit premise by exactly the two rules that build a
    suspended computation, whose V-clauses demand channel ownership:
    E-Abs needs all three (the ⊸-clause asks for [fchans eb = dom Θ],
    ⊆ from the first two, ⊇ from relevance) and E-Box needs the first
    two (the □-clause asks for [fchans eb = ∅]; relevance is vacuous
    there, the environment being unlimited). The elimination rules
    need none of it: E constrains environments, not term channels. *)
Definition term_wf (Θ : tenv) (Δ : lenv) (e : expr) : Prop :=
  fchans e = dom Θ ∧
  allfv (lenv_avail Δ) e ∧
  (∀ x, lenv_avail_lin Δ x → freevar x e).

Lemma tenv_comp_empty_r (peq : point → point → Prop) Θ : tenv_comp peq Θ Θ ∅.
Proof.
  split; [|intros c e1 e2 _ H; by rewrite lookup_empty in H].
  intros c. rewrite lookup_empty. destruct (Θ !! c); constructor.
Qed.

Lemma tenv_comp_empty_r_inv (peq : point → point → Prop) Θ Θ1 : tenv_comp peq Θ Θ1 ∅ → Θ = Θ1.
Proof.
  intros [Hj _]. apply map_eq. intros c. specialize (Hj c). rewrite lookup_empty in Hj.
  by inversion Hj.
Qed.

(** Θ; Δ ⊨^F_W e : T.  In every future world, the channels of e itself
    are covered by Θ; the grounding substitution brings its own Θ',
    composed with Θ (Θ'' = Θ, Θ'). The two may overlap in dual ends at
    aliased points, because a bound variable may hold the other end of
    a channel of Θ (sharp edges 50). F is the frame, and F = ∅ is the
    paper's judgment (Def. 3.3) plus readiness.

    The judgment is purely semantic: it says nothing about the syntax
    of e beyond what Erel says about its behaviour. The syntactic
    side conditions live in [term_wf] and enter as premises exactly
    where Fig. 4's proofs consume them. *)
Definition sem_typed (W : world) (Θ : tenv) (Δ : lenv) (F : gset point)
    (e : expr) (T : ty) : Prop :=
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ Θ' →
    grounding n W' Θ' Δ γ → Erel n W' Θ'' T F (subst γ e).

(** Σ ⊨_W p : T *)
Definition sem_ptyped (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ n, Prel n W Σ T p.

(** ** The adequacy chain (Lemmas 3.4, 3.5 and Theorem 3.6) *)

(** Lemma 3.4, for the closed environment: the last state of a run is
    related in some world. *)
Lemma Prel_steps m : ∀ W n T p p',
  nsteps preduction m p p' → Prel (m + n) W ∅ T p →
  ∃ W', Prel n W' ∅ T p'.
Proof.
  induction m as [|m IH]; intros W n T p p' Hrun HP.
  { inversion Hrun; subst. by exists W. }
  inversion Hrun as [|? ? q ? Hpq Hqr]; subst. simpl in HP.
  destruct (Prel_S_tau _ _ _ _ _ _ HP Hpq) as (N & W' & _ & _ & HP');
    [rewrite dom_empty_L; apply disjoint_empty_r|].
  exact (IH W' n T q p' Hqr HP').
Qed.

(** Lemma 3.5 *)
Lemma Prel_safe n W T p : Prel (S n) W ∅ T p → safe p.
Proof.
  intros HP. destruct (proc_progress p) as [Hirr|(π & p' & Hst)].
  - left. destruct (Prel_S_irred _ _ _ _ _ HP Hirr) as (v & E & -> & Hv & _ & HE).
    exists v, E. auto.
  - right. destruct π as [|σ].
    + by exists p'.
    + exfalso. by eapply Prel_S_empty_no_sess.
Qed.

(** Theorem 3.6 (Adequacy). *)
Theorem adequacy W T p : sem_ptyped W ∅ p T → deadlock_free p.
Proof.
  intros HP p' Hsteps. apply rtc_nsteps_1 in Hsteps as [m Hm].
  destruct (Prel_steps m W 1 T p p' Hm) as (W' & HPr);
    [by rewrite Nat.add_1_r|].
  by eapply (Prel_safe 0).
Qed.

(** ** Downward closure (Lemma 3.7) *)

Lemma Vrel_down_lolli n m W Θ ub lb T U v :
  m ≤ n → Vrel n W Θ (TLolli ub lb T U) v → Vrel m W Θ (TLolli ub lb T U) v.
Proof.
  intros Hle. rewrite !Vrel_lolli_iff.
  intros [(eb & -> & Hsup & Hlb & H)|Hk]; [left|by right].
  exists eb. split_and!; [done..|].
  intros W' j Θ' Θ'' w F HW Hj Hc HV Hub.
  apply (H W' j Θ' Θ'' w F); auto. lia.
Qed.

Lemma Vrel_down n m W Θ T v : m ≤ n → Vrel n W Θ T v → Vrel m W Θ T v.
Proof.
  intros Hle. induction T as [|ub lb T1 IH1 U IH2|T1 IH1 U IH2|T1 IH1 U IH2|m0 C T1 IH|s x
                             |lb m0 C T1 IH] in W, Θ, v |- * using ty_ind_ex.
  - rewrite !Vrel_unit_iff. done.
  - by apply Vrel_down_lolli.
  - rewrite !Vrel_prod_iff.
    intros (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2).
    eexists _, _, _, _. split_and!; eauto.
  - rewrite !Vrel_sum_iff.
    intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
  - rewrite !Vrel_box_iff.
    intros (-> & eb & -> & Hfc & H). split; [done|].
    exists eb. split_and!; [done|done|]. intros W' xs HW Hxs HC HK.
    apply IH. by apply H.
  - rewrite !Vrel_sess_iff. done.
  - rewrite !Vrel_ex_iff. intros [Hlb (xs & Hxs & HK & HC & HV)].
    split; [done|]. exists xs. split_and!; [done..|]. by apply IH.
Qed.

Lemma Erel_down n m W Θ T F e :
  m ≤ n → Erel n W Θ T F e → Erel m W Θ T F e.
Proof.
  revert n W Θ T F e. induction m as [|m' IH]; intros n W Θ T F e Hle HE;
    [apply Erel_0|].
  destruct n as [|n']; [lia|].
  revert W Θ T F e HE. apply Erel_S_ind. intros W Θ T F e H1 Hr H2.
  apply Erel_S_iff. split_and!.
  - intros He. eapply Vrel_down; [|by apply H1]. lia.
  - done.
  - intros α e' Hst. specialize (H2 α e' Hst).
    destruct α as [|[c w|c w|c|cd]|c|w]; simpl in H2 |- *.
    + eapply IH; [|exact H2]. lia.
    + destruct H2 as (Θ1 & m & U & s & k & Hhd & H2).
      eexists _, _, _, _, _. split; [done|].
      intros W' j Θ2 Θ1c Θ' HW Hj Hext Hc HV. apply (H2 W' j Θ2 Θ1c Θ'); auto. lia.
    + destruct H2 as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                      Hhd & Hc & HV & Hext & HE').
      eexists _, _, _, _, _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * exact (proj2 HE').
    + destruct H2 as (Θ1 & k & Hhd & HE').
      eexists _, _. split; [done|]. exact (proj2 HE').
    + destruct H2 as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                      -> & ? & ? & ? & ? & HE').
      eexists _, _, _, _, _, _, _, _. split_and!; [done..|]. exact (proj2 HE').
    + intros Hc. destruct (H2 Hc) as (a & s & s' & W' & ? & ? & ? & HE').
      eexists _, _, _, _. split_and!; [done|done|done|]. eapply IH; [|done]. lia.
    + destruct H2 as (Θ1 & Θ2 & ub & lb & ? & HV & HE').
      eexists _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * eapply IH; [|done]. lia.
Qed.

Lemma Prel_down n m W Σ T p : m ≤ n → Prel n W Σ T p → Prel m W Σ T p.
Proof.
  revert n W Σ T p. induction m as [|m' IH]; intros n W Σ T p Hle HP;
    [apply Prel_0|].
  destruct n as [|n']; [lia|].
  revert W Σ T p HP. apply Prel_S_ind. intros W Σ T p H1 Hr H2.
  apply Prel_S_iff. split_and!.
  - intros Hirr. destruct (H1 Hirr) as (v & E & -> & ? & HV & ?).
    eexists _, _. split_and!; eauto. eapply Vrel_down; [|exact HV]. lia.
  - done.
  - intros π p' Hst. specialize (H2 π p' Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in H2 |- *.
    + destruct H2 as [H2 Hl]. split.
      * intros Hd. destruct (H2 Hd) as (N & W' & ? & ? & ?).
        exists N, W'. split_and!; [done|done|]. eapply IH; [|done]. lia.
      * intros Hlk. eapply Plinktau_case_mono; [|exact (Hl Hlk)]. by intros ? ? ? ? [_ ?].
    + destruct H2 as (Σ1 & m & U & s & k & Hhd & Hc & H2).
      eexists _, _, _, _, _. split_and!; [done|done|].
      intros W' j Θ2 HW Hj Hfr Hdu HV. apply (H2 W' j Θ2); auto. lia.
    + destruct H2 as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd &
                      ? & ? & ? & ? & ? & ? & HV & HP0).
      eexists _, _, _, _, _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * exact (proj2 HP0).
    + destruct H2 as (Σ1 & k & Hhd & ? & HP').
      eexists _, _. split_and!; eauto. exact (proj2 HP').
    + destruct H2 as (c & d & Σ1 & sc & sd & kc & kd &
                      -> & ? & -> & ? & ? & ? & ? & HP').
      eexists _, _, _, _, _, _, _. split_and!; [done..|]. exact (proj2 HP').
Qed.

(** V-Box at a thunk type ∗ ⊸^u_⊤ T, read as the box of sharp edge 52:
    the unrolled body is in E at every lower index, admissible instance
    and frame above the instantiated upper point. *)
Lemma Vrel_box_thunk_iff n W Θ m C ub T v :
  Vrel n W Θ (TBox m C (TLolli ub None TUnit T)) v ↔
  Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
    ∀ W' j xs F, wext W W' → j < n → length xs = m →
      bcs_hold (w_eq W') (w_lt W') C xs → Forall (pt_known W') xs →
      ub_below W' (pt_inst (plist xs) <$> ub) F →
      Erel j W' ∅ (ty_inst xs T) F (subst1 (EBox eb) eb).
Proof.
  rewrite Vrel_box_iff. apply and_iff_compat_l.
  split; intros (eb & -> & Hfc & H); exists eb; (split_and!; [done..|]).
  - intros W' j xs F HW Hj Hxs HC HK HF.
    specialize (H W' xs HW Hxs HC HK). cbn in H.
    apply Vrel_lolli_iff in H as [(eb' & Heb & _ & _ & H)|(? & ? & ? & _)]; [|done].
    injection Heb as <-. rewrite <-(thunk_app EUnit eb).
    apply (H W' j ∅ ∅ EUnit F); [apply wext_refl, HW|done|apply tenv_comp_empty_r|
      by apply Vrel_unit_iff|done].
  - intros W' xs HW Hxs HC HK. cbn. apply Vrel_lolli_iff. left.
    exists (rename S (subst1 (EBox eb) eb)). split; [done|]. split; [|split].
    + rewrite fchans_rename, dom_empty_L. apply set_eq. intros c. split; [|set_solver].
      intros Hc%fchans_subst1_sub. simpl in Hc. set_solver.
    + simpl. unfold tenv_heads. by rewrite map_fold_empty.
    + intros W'' j Θ' Θ'' w F HW' Hj Hc HV HF.
      apply Vrel_unit_iff in HV as [-> ->]. apply tenv_comp_empty_r_inv in Hc as ->.
      rewrite thunk_app. apply H; [by eapply wext_trans|done|done| | |done].
      * eapply bcs_hold_mono; [| |exact HC]; apply HW'.
      * eapply Forall_impl; [exact HK|]. intros x Hx. apply HW', Hx.
Qed.

