(** * The live logical relation (docs/extensions/liveness.md)

    V^W_n, E^W_n and P^W_n as in relation/LogicalRelation.v, with other
    costs. Every channel step costs one index step, send, select, close
    and link included. A synchronization of two threads costs two. Every
    τ (β, new, spawn) costs nothing and is read inductively: inside a
    level, E and P are least fixpoints over τ steps ([Eind], [Pind]).
    The index therefore counts observations, and inside every prefix of
    n observations no infinite τ sequence exists.

    The arrow reads its argument and its body at every j ≤ n, the
    current level included, so a β is free (Tait). Every payload is read
    one level down, so E at level n reads V at level n only at the type
    of its own term and at ∗ ⊸ ∗ (spawn, inlined). V recurs on [tsize]
    with fuel, because the box reads the arrow at an instance of its
    body, which keeps the size but is not a subterm.

    The premises of [Eind] and [Pind] hold in every future world (Kripke
    style, liveness.md §4). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export relation.LogicalRelation.

Local Set Warnings "-register-all".

(** ** Sizes of types *)

Fixpoint tsize (T : ty) : nat :=
  match T with
  | TUnit | TSess _ _ => 1
  | TLolli _ _ T1 U | TProd T1 U | TSum T1 U => S (tsize T1 + tsize U)
  | TBox _ _ _ T1 | TEx _ _ _ T1 => S (tsize T1)
  end.

Lemma tsize_pos T : 0 < tsize T.
Proof. destruct T; simpl; lia. Qed.

Lemma tsize_pinst σ T : tsize (pinst_ty σ T) = tsize T.
Proof. induction T in σ |- *; simpl; auto. Qed.

Lemma tsize_sinst σ T : tsize (sinst_ty σ T) = tsize T.
Proof. induction T in σ |- *; simpl; auto. Qed.

(** ** Future worlds, reflexively *)

Definition wext_r (W W' : world) : Prop := W' = W ∨ wext W W'.

Lemma wext_r_refl W : wext_r W W.
Proof. by left. Qed.

Lemma wext_r_trans W1 W2 W3 : wext_r W1 W2 → wext_r W2 W3 → wext_r W1 W3.
Proof.
  intros [->|H1] [->|H2]; [by left|by right|by right|right; by eapply wext_trans].
Qed.

Lemma wext_wext_r W W' : wext W W' → wext_r W W'.
Proof. by right. Qed.

(** ** Process τ steps, classified

    [padmin]: the τ of P-Act-Beta, P-Act-New and P-Act-Spawn, which cost
    nothing. [pcomm]: the τ of P-Act-Msg, P-Act-Close and P-Act-Choice,
    which cost two. [ptau_link]: the τ of P-Act-Link, which costs one.
    [pchan] is a channel step of a process: [pcomm] or [ptau_link]. *)

Inductive padmin : proc → proc → Prop :=
  | PABeta C E e e' :
      tstep e LBeta e' → padmin (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]})
  | PANew C E e c e' :
      tstep e (LNew c) e' → c ∉ C → c ∉ echans E → c ∉ fchans e →
      padmin (C, E ⊎ {[+ e +]}) (C ∪ {[c]}, E ⊎ {[+ e' +]})
  | PASpawn C E e v e' :
      tstep e (LSpawn v) e' →
      padmin (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}).

Inductive pcomm : proc → proc → Prop :=
  | PCMsg C E c v e e' f f' :
      tstep e (LSess (SSend c v)) e' → tstep f (LSess (SRecv c v)) f' →
      pcomm (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PCClose C E c e e' f f' :
      tstep e (LSess (SClos c)) e' → tstep f (LSess (SClos c)) f' → c ∈ C →
      pcomm (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C ∖ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PCChoice C E c b e e' f f' :
      tstep e (LSess (SSel c b)) e' → tstep f (LSess (SBra c b)) f' →
      pcomm (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]}).

Definition pchan (p p' : proc) : Prop := pcomm p p' ∨ ptau_link p p'.

Lemma ptau_classify p p' : proc_step p PTau p' ↔ padmin p p' ∨ pchan p p'.
Proof.
  split.
  - inversion 1; subst.
    + left. by econstructor.
    + left. by econstructor.
    + left. by econstructor.
    + right. left. by econstructor.
    + right. left. by econstructor.
    + right. left. by econstructor.
    + right. right. eexists _, _, _, _, _, _. done.
  - intros [Ha|[Hc|(C & E & e & c & d & e' & -> & Hst & HC & ->)]].
    + destruct Ha; by econstructor.
    + destruct Hc; by econstructor.
    + by econstructor.
Qed.

Lemma padmin_step p p' : padmin p p' → preduction p p'.
Proof. intros H. apply ptau_classify. by left. Qed.

Lemma pchan_step p p' : pchan p p' → preduction p p'.
Proof. intros H. apply ptau_classify. by right. Qed.

(** ** Levels *)

Record llevel := LLevel {
  lvV : world → tenv → ty → expr → Prop;
  lvE : world → tenv → ty → gset point → expr → Prop;
  lvP : world → senv → ty → proc → Prop
}.

(** ** Obligations of channel steps, all one level down *)

(** The six session labels of a thread. The payload of a send is read at
    n − 1, the index of the continuation. *)
Definition LEobl (Vlow : nat → world → tenv → ty → expr → Prop)
    (Elow : nat → world → tenv → ty → gset point → expr → Prop)
    (n : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point)
    (σ : slabel) (e' : expr) : Prop :=
  match σ with
  | SRecv c w =>                                       (* O-Recv *)
      ∃ Θ1 m U s k,
        tenv_hd Θ c (SSeq (SRcv m U) s) k Θ1 ∧
        ∀ W' j Θ2 Θ1c Θ', wext W W' → j ≤ pred n →
          tenv_ext Θ1 c (s, pt_shift 1 k) Θ1c →
          tenv_comp (w_eq W') Θ' Θ1c Θ2 →
          Vlow j W' Θ2 (payload_at m U k) w →
          Elow j W' Θ' T F e'
  | SSend c w =>                                       (* O-Send *)
      ∃ Θr Θ1 Θ2 m U s k Θ',
        tenv_hd Θ c (SSeq (SSnd m U) s) k Θr ∧ tenv_comp (w_eq W) Θr Θ1 Θ2 ∧
        Vlow (pred n) W Θ2 (payload_at m U k) w ∧
        tenv_ext Θ1 c (s, pt_shift 1 k) Θ' ∧
        Elow (pred n) W Θ' T F e'
  | SClos c =>                                         (* O-Close *)
      ∃ Θ1 k, tenv_hd Θ c SEnd k Θ1 ∧ Elow (pred n) W Θ1 T F e'
  | SLink cd =>                                        (* O-Link *)
      ∃ c d Θ1 Θm sc sd kc kd,
        cd = {[c; d]} ∧
        tenv_ext Θ1 d (sd, kd) Θm ∧ tenv_ext Θm c (sc, kc) Θ ∧
        sdual sd sc ∧ w_eq W kc (pt_dual kd) ∧
        Elow (pred n) W Θ1 T F e'
  | SSel c b =>                                        (* O-Select *)
      ∃ Θr s1 s2 k Θ', tenv_hd Θ c (SPlus s1 s2) k Θr ∧
        tenv_ext Θr c (sbranch b s1 s2, sel_pt k b) Θ' ∧
        Elow (pred n) W Θ' T F e'
  | SBra c b =>                                        (* O-Branch *)
      ∃ Θr s1 s2 k Θ', tenv_hd Θ c (SWith s1 s2) k Θr ∧
        tenv_ext Θr c (sbranch b s1 s2, bra_pt k b) Θ' ∧
        Elow (pred n) W Θ' T F e'
  end.

(** The session labels of a process, each at cost one. *)
Definition LPobl (Vlow : nat → world → tenv → ty → expr → Prop)
    (Plow : nat → world → senv → ty → proc → Prop)
    (n : nat) (W : world) (Σ : senv) (T : ty) (p : proc)
    (σ : slabel) (p' : proc) : Prop :=
  match σ with
  | SRecv c w =>                                       (* Q-Recv *)
      ∃ Σ1 m U s k,
        senv_hd Σ c (SSeq (SRcv m U) s) k Σ1 ∧ c ∉ dom Σ1 ∧
        ∀ W' j Θ2, wext W W' → j ≤ pred n → dom Θ2 ## p.1 →
          recv_ok W' (<[c := (s, pt_shift 1 k)]> Σ1) Θ2 →
          Vlow j W' Θ2 (payload_at m U k) w →
          Plow j W' (recv_env (<[c := (s, pt_shift 1 k)]> Σ1) Θ2) T
            (p'.1 ∪ recv_back (<[c := (s, pt_shift 1 k)]> Σ1) Θ2, p'.2)
  | SSend c w =>                                       (* Q-Send *)
      Psend_case (Vlow (pred n)) (Plow (pred n)) W Σ T p c w p'
  | SClos c =>                                         (* Q-Close *)
      Pclos_case (Plow (pred n)) W Σ T c p'
  | SLink cd =>                                        (* Q-Link *)
      Plink_case (Plow (pred n)) W Σ T cd p'
  | SSel c b =>                                        (* Q-Select *)
      Pchoice_case (Plow (pred n)) W Σ T c b SPlus sel_pt p'
  | SBra c b =>                                        (* Q-Branch *)
      Pchoice_case (Plow (pred n)) W Σ T c b SWith bra_pt p'
  end.

(** ** The spawned closure

    V at ∗ ⊸ ∗ at level n, with E at level n given as [Etop]. The
    spawned thread is read in the parent's derivation, so its τ steps
    before its first channel step belong to the parent's fixpoint. *)
Definition Vspawn (Vlow : nat → world → tenv → ty → expr → Prop)
    (Elow : nat → world → tenv → ty → gset point → expr → Prop)
    (Etop : world → tenv → gset point → expr → Prop)
    (n : nat) (W : world) (Θ : tenv) (ub lb : option point) (w : expr) : Prop :=
  (∃ eb, w = Lam eb ∧ fchans eb = dom Θ ∧ lb_below W lb (tenv_heads Θ) ∧
     ∀ W' j Θ' Θ'' w' F, wext W W' → j ≤ n →
       tenv_comp (w_eq W') Θ'' Θ Θ' → ub_below W' ub F →
       (j < n → Vlow j W' Θ' TUnit w' → Elow j W' Θ'' TUnit F (subst1 w' eb)) ∧
       (j = n → Θ' = ∅ → w' = EUnit → Etop W' Θ'' F (subst1 w' eb)))
  ∨ (∃ k T0, w = Konst k ∧ Θ = ∅ ∧ konst_ty (w_eq W) (w_lt W) (pt_known W) k T0 ∧
       teqW W T0 (TLolli ub lb TUnit TUnit)).

(** ** The term relation at level n

    [Ebody X] is one unfolding, with X for the relation at level n
    itself. VT is V at level n for the type T of the term. Both are
    indices of X, because the spawned thread is read at ∗. *)
Definition Vunit_top : world → tenv → expr → Prop := λ _ Θ v, Θ = ∅ ∧ v = EUnit.

Definition Ebody (below : nat → llevel) (n : nat)
    (X : (world → tenv → expr → Prop) → ty → world → tenv → gset point → expr → Prop)
    (VT : world → tenv → expr → Prop) (T : ty)
    (W : world) (Θ : tenv) (F : gset point) (e : expr) : Prop :=
  ∀ W1, wext_r W W1 →
    (irred e → VT W1 Θ e) ∧                                        (* E-Stop *)
    (¬ irred e → ready_t W1 Θ F e) ∧                              (* E-Step *)
    (∀ e', tstep e LBeta e' → X VT T W1 Θ F e') ∧                  (* O-Beta *)
    (∀ c e', tstep e (LNew c) e' → c ∉ dom Θ →                    (* O-New *)
       ∃ a s s' W', NConst a ∉ tenv_roots Θ ∪ ty_roots T ∪ future_roots F ∧
         sdual s s' ∧ wext_fresh W1 {[NConst a]} W' ∧
         X VT T W' (<[c := Both (s, pconst a) (s', pt_dual (pconst a))]> Θ) F e') ∧
    (∀ w e', tstep e (LSpawn w) e' →                               (* O-Spawn *)
       ∃ Θ1 Θ2 ub lb, tenv_comp (w_eq W1) Θ Θ1 Θ2 ∧
         Vspawn (λ j, lvV (below j)) (λ j, lvE (below j))
           (X Vunit_top TUnit) n W1 Θ1 ub lb w ∧
         X VT T W1 Θ2 F e') ∧
    (∀ σ e', tstep e (LSess σ) e' →                                 (* O-σ *)
       LEobl (λ j, lvV (below j)) (λ j, lvE (below j)) n W1 Θ T F σ e').

Inductive Eind (below : nat → llevel) (n : nat) :
    (world → tenv → expr → Prop) → ty → world → tenv → gset point → expr → Prop :=
  | EIntro VT T W Θ F e :
      Ebody below n (Eind below n) VT T W Θ F e → Eind below n VT T W Θ F e.

(** ** The process relation at level n *)
Definition Pbody (below : nat → llevel) (n : nat)
    (VT : world → tenv → expr → Prop) (T : ty)
    (X : world → senv → proc → Prop) (W : world) (Σ : senv) (p : proc) : Prop :=
  ∀ W1, wext_r W W1 →
    (pirred p →                                                    (* P-Stop *)
      ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ VT W1 (tenv_of Σ) v ∧
             (∀ e, e ∈ E → e = EUnit)) ∧
    (¬ pirred p → ready_p W1 Σ p) ∧                                 (* P-Step *)
    (∀ p', padmin p p' → p'.1 ## dom Σ →                           (* Q-Admin *)
       ∃ N W', N ## senv_roots Σ ∪ ty_roots T ∧ wext_fresh W1 N W' ∧ X W' Σ p') ∧
    (∀ p', pcomm p p' →                                            (* Q-Comm *)
       Ptau_case (lvP (below (pred (pred n)))) W1 Σ T p') ∧
    (∀ p', ptau_link p p' →                                        (* Q-Link-τ *)
       Ptau_case (lvP (below (pred n))) W1 Σ T p') ∧
    (∀ σ p', proc_step p (PSess σ) p' →                             (* Q-σ *)
       LPobl (λ j, lvV (below j)) (λ j, lvP (below j)) n W1 Σ T p σ p').

Inductive Pind (below : nat → llevel) (n : nat)
    (VT : world → tenv → expr → Prop) (T : ty) : world → senv → proc → Prop :=
  | PIntro W Σ p : Pbody below n VT T (Pind below n VT T) W Σ p → Pind below n VT T W Σ p.

(** Level 0 holds every term and every process. *)
Definition Etop (below : nat → llevel) (n : nat)
    (VT : world → tenv → expr → Prop) (T : ty)
    (W : world) (Θ : tenv) (F : gset point) (e : expr) : Prop :=
  match n with 0 => True | S _ => Eind below n VT T W Θ F e end.

Definition Ptop (below : nat → llevel) (n : nat)
    (VT : world → tenv → expr → Prop) (T : ty)
    (W : world) (Σ : senv) (p : proc) : Prop :=
  match n with 0 => True | S _ => Pind below n VT T W Σ p end.

(** ** The value relation at level n, by fuel on [tsize]

    As [Vdef] except the arrow, which reads the argument and the body at
    the lower levels j < n and, through [Etop], at n itself. *)
Fixpoint LVdef (below : nat → llevel) (n k : nat)
    (W : world) (Θ : tenv) (σ : nat → point) (T : ty) (v : expr) {struct k} : Prop :=
  match k with
  | 0 => False
  | S k' =>
    match T with
    | TUnit => Θ = ∅ ∧ v = EUnit
    | TSess s x =>
        ∃ c s0 kk, v = Chan c ∧ Θ = {[c := One (s0, kk)]} ∧ seq s0 s ∧
          w_eq W kk (pt_inst σ x)
    | TLolli ub lb T1 U =>
        (∃ eb, v = Lam eb ∧ fchans eb = dom Θ ∧
           lb_below W (pt_inst σ <$> lb) (tenv_heads Θ) ∧
           ∀ W' j Θ' Θ'' w F, wext W W' → j ≤ n →
             tenv_comp (w_eq W') Θ'' Θ Θ' → ub_below W' (pt_inst σ <$> ub) F →
             (j < n → lvV (below j) W' Θ' (pinst_ty σ T1) w →
                lvE (below j) W' Θ'' (pinst_ty σ U) F (subst1 w eb)) ∧
             (j = n → LVdef below n k' W' Θ' σ T1 w →
                Etop below n (λ W Θ v, LVdef below n k' W Θ σ U v) (pinst_ty σ U)
                  W' Θ'' F (subst1 w eb)))
        ∨ (∃ kc T0, v = Konst kc ∧ Θ = ∅ ∧ konst_ty (w_eq W) (w_lt W) (pt_known W) kc T0 ∧
             teqW W T0 (pinst_ty σ (TLolli ub lb T1 U)))
    | TProd T1 U =>
        ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ tenv_comp (w_eq W) Θ Θ1 Θ2 ∧
          LVdef below n k' W Θ1 σ T1 v1 ∧ LVdef below n k' W Θ2 σ U v2
    | TSum T1 U =>
        (∃ v', v = Inj1 v' ∧ LVdef below n k' W Θ σ T1 v')
        ∨ (∃ v', v = Inj2 v' ∧ LVdef below n k' W Θ σ U v')
    | TBox m kk C T1 =>
        Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
          ∀ W' xs ss, wext W W' → length xs = m → length ss = kk → Forall hcontractive ss →
            bcs_hold (w_eq W') (w_lt W') (bcs_inst σ C) xs → Forall (pt_known W') xs →
            LVdef below n k' W' ∅ pvar
              (sinst_ty (slist ss) (ty_inst xs (pinst_ty (pup m σ) T1))) (thunk eb)
    | TEx lb m C T1 =>
        lbx_below W (lb_map (pt_inst σ) lb) (tenv_heads Θ) false ∧
        ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧
          bcs_hold (w_eq W) (w_lt W) (bcs_inst σ C) xs ∧
          LVdef below n k' W Θ (pt_inst (plist xs) ∘ pup m σ) T1 v
    end
  end.

Definition lVtop (below : nat → llevel) (n : nat) (T : ty) : world → tenv → expr → Prop :=
  λ W Θ v, LVdef below n (S (tsize T)) W Θ pvar T v.

Definition mk_llevel (below : nat → llevel) (n : nat) : llevel :=
  {| lvV := λ W Θ T v, lVtop below n T W Θ v;
     lvE := λ W Θ T F e, Etop below n (lVtop below n T) T W Θ F e;
     lvP := λ W Σ T p, Ptop below n (lVtop below n T) T W Σ p |}.

Definition dummy_llevel : llevel :=
  {| lvV := λ _ _ _ _, False; lvE := λ _ _ _ _ _, False; lvP := λ _ _ _ _, False |}.

Fixpoint llevels (n : nat) : nat → llevel :=
  match n with
  | 0 => λ _, dummy_llevel
  | S n' => λ j, if decide (j < n') then llevels n' j else mk_llevel (llevels n') n'
  end.

Definition llevel_at (n : nat) : llevel := llevels (S n) n.

Definition LVrel (n : nat) : world → tenv → ty → expr → Prop := lvV (llevel_at n).
Definition LErel (n : nat) : world → tenv → ty → gset point → expr → Prop :=
  lvE (llevel_at n).
Definition LPrel (n : nat) : world → senv → ty → proc → Prop := lvP (llevel_at n).
