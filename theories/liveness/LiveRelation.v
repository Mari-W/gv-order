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

(** ** Sizes of types

    [tsize] (types/Types.v) counts the type constructors outside session
    types. Instantiation keeps it. *)

Lemma tsize_pos T : 0 < tsize T.
Proof. destruct T; simpl; lia. Qed.

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

    [padmin]: the τ of P-Act-Beta, P-Act-New, P-Act-Spawn and P-Act-Link,
    which cost nothing. A link observes nothing, so it is internal
    (lock-freedom plan §6.1). [pcomm]: the τ of P-Act-Msg, P-Act-Close
    and P-Act-Choice, which cost two. [pchan] is a channel step of a
    process, that is [pcomm]. *)

Inductive padmin : proc → proc → Prop :=
  | PABeta C E e e' :
      tstep e LBeta e' → padmin (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]})
  | PANew C E e c x e' :
      tstep e (LNew c x) e' → c ∉ C → c ∉ echans E → c ∉ fchans e →
      padmin (C, E ⊎ {[+ e +]}) (C ∪ {[c]}, E ⊎ {[+ e' +]})
  | PASpawn C E e v e' :
      tstep e (LSpawn v) e' →
      padmin (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]})
  | PALink C E e c bc d bd e' :
      tstep e (LSess (SLink {[(c, bc); (d, bd)]})) e' → c ∈ C →
      padmin (C, E ⊎ {[+ e +]}) (C ∖ {[c]}, echsubst c d (E ⊎ {[+ e' +]})).

Inductive pcomm : proc → proc → Prop :=
  | PCMsg C E c b v e e' f f' :
      tstep e (LSess (SSend (c, b) v)) e' → tstep f (LSess (SRecv (c, negb b) v)) f' →
      pcomm (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PCClose C E c b e e' f f' :
      tstep e (LSess (SClos (c, b))) e' → tstep f (LSess (SClos (c, negb b))) f' → c ∈ C →
      pcomm (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C ∖ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PCChoice C E c β b e e' f f' :
      tstep e (LSess (SSel (c, β) b)) e' → tstep f (LSess (SBra (c, negb β) b)) f' →
      pcomm (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]}).

Definition pchan (p p' : proc) : Prop := pcomm p p'.

Lemma padmin_link p p' : ptau_link p p' → padmin p p'.
Proof. intros (C & E & e & c & bc & d & bd & e' & -> & Hst & HC & ->). by eapply PALink. Qed.

Lemma ptau_classify p p' : proc_step p PTau p' ↔ padmin p p' ∨ pchan p p'.
Proof.
  split.
  - inversion 1; subst.
    + left. by econstructor.
    + left. by econstructor.
    + left. by econstructor.
    + right. by econstructor.
    + right. by econstructor.
    + right. by econstructor.
    + left. by econstructor.
  - intros [Ha|Hc].
    + destruct Ha; by econstructor.
    + destruct Hc; by econstructor.
Qed.

Lemma padmin_step p p' : padmin p p' → preduction p p'.
Proof. intros H. apply ptau_classify. by left. Qed.

Lemma pchan_step p p' : pchan p p' → preduction p p'.
Proof. intros H. apply ptau_classify. by right. Qed.

(** ** Environments that fit a term (E-Fit, sharp edges 173)

    [tenv_bipol Θ]: the two entries of a channel Θ holds both ends of
    sit at points of different polarity, so they are two ends.
    [tenv_fit Θ e] (types/Types.v) is [tenv_ends Θ = fends e] and this. *)

Definition tenv_bipol (Θ : tenv) : Prop :=
  ∀ c e1 e2, Θ !! c = Some (Both e1 e2) → pt_pol e1.2 ≠ pt_pol e2.2.

Lemma tenv_fit_iff Θ e : tenv_fit Θ e ↔ tenv_ends Θ = fends e ∧ tenv_bipol Θ.
Proof. done. Qed.

Lemma pt_pol_dual y : pt_pol (pt_dual y) = negb (pt_pol y).
Proof. done. Qed.

Lemma tenv_bipol_empty : tenv_bipol ∅.
Proof. intros c e1 e2. by rewrite lookup_empty. Qed.

Lemma tenv_bipol_singleton_one c e : tenv_bipol {[c := One e]}.
Proof. intros c' e1 e2 H. apply lookup_singleton_Some in H as [_ H]. done. Qed.

Lemma tenv_bipol_comp Θ Θ1 Θ2 :
  tenv_comp (@eq point) Θ Θ1 Θ2 → tenv_bipol Θ1 → tenv_bipol Θ2 → tenv_bipol Θ.
Proof.
  intros [Hj Hd] H1 H2 c e1 e2 Hc. pose proof (Hj c) as Hjc. rewrite Hc in Hjc.
  inversion Hjc as [|o Ha Hb|o Ha Hb|f1 f2 Ha Hb|f1 f2 Ha Hb]; subst.
  - by apply (H1 c).
  - by apply (H2 c).
  - destruct (Hd c e1 e2 (eq_sym Ha) (eq_sym Hb)) as [He _]. rewrite He, pt_pol_dual.
    by destruct (pt_pol e2.2).
  - destruct (Hd c e2 e1 (eq_sym Ha) (eq_sym Hb)) as [He _]. rewrite He, pt_pol_dual.
    by destruct (pt_pol e1.2).
Qed.

Lemma tenv_bipol_comp_l R Θ Θ1 Θ2 : tenv_comp R Θ Θ1 Θ2 → tenv_bipol Θ → tenv_bipol Θ1.
Proof.
  intros [Hj _] H c e1 e2 Hc. pose proof (Hj c) as Hjc. rewrite Hc in Hjc.
  inversion Hjc; subst. by apply (H c).
Qed.

Lemma tenv_bipol_comp_r R Θ Θ1 Θ2 : tenv_comp R Θ Θ1 Θ2 → tenv_bipol Θ → tenv_bipol Θ2.
Proof.
  intros [Hj _] H c e1 e2 Hc. pose proof (Hj c) as Hjc. rewrite Hc in Hjc.
  inversion Hjc; subst. by apply (H c).
Qed.

Lemma tenv_bipol_insert_new Θ c s s' x :
  tenv_bipol Θ → tenv_bipol (<[c := Both (s, x) (s', pt_dual x)]> Θ).
Proof.
  intros H c' e1 e2 Hc. destruct (decide (c' = c)) as [->|Hne].
  - rewrite lookup_insert_eq in Hc. injection Hc as <- <-. simpl.
    destruct x as [? [] ?]; simpl; done.
  - rewrite lookup_insert_ne in Hc by done. by apply (H c').
Qed.

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
        tenv_hd_end Θ c (SSeq (SRcv m U) s) k Θ1 ∧
        ∀ W' j Θ2 Θ1c Θ', wext W W' → j ≤ pred n →
          tenv_ext Θ1 c.1 (s, pt_shift 1 k) Θ1c →
          tenv_comp (w_eq W') Θ' Θ1c Θ2 →
          Vlow j W' Θ2 (payload_at m U k) w →
          Elow j W' Θ' T F e'
  | SSend c w =>                                       (* O-Send *)
      ∃ Θr Θ1 Θ2 m U s k Θ',
        tenv_hd_end Θ c (SSeq (SSnd m U) s) k Θr ∧ tenv_comp (w_eq W) Θr Θ1 Θ2 ∧
        Vlow (pred n) W Θ2 (payload_at m U k) w ∧
        tenv_ext Θ1 c.1 (s, pt_shift 1 k) Θ' ∧
        Elow (pred n) W Θ' T F e'
  | SClos c =>                                         (* O-Close *)
      ∃ Θ1 k, tenv_hd_end Θ c SEnd k Θ1 ∧ Elow (pred n) W Θ1 T F e'
  | SLink cd => True                                   (* O-Link, in Ebody *)
  | SSel c b =>                                        (* O-Select *)
      ∃ Θr s1 s2 k Θ', tenv_hd_end Θ c (SPlus s1 s2) k Θr ∧
        tenv_ext Θr c.1 (sbranch b s1 s2, sel_pt k b) Θ' ∧
        Elow (pred n) W Θ' T F e'
  | SBra c b =>                                        (* O-Branch *)
      ∃ Θr s1 s2 k Θ', tenv_hd_end Θ c (SWith s1 s2) k Θr ∧
        tenv_ext Θr c.1 (sbranch b s1 s2, bra_pt k b) Θ' ∧
        Elow (pred n) W Θ' T F e'
  end.

(** O-Link: a link costs nothing, so its continuation is read at the
    same level, X (lock-freedom plan §6.1). *)
Definition LElink (X : world → tenv → gset point → expr → Prop)
    (W : world) (Θ : tenv) (F : gset point) (cd : gset cend) (e' : expr) : Prop :=
  ∃ c d Θ1 Θm sc sd kc kd,
    cd = {[(c, pt_pol kc); (d, pt_pol kd)]} ∧
    tenv_ext Θ1 d (sd, kd) Θm ∧ tenv_ext Θm c (sc, kc) Θ ∧
    sdual sd sc ∧ w_eq W kc (pt_dual kd) ∧
    X W Θ1 F e'.

(** The session labels of a process other than a link, each at cost
    one. *)
Definition LPobl (Vlow : nat → world → tenv → ty → expr → Prop)
    (Plow : nat → world → senv → ty → proc → Prop)
    (n : nat) (W : world) (Σ : senv) (T : ty) (p : proc)
    (σ : slabel) (p' : proc) : Prop :=
  match σ with
  | SRecv c w =>                                       (* Q-Recv *)
      ∃ Σ1 m U s k,
        senv_hd Σ c.1 (SSeq (SRcv m U) s) k Σ1 ∧ c.1 ∉ dom Σ1 ∧
        ∀ W' j Θ2, wext W W' → j ≤ pred n → dom Θ2 ## p.1 →
          recv_ok W' (<[c.1 := (s, pt_shift 1 k)]> Σ1) Θ2 →
          Vlow j W' Θ2 (payload_at m U k) w →
          Plow j W' (recv_env (<[c.1 := (s, pt_shift 1 k)]> Σ1) Θ2) T
            (p'.1 ∪ recv_back (<[c.1 := (s, pt_shift 1 k)]> Σ1) Θ2, p'.2)
  | SSend c w =>                                       (* Q-Send *)
      Psend_case (Vlow (pred n)) (Plow (pred n)) W Σ T p c w p'
  | SClos c =>                                         (* Q-Close *)
      Pclos_case (Plow (pred n)) W Σ T c p'
  | SLink cd => True                                   (* Q-Link, in Pbody *)
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
  (∃ eb, w = Lam eb ∧ tenv_fit Θ eb ∧ lb_below W lb (tenv_heads Θ) ∧
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
  tenv_fit Θ e ∧                                                    (* E-Fit *)
  ∀ W1, wext_r W W1 →
    (irred e → VT W1 Θ e) ∧                                        (* E-Stop *)
    (¬ irred e → ready_t W1 Θ F e) ∧                              (* E-Step *)
    (∀ e', tstep e LBeta e' → X VT T W1 Θ F e') ∧                  (* O-Beta *)
    (∀ c x e', tstep e (LNew c x) e' → c ∉ dom Θ →                (* O-New *)
       pt_known W1 x ∧ ∃ s s',
         sdual s s' ∧
         X VT T W1 (<[c := Both (s, x) (s', pt_dual x)]> Θ) F e') ∧
    (∀ w e', tstep e (LSpawn w) e' →                               (* O-Spawn *)
       ∃ Θ1 Θ2 ub lb, tenv_comp (w_eq W1) Θ Θ1 Θ2 ∧
         Vspawn (λ j, lvV (below j)) (λ j, lvE (below j))
           (X Vunit_top TUnit) n W1 Θ1 ub lb w ∧
         X VT T W1 Θ2 F e') ∧
    (∀ σ e', tstep e (LSess σ) e' →                                 (* O-σ *)
       LEobl (λ j, lvV (below j)) (λ j, lvE (below j)) n W1 Θ T F σ e') ∧
    (∀ cd e', tstep e (LSess (SLink cd)) e' →                       (* O-Link *)
       LElink (X VT T) W1 Θ F cd e').

Inductive Eind (below : nat → llevel) (n : nat) :
    (world → tenv → expr → Prop) → ty → world → tenv → gset point → expr → Prop :=
  | EIntro VT T W Θ F e :
      Ebody below n (Eind below n) VT T W Θ F e → Eind below n VT T W Θ F e.

(** A process τ keeps the world (constant world, sharp edge 172). *)
Definition LPtau_case (X : world → senv → ty → proc → Prop)
    (W : world) (Σ : senv) (T : ty) (p' : proc) : Prop :=
  p'.1 ## dom Σ → X W Σ T p'.

(** ** The process relation at level n *)
Definition Pbody (below : nat → llevel) (n : nat)
    (VT : world → tenv → expr → Prop) (T : ty)
    (X : world → senv → proc → Prop) (W : world) (Σ : senv) (p : proc) : Prop :=
  ∀ W1, wext_r W W1 →
    (pirred p →                                                    (* P-Stop *)
      ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ VT W1 (tenv_of Σ) v ∧
             (∀ e, e ∈ E → e = EUnit)) ∧
    (¬ pirred p → ready_p W1 Σ p) ∧                                 (* P-Step *)
    (∀ p', padmin p p' → p'.1 ## dom Σ → X W1 Σ p') ∧              (* Q-Admin *)
    (∀ p', pcomm p p' →                                            (* Q-Comm *)
       LPtau_case (lvP (below (pred (pred n)))) W1 Σ T p') ∧
    (∀ cd p', proc_step p (PSess (SLink cd)) p' →                   (* Q-Link *)
       Plink_case (λ W Σ _ q, X W Σ q) W1 Σ T cd p') ∧
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

    As [Vrel] except the arrow, which reads the argument and the body at
    the lower levels j < n and, through [Etop], at n itself. The fuel
    makes the point substitution of [Vdef] unnecessary: the existential
    and the box read their body at the instance itself. *)
Fixpoint LVdef (below : nat → llevel) (n k : nat)
    (W : world) (Θ : tenv) (T : ty) (v : expr) {struct k} : Prop :=
  match k with
  | 0 => False
  | S k' =>
    match T with
    | TUnit => Θ = ∅ ∧ v = EUnit
    | TSess s x =>
        ∃ c b s0 kk, v = Chan c b ∧ Θ = {[c := One (s0, kk)]} ∧ seq s0 s ∧ w_eq W kk x ∧
          pt_pol kk = b
    | TPt x => Θ = ∅ ∧ v = EPt x ∧ pt_known W x
    | TLolli ub lb T1 U =>
        (∃ eb, v = Lam eb ∧ tenv_fit Θ eb ∧ lb_below W lb (tenv_heads Θ) ∧
           ∀ W' j Θ' Θ'' w F, wext W W' → j ≤ n →
             tenv_comp (w_eq W') Θ'' Θ Θ' → ub_below W' ub F →
             (j < n → lvV (below j) W' Θ' T1 w → lvE (below j) W' Θ'' U F (subst1 w eb)) ∧
             (j = n → LVdef below n k' W' Θ' T1 w →
                Etop below n (λ W Θ v, LVdef below n k' W Θ U v) U W' Θ'' F (subst1 w eb)))
        ∨ (∃ kc T0, v = Konst kc ∧ Θ = ∅ ∧ konst_ty (w_eq W) (w_lt W) (pt_known W) kc T0 ∧
             teqW W T0 (TLolli ub lb T1 U))
    | TProd T1 U =>
        ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ tenv_comp (w_eq W) Θ Θ1 Θ2 ∧
          LVdef below n k' W Θ1 T1 v1 ∧ LVdef below n k' W Θ2 U v2
    | TSum T1 U =>
        (∃ v', v = Inj1 v' ∧ LVdef below n k' W Θ T1 v')
        ∨ (∃ v', v = Inj2 v' ∧ LVdef below n k' W Θ U v')
    | TBox m kk C T1 =>
        Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
          ∀ W' xs ss, wext W W' → length xs = m → length ss = kk → Forall hcontractive ss →
            bcs_hold (w_eq W') (w_lt W') C xs → Forall (pt_known W') xs →
            LVdef below n k' W' ∅ (sinst_ty (slist ss) (ty_inst xs T1)) (thunk eb)
    | TEx lb m C T1 =>
        lbx_below W lb (tenv_heads Θ) false ∧
        ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧ bcs_hold (w_eq W) (w_lt W) C xs ∧
          LVdef below n k' W Θ (ty_inst xs T1) v
    end
  end.

Definition lVtop (below : nat → llevel) (n : nat) (T : ty) : world → tenv → expr → Prop :=
  λ W Θ v, LVdef below n (S (tsize T)) W Θ T v.

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

(** ** Monotonicity of one unfolding, and induction

    [Ebody_mono] and [Pbody_mono] are transparent, so that the guard
    checker sees through them in [Eind_ind'] and [Pind_ind']. *)

Definition Ebody_mono below n
    (X Y : (world → tenv → expr → Prop) → ty → world → tenv → gset point → expr → Prop)
    (f : ∀ VT T W Θ F e, X VT T W Θ F e → Y VT T W Θ F e) VT T W Θ F e :
  Ebody below n X VT T W Θ F e → Ebody below n Y VT T W Θ F e.
Proof.
  intros [Hfit H]. split; [exact Hfit|]. intros W1 HW. destruct (H W1 HW) as (Hs & Hr & Hb & Hn & Hsp & Hσ & Hlk).
  split; [exact Hs|]. split; [exact Hr|]. split.
  { intros e' Hst. exact (f _ _ _ _ _ _ (Hb e' Hst)). }
  split.
  { intros c x e' Hst Hc. destruct (Hn c x e' Hst Hc) as (H1 & s & s' & H2 & H4).
    split; [exact H1|]. exists s, s'. split; [exact H2|].
    exact (f _ _ _ _ _ _ H4). }
  split; [|split; [exact Hσ|]].
  2: { intros cd e' Hst. destruct (Hlk cd e' Hst) as (c & d & Θ1 & Θm & sc & sd & kc & kd & H1 & H2 & H3 & H4 & H5 & H6).
       exists c, d, Θ1, Θm, sc, sd, kc, kd. split; [exact H1|]. split; [exact H2|].
       split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. exact (f _ _ _ _ _ _ H6). }
  intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & H1 & H2 & H3).
  exists Θ1, Θ2, ub, lb. split; [exact H1|]. split; [|exact (f _ _ _ _ _ _ H3)].
  destruct H2 as [(eb & Hw & Hfc & Hlb & H')|Hk]; [left|right; exact Hk].
  exists eb. split; [exact Hw|]. split; [exact Hfc|]. split; [exact Hlb|].
  intros W' j Θ' Θ'' w' F' HW' Hj Hc Hub.
  destruct (H' W' j Θ' Θ'' w' F' HW' Hj Hc Hub) as [K1 K2]. split; [exact K1|].
  intros Hjn HΘ Hw'. exact (f _ _ _ _ _ _ (K2 Hjn HΘ Hw')).
Defined.

Lemma Eind_ind' below n
    (Φ : (world → tenv → expr → Prop) → ty → world → tenv → gset point → expr → Prop) :
  (∀ VT T W Θ F e,
     Ebody below n (λ VT T W Θ F e, Eind below n VT T W Θ F e ∧ Φ VT T W Θ F e)
       VT T W Θ F e → Φ VT T W Θ F e) →
  ∀ VT T W Θ F e, Eind below n VT T W Θ F e → Φ VT T W Θ F e.
Proof.
  intros Hind. fix IH 7. intros VT T W Θ F e [VT' T' W' Θ' F' e' H].
  apply Hind. refine (Ebody_mono below n _ _ _ VT' T' W' Θ' F' e' H).
  intros ? ? ? ? ? ? HX. exact (conj HX (IH _ _ _ _ _ _ HX)).
Qed.

Definition Pbody_mono below n VT T (X Y : world → senv → proc → Prop)
    (f : ∀ W Σ p, X W Σ p → Y W Σ p) W Σ p :
  Pbody below n VT T X W Σ p → Pbody below n VT T Y W Σ p.
Proof.
  intros H W1 HW. destruct (H W1 HW) as (Hs & Hr & Ha & Hc & Hl & Hσ).
  split; [exact Hs|]. split; [exact Hr|]. split; [|split; [exact Hc|split; [|exact Hσ]]].
  - intros p' Hst Hd. exact (f _ _ _ (Ha p' Hst Hd)).
  - intros cd p' Hst. destruct (Hl cd p' Hst) as (c & d & Σ1 & sc & sd & kc & kd & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exists c, d, Σ1, sc, sd, kc, kd. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. exact (f _ _ _ H8).
Defined.

Lemma Pind_ind' below n VT T (Φ : world → senv → proc → Prop) :
  (∀ W Σ p, Pbody below n VT T (λ W Σ p, Pind below n VT T W Σ p ∧ Φ W Σ p) W Σ p →
     Φ W Σ p) →
  ∀ W Σ p, Pind below n VT T W Σ p → Φ W Σ p.
Proof.
  intros Hind. fix IH 4. intros W Σ p [W' Σ' p' H].
  apply Hind. refine (Pbody_mono below n VT T _ _ _ W' Σ' p' H).
  intros ? ? ? HX. exact (conj HX (IH _ _ _ HX)).
Qed.

Lemma Eind_inv below n VT T W Θ F e :
  Eind below n VT T W Θ F e → Ebody below n (Eind below n) VT T W Θ F e.
Proof. by destruct 1. Qed.

Lemma Pind_inv below n VT T W Σ p :
  Pind below n VT T W Σ p → Pbody below n VT T (Pind below n VT T) W Σ p.
Proof. by destruct 1. Qed.

(** Monotonicity in the world holds by definition. *)
Lemma Eind_mono_world below n VT T W W' Θ F e :
  wext_r W W' → Eind below n VT T W Θ F e → Eind below n VT T W' Θ F e.
Proof.
  intros HW [Hfit H]%Eind_inv. constructor. split; [exact Hfit|]. intros W1 HW1. apply H. by eapply wext_r_trans.
Qed.

Lemma Pind_mono_world below n VT T W W' Σ p :
  wext_r W W' → Pind below n VT T W Σ p → Pind below n VT T W' Σ p.
Proof.
  intros HW H%Pind_inv. constructor. intros W1 HW1. apply H. by eapply wext_r_trans.
Qed.

Lemma Vspawn_mono Vl El (E1 E2 : world → tenv → gset point → expr → Prop) n W Θ ub lb w :
  (∀ W Θ F e, E1 W Θ F e → E2 W Θ F e) →
  Vspawn Vl El E1 n W Θ ub lb w → Vspawn Vl El E2 n W Θ ub lb w.
Proof.
  intros HE [(eb & -> & Hfc & Hlb & H)|Hk]; [left|by right].
  exists eb. split_and!; [done..|]. intros W' j Θ' Θ'' w' F HW Hj Hc Hub.
  destruct (H W' j Θ' Θ'' w' F HW Hj Hc Hub) as [H1 H2]. split; [done|].
  intros ? ? ?. apply HE. auto.
Qed.

(** E-Stop reads VT only. *)
Lemma Eind_VT_mono below n VT1 VT2 T W Θ F e :
  (∀ W Θ v, VT1 W Θ v → VT2 W Θ v) →
  Eind below n VT1 T W Θ F e → Eind below n VT2 T W Θ F e.
Proof.
  intros HV H. revert VT2 HV.
  induction H as [VT T W Θ F e H] using Eind_ind'. intros VT2 HV.
  constructor. destruct H as [Hfit H]. split; [exact Hfit|].
  intros W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hb & Hn & Hsp & Hσ & Hlk).
  split_and!; [auto|done| | | |done|].
  - intros e' Hst. by apply (Hb e' Hst).
  - intros c x e' Hst Hc. destruct (Hn c x e' Hst Hc) as (? & s & s' & ? & _ & HX).
    split; [done|]. exists s, s'. split; [done|]. by apply HX.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & _ & HX).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |by apply HX].
    eapply Vspawn_mono; [|exact Hv]. by intros ? ? ? ? [? _].
  - intros cd e' Hst. destruct (Hlk cd e' Hst) as (c & d & Θ1 & Θm & sc & sd & kc & kd & ? & ? & ? & ? & ? & _ & HX).
    exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..|]. by apply HX.
Qed.

Lemma Eind_VT_iff below n VT1 VT2 T W Θ F e :
  (∀ W Θ v, VT1 W Θ v ↔ VT2 W Θ v) →
  Eind below n VT1 T W Θ F e ↔ Eind below n VT2 T W Θ F e.
Proof. intros HV. split; apply Eind_VT_mono; naive_solver. Qed.

Lemma Etop_VT_iff below n VT1 VT2 T W Θ F e :
  (∀ W Θ v, VT1 W Θ v ↔ VT2 W Θ v) →
  Etop below n VT1 T W Θ F e ↔ Etop below n VT2 T W Θ F e.
Proof. intros HV. destruct n; [done|]. by apply Eind_VT_iff. Qed.

Lemma Pind_VT_mono below n VT1 VT2 T W Σ p :
  (∀ W Θ v, VT1 W Θ v → VT2 W Θ v) →
  Pind below n VT1 T W Σ p → Pind below n VT2 T W Σ p.
Proof.
  intros HV H. induction H as [W Σ p H] using Pind_ind'.
  constructor. intros W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Ha & Hc & Hl & Hσ).
  split_and!; [|done| |done| |done].
  - intros Hirr. destruct (Hs Hirr) as (v & E & ? & ? & ? & ?). exists v, E. auto.
  - intros p' Hst Hd. by destruct (Ha p' Hst Hd) as [_ HX].
  - intros cd p' Hst. destruct (Hl cd p' Hst) as (c & d & Σ1 & sc & sd & kc & kd & ? & ? & ? & ? & ? & ? & ? & _ & HX).
    exists c, d, Σ1, sc, sd, kc, kd. by split_and!.
Qed.

(** ** Obligations, monotone in the lower levels *)

Lemma LEobl_mono Vl1 Vl2 El1 El2 n W Θ T F σ e' :
  (∀ j, j ≤ pred n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
  (∀ j, j ≤ pred n → ∀ W Θ T F, El1 j W Θ T F e' → El2 j W Θ T F e') →
  LEobl Vl1 El1 n W Θ T F σ e' → LEobl Vl2 El2 n W Θ T F σ e'.
Proof.
  intros HV HE. destruct σ as [c w|c w|c|cd|c b|c b]; cbn [LEobl].
  - intros (Θ1 & m & U & s & k & Hhd & H). exists Θ1, m, U, s, k. split; [done|].
    intros W' j Θ2 Θ1c Θ' HW Hj Hext Hc HV'. apply HE; [done|].
    apply (H W' j Θ2 Θ1c Θ'); try done. by apply HV.
  - intros (Θr&Θ1&Θ2&m&U&s&k&Θ'&?&?&Hp&?&HX). exists Θr, Θ1, Θ2, m, U, s, k, Θ'.
    split_and!; try done; [by apply HV|by apply HE].
  - intros (Θ1&k&?&HX). exists Θ1, k. split; [done|by apply HE].
  - done.
  - intros (Θr&s1&s2&k&Θ'&?&?&HX). exists Θr, s1, s2, k, Θ'. split_and!; try done. by apply HE.
  - intros (Θr&s1&s2&k&Θ'&?&?&HX). exists Θr, s1, s2, k, Θ'. split_and!; try done. by apply HE.
Qed.

Lemma LElink_mono (X Y : world → tenv → gset point → expr → Prop) W Θ F cd e' :
  (∀ Θ1, X W Θ1 F e' → Y W Θ1 F e') → LElink X W Θ F cd e' → LElink Y W Θ F cd e'.
Proof.
  intros HXY (c&d&Θ1&Θm&sc&sd&kc&kd&?&?&?&?&?&HX).
  exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; try done. by apply HXY.
Qed.

Lemma Plink_case_mono (X Y : world → senv → ty → proc → Prop) W Σ T T' cd p' :
  (∀ Σ1, X W Σ1 T p' → Y W Σ1 T' p') → Plink_case X W Σ T cd p' → Plink_case Y W Σ T' cd p'.
Proof.
  intros HXY (c&d&Σ1&sc&sd&kc&kd&?&?&?&?&?&?&?&HX).
  exists c, d, Σ1, sc, sd, kc, kd. split_and!; try done. by apply HXY.
Qed.

Lemma LPtau_case_mono (X Y : world → senv → ty → proc → Prop) W Σ T p' :
  (∀ W Σ T, X W Σ T p' → Y W Σ T p') → LPtau_case X W Σ T p' → LPtau_case Y W Σ T p'.
Proof. intros HXY H Hd. by apply HXY, H. Qed.

Lemma LPobl_mono Vl1 Vl2 Pl1 Pl2 n W Σ T p σ p' :
  (∀ j, j ≤ pred n → ∀ W Θ T v, Vl1 j W Θ T v ↔ Vl2 j W Θ T v) →
  (∀ j, j ≤ pred n → ∀ W Σ T q, Pl1 j W Σ T q → Pl2 j W Σ T q) →
  LPobl Vl1 Pl1 n W Σ T p σ p' → LPobl Vl2 Pl2 n W Σ T p σ p'.
Proof.
  intros HV HP. destruct σ as [c w|c w|c|cd|c b|c b]; cbn [LPobl].
  - intros (Σ1 & m & U & s & k & Hhd & Hc & H). exists Σ1, m, U, s, k.
    split_and!; [done|done|]. intros W' j Θ2 HW Hj Hfr Hdu HV'.
    apply HP; [done|]. apply (H W' j Θ2); try done. by apply HV.
  - intros (Σ0&Σv&m&U&s&k&Σe&Θe&?&?&?&?&?&?&?&Hp&HX).
    exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; try done; [by apply HV|by apply HP].
  - intros (Σ1&k&?&?&HX). exists Σ1, k. split_and!; try done. by apply HP.
  - done.
  - intros (Σ1&s1&s2&k&?&?&HX). exists Σ1, s1, s2, k. split_and!; try done. by apply HP.
  - intros (Σ1&s1&s2&k&?&?&HX). exists Σ1, s1, s2, k. split_and!; try done. by apply HP.
Qed.

(** The relation at level n reads the levels below n only. *)
Lemma Eind_below below1 below2 n VT T W Θ F e :
  0 < n → (∀ j, j < n → below1 j = below2 j) →
  Eind below1 n VT T W Θ F e → Eind below2 n VT T W Θ F e.
Proof.
  intros Hn Hb H. induction H as [VT T W Θ F e H] using Eind_ind'.
  constructor. destruct H as [Hfit H]. split; [exact Hfit|].
  intros W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Hbeta & Hnew & Hsp & Hσ & Hlk).
  split_and!; [done|done| | | | |].
  - intros e' Hst. by apply (Hbeta e' Hst).
  - intros c x e' Hst Hc. destruct (Hnew c x e' Hst Hc) as (? & s & s' & ? & _ & HX).
    split; [done|]. exists s, s'. by split_and!.
  - intros w e' Hst. destruct (Hsp w e' Hst) as (Θ1 & Θ2 & ub & lb & ? & Hv & _ & HX).
    exists Θ1, Θ2, ub, lb. split_and!; [done| |done].
    destruct Hv as [(eb & -> & ? & ? & Hv)|Hk]; [left|by right]. exists eb.
    split_and!; [done..|]. intros W' j Θ' Θ'' w' F' HW Hj Hc Hub.
    destruct (Hv W' j Θ' Θ'' w' F' HW Hj Hc Hub) as [K1 K2]. split.
    + intros Hjn. rewrite <-(Hb j Hjn). by apply K1.
    + intros ? ? ?. by apply K2.
  - intros σ e' Hst. eapply LEobl_mono; [..|exact (Hσ σ e' Hst)].
    + intros j Hj W' Θ' T' v. cbv beta. rewrite (Hb j) by lia. done.
    + intros j Hj W' Θ' T' F'. cbv beta. rewrite (Hb j) by lia. done.
  - intros cd e' Hst. eapply LElink_mono; [|exact (Hlk cd e' Hst)]. by intros ? [_ ?].
Qed.

Lemma Pind_below below1 below2 n VT T W Σ p :
  0 < n → (∀ j, j < n → below1 j = below2 j) →
  Pind below1 n VT T W Σ p → Pind below2 n VT T W Σ p.
Proof.
  intros Hn Hb H. induction H as [W Σ p H] using Pind_ind'.
  constructor. intros W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Ha & Hc & Hl & Hσ).
  split_and!; [done|done| | | |].
  - intros p' Hst Hd. by destruct (Ha p' Hst Hd) as [_ HX].
  - intros p' Hst. rewrite <-(Hb (pred (pred n))) by lia. auto.
  - intros cd p' Hst. eapply Plink_case_mono; [|exact (Hl cd p' Hst)]. by intros ? [_ ?].
  - intros σ p' Hst. eapply LPobl_mono; [..|exact (Hσ σ p' Hst)].
    + intros j Hj W' Θ' T' v. cbv beta. rewrite (Hb j) by lia. done.
    + intros j Hj W' Σ' T' q. cbv beta. rewrite (Hb j) by lia. done.
Qed.

(** ** Levels *)

Lemma llevel_at_eq n : llevel_at n = mk_llevel (llevels n) n.
Proof. unfold llevel_at. simpl. by destruct (decide (n < n)); [lia|]. Qed.

Lemma llevels_at n j : j < n → llevels n j = llevel_at j.
Proof.
  revert j. induction n as [|n' IH]; intros j Hj; [lia|].
  simpl. destruct (decide (j < n')) as [H|H].
  - by apply IH.
  - assert (j = n') as -> by lia. by rewrite llevel_at_eq.
Qed.

Lemma LErel_0 W Θ T F e : LErel 0 W Θ T F e.
Proof. unfold LErel. rewrite llevel_at_eq. simpl. exact I. Qed.

Lemma LPrel_0 W Σ T p : LPrel 0 W Σ T p.
Proof. unfold LPrel. rewrite llevel_at_eq. simpl. exact I. Qed.

(** ** The fuel of V does not matter above the size *)

Lemma LVdef_fuel below n k1 : ∀ k2 W Θ T v, tsize T < k1 → tsize T < k2 →
  LVdef below n k1 W Θ T v ↔ LVdef below n k2 W Θ T v.
Proof.
  induction k1 as [|k1 IH]; intros k2 W Θ T v H1 H2; [lia|].
  destruct k2 as [|k2]; [lia|].
  assert (∀ W Θ T v, tsize T < k1 → tsize T < k2 →
            LVdef below n k1 W Θ T v ↔ LVdef below n k2 W Θ T v) as IH'.
  { intros W0 Θ0 T0 v0 ? ?. by apply IH. }
  clear IH.
  destruct T as [|ub lb T1 U|T1 U|T1 U|m kk C T1|s x|lb m C T1|x]; cbn [LVdef tsize] in *.
  - done.
  - apply or_iff_compat_r.
    split; intros (eb & -> & Hfc & Hlb & H); exists eb; (split_and!; [done..|]);
      intros W' j Θ' Θ'' w F HW Hj Hc Hub; destruct (H W' j Θ' Θ'' w F HW Hj Hc Hub) as [K1 K2];
      (split; [done|]); intros Hjn HV.
    + eapply Etop_VT_iff; [|apply K2; [done|]].
      * intros. symmetry. apply IH'; lia.
      * apply (IH' W' Θ' T1 w); [lia|lia|exact HV].
    + eapply Etop_VT_iff; [|apply K2; [done|]].
      * intros. apply IH'; lia.
      * apply (IH' W' Θ' T1 w); [lia|lia|exact HV].
  - split; intros (v1 & v2 & Θ1 & Θ2 & -> & Hc & Hv1 & Hv2); exists v1, v2, Θ1, Θ2;
      (split_and!; [done|done| |]); (eapply IH'; [..|eassumption]; lia).
  - split; (intros [(v' & -> & Hv)|(v' & -> & Hv)]; [left|right]); exists v'; (split; [done|]);
      (eapply IH'; [..|eassumption]; lia).
  - assert (∀ xs ss, tsize (sinst_ty (slist ss) (ty_inst xs T1)) = tsize T1) as Hts.
    { intros xs ss. unfold ty_inst. by rewrite tsize_sinst, tsize_pinst. }
    split; intros (-> & eb & -> & Hfc & H); (split; [done|]); exists eb; (split_and!; [done..|]);
      intros W' xs ss HW Hxs Hss Hsc HC HK; specialize (H W' xs ss HW Hxs Hss Hsc HC HK);
      (eapply IH'; [..|exact H]); rewrite Hts; lia.
  - done.
  - assert (∀ xs, tsize (ty_inst xs T1) = tsize T1) as Hts.
    { intros xs. unfold ty_inst. by rewrite tsize_pinst. }
    apply and_iff_compat_l. split; intros (xs & ? & ? & ? & Hv); exists xs; (split_and!; [done..|]);
      (eapply IH'; [..|exact Hv]); rewrite Hts; lia.
  - done.
Qed.
