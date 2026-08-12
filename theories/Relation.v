(** * The logical relation (Fig. 5) and semantic typing (§3)

    Three step-indexed layers:
      V_n⟦Σ ⊢ T⟧  values      ([Vrel])
      E_n⟦Σ ⊢ T⟧  terms       ([Erel])
      P_n⟦Σ ⊢ T⟧  processes   ([Prel])

    The step-index recursion is implemented by course-of-values
    recursion on n: [levels n] is (structurally in n) the family of all
    levels below n, [mk_level below n] builds level n from it, and
    [level_at n] projects the actual level n. Later proofs only use the
    equations [level_at_eq] and [levels_at], never the encoding.

    "Σ = Σ1, c : S" from the paper is rendered as
    Σ = <[c := S]> Σ1 together with c ∉ dom Σ1.

    Lemma 3.5 needs the paper's argument "if p is not irreducible then
    it has some transition". That is [proc_progress], proved by
    deciding reducibility rather than by excluded middle, so the
    development is closed under the global context. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Semantics Safety Types Typing.

(** ** The three relations, level by level *)

Record level := Level {
  lV : senv → ty → expr → Prop;
  lE : senv → ty → expr → Prop;
  lP : senv → ty → proc → Prop
}.

(** Value relation at level n, given the family [below] of levels < n.
    Recursive on the type; lower levels are accessed through [below]
    (the ∀ j < n quantification in the ⊸ case). The ⊸ case also
    requires the abstraction's channels to be covered by Σ — for all
    other value forms this holds by construction ([Vrel_fchans]), and
    compositionality needs it: a value sent to the environment must
    not mention channels restricted by an independent component. *)
Fixpoint Vdef (below : nat → level) (n : nat)
    (Σ : senv) (T : ty) (v : expr) {struct T} : Prop :=
  match T with
  | TUnit => Σ = ∅ ∧ v = EUnit
  | TSess s =>
      (* a channel is read up to unfolding: the stored protocol may be
         any type with the same unfolding — E-Conv at the value level *)
      ∃ c s0, v = Chan c ∧ Σ = {[c := s0]} ∧ unfoldS s0 = unfoldS s
  | TLolli T1 U =>
      (∃ eb, v = Lam eb ∧ fchans eb = dom Σ ∧
         ∀ j Σ' w, j < n → Σ' ##ₘ Σ →
           lV (below j) Σ' T1 w →
           lE (below j) (Σ ∪ Σ') U (subst1 w eb))
      ∨ (∃ k, v = Konst k ∧ Σ = ∅ ∧ konst_ty k (TLolli T1 U))
  | TProd T1 U =>
      ∃ v1 v2 Σ1 Σ2, v = Pair v1 v2 ∧ senv_split Σ Σ1 Σ2 ∧
        Vdef below n Σ1 T1 v1 ∧ Vdef below n Σ2 U v2
  | TSum T1 U =>
      (∃ v', v = Inj1 v' ∧ Vdef below n Σ T1 v')
      ∨ (∃ v', v = Inj2 v' ∧ Vdef below n Σ U v')
  | TBox T1 =>
      (* a replicable thunk owns no channels — syntactically, so that
         tightness ([Vrel_fchans]) survives — and its unrolling is a
         good term at every lower index. This is Fig. 8's
         V⟦□T⟧ = {!e | fix x.e ∈ E⟦T⟧} with fix x.e = e[!e/x]: [Vdef]
         at level n is built before [Edef] at level n, but forcing
         always takes a β step, so only lower indices are ever
         constrained and [Vrel_box_iff] recovers the paper's
         same-index statement *)
      Σ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
        ∀ j, j < n → lE (below j) ∅ T1 (subst1 (EBox eb) eb)
  end.

(** Term relation at level n (n = S n' in the non-trivial case),
    given [below] and the level-n value relation [Vn]. One case per
    label shape of the transition, with the Σ bookkeeping of Fig. 5.
    The fork case is guarded by freshness of the new channel: fork
    labels exist for every name c, but only fresh ones are process-
    level enabled. *)
Definition Edef (below : nat → level) (Vn : senv → ty → expr → Prop)
    (n : nat) (Σ : senv) (T : ty) (e : expr) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      (irred e → Vn Σ T e) ∧
      (∀ α e', tstep e α e' →
        match α with
        | LBeta =>                                     (* case 1 *)
            lE (below n') Σ T e'
        | LFork c w =>                                 (* case 2 *)
            c ∉ dom Σ →
            ∃ Σ1 Σ2 s,
              senv_split Σ Σ1 Σ2 ∧
              Vn Σ1 (TLolli (TSess s) TUnit) w ∧
              lE (below n') (<[c := dual s]> Σ2) T e'
        | LSess (SRecv c w) =>                         (* case 3 *)
            ∃ Σ1 U s,
              senv_hd Σ c (SRcv U s) Σ1 ∧ c ∉ dom Σ1 ∧
              ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 →
                lV (below j) Σ2 U w →
                lE (below j) (<[c := s]> (Σ1 ∪ Σ2)) T e'
        | LSess (SSend c w) =>                         (* case 4 *)
            ∃ Σ1 Σ2 U s,
              senv_hd Σ c (SSnd U s) (Σ1 ∪ Σ2) ∧
              Σ1 ##ₘ Σ2 ∧ c ∉ dom Σ1 ∧ c ∉ dom Σ2 ∧
              Vn Σ2 U w ∧
              lE (below n') (<[c := s]> Σ1) T e'
        | LSess (SClos c) =>                           (* case 5 *)
            ∃ Σ1, senv_hd Σ c SEnd Σ1 ∧ c ∉ dom Σ1 ∧
              lE (below n') Σ1 T e'
        | LSess (SLink cd) =>                                  (* case 6, Fig. 10 *)
            (* the two connected ends vanish from the context; their
               stored protocols are dual up to unfolding *)
            ∃ c d Σ1 sc sd,
              cd = {[c; d]} ∧ c ≠ d ∧
              Σ = <[c := sc]> (<[d := sd]> Σ1) ∧
              c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧
              unfoldS sd = unfoldS (dual sc) ∧
              lE (below n') Σ1 T e'
        end)
  end.

(** Type bookkeeping for splitting a process into pieces: of the two
    return types, at most one is not ∗ and it determines the total. *)
Definition ty_one_of (A B C : ty) : Prop :=
  (A = C ∧ B = TUnit) ∨ (A = TUnit ∧ B = C).

(** The split an output forces on the residual, one piece per
    extruded channel.

    [extrusion_split P σ Σ T p]: the process p decomposes into a family of
    pairwise independent processes, exactly one per channel d ∈ dom σ,
    where the piece for d is in the (parameter) process relation P at
    environment Σd, d : σ(d) — it owns the residual end of d. Σ
    accumulates the Σd's (without the d's themselves) and T the return
    types (at most one ≠ ∗). The base case is the degenerate empty
    process: for no extruded channels, nothing needs to remain.

    This is where the relation constrains topology, and the only
    place it does: internally a component may be as cyclic as it
    likes (see examples/Cycle.v), but on its EXTERNAL interface an
    output must leave the residual split one piece per extruded
    channel.  A single piece holding two extruded ends could close a
    dependency cycle through the environment, which is exactly what
    this rules out; and it is what the compositionality proofs need
    when one communication transfers several restricted channels at
    once, since each is reconnected to its own piece separately. *)
Inductive extrusion_split (P : senv → ty → proc → Prop)
    : gmap chan sty → senv → ty → proc → Prop :=
  | extrusion_split_nil : extrusion_split P ∅ ∅ TUnit (∅, ∅)
  | extrusion_split_cons σ d s Σd Σr Td Tr Tt Cd Ed Cr Er :
      σ !! d = None →
      d ∉ dom Σd → d ∉ dom Σr → d ∉ Cd → d ∉ Cr →
      dom σ ## dom Σd → dom σ ## Cd →
      Σd ##ₘ Σr → Cd ## Cr → Cd ## dom Σr → Cr ## dom Σd →
      P (<[d := s]> Σd) Td (Cd, Ed) →
      extrusion_split P σ Σr Tr (Cr, Er) →
      ty_one_of Td Tr Tt →
      extrusion_split P (<[d := s]> σ) (Σd ∪ Σr) Tt (Cd ∪ Cr, Ed ⊎ Er).

Lemma extrusion_split_mono (P Q : senv → ty → proc → Prop) σ Σ T p :
  (∀ Σ' T' p', P Σ' T' p' → Q Σ' T' p') →
  extrusion_split P σ Σ T p → extrusion_split Q σ Σ T p.
Proof. induction 2; econstructor; eauto. Qed.

(** Process relation at level n. Differences from the term relation:

    - τ obligations are guarded by [p'.1 ## dom Σ]: a fork picks a
      globally fresh channel, and only names fresh for Σ as well are
      constrained (the paper's implicit "Σ and C do not share
      channels" well-formedness).
    - the input case additionally assumes the received channels are
      fresh for the restricted set ([dom Σ2 ## p.1]), for the same
      reason.
    - the output case (case 3, the ⌈updated⌉ one in Fig. 5) is the
      iterated form: sending w on c leaks the restricted channels
      dom σe = fchans w ∩ C; the residual splits into a continuation
      piece for c and one independent piece per extruded channel
      ([extrusion_split]), with the value typed against the duals of the
      pieces' types. *)
Definition Pdef (below : nat → level) (Vn : senv → ty → expr → Prop)
    (n : nat) (Σ : senv) (T : ty) (p : proc) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      (pirred p →
        ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vn Σ T v ∧
               (∀ e, e ∈ E → e = EUnit)) ∧
      (∀ π p', proc_step p π p' →
        match π with
        | PTau =>                                      (* case 1 *)
            p'.1 ## dom Σ →
            lP (below n') Σ T p'
        | PSess (SRecv c w) =>                         (* case 2 *)
            ∃ Σ1 U s,
              senv_hd Σ c (SRcv U s) Σ1 ∧ c ∉ dom Σ1 ∧
              ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 → dom Σ2 ## p.1 →
                lV (below j) Σ2 U w →
                lP (below j) (<[c := s]> (Σ1 ∪ Σ2)) T p'
        | PSess (SSend c w) =>                         (* case 3, iterated *)
            ∃ Σ0 Σv U s (σe : gmap chan sty) Σw C0 E0 Cw Ew T0 Tw,
              senv_hd Σ c (SSnd U s) (Σ0 ∪ Σv ∪ Σw) ∧
              Σ0 ##ₘ Σv ∧ Σ0 ##ₘ Σw ∧ Σv ##ₘ Σw ∧
              c ∉ dom Σ0 ∧ c ∉ dom Σv ∧ c ∉ dom Σw ∧
              dom σe = fchans w ∩ p.1 ∧
              dom σe ## dom Σ ∧ c ∉ dom σe ∧
              p'.1 = C0 ∪ Cw ∧ C0 ## Cw ∧
              p'.2 = E0 ⊎ Ew ∧
              Vn (Σv ∪ (dual <$> σe)) U w ∧
              lP (below n') (<[c := s]> Σ0) T0 (C0, E0) ∧
              extrusion_split (lP (below n')) σe Σw Tw (Cw, Ew) ∧
              ty_one_of T0 Tw T
        | PSess (SClos c) =>                           (* case 4 *)
            ∃ Σ1, senv_hd Σ c SEnd Σ1 ∧ c ∉ dom Σ1 ∧
              lP (below n') Σ1 T p'
        | PSess (SLink cd) =>                                  (* case 5, Fig. 10 *)
            ∃ c d Σ1 sc sd,
              cd = {[c; d]} ∧ c ≠ d ∧
              Σ = <[c := sc]> (<[d := sd]> Σ1) ∧
              c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧
              unfoldS sd = unfoldS (dual sc) ∧
              lP (below n') Σ1 T p'
        end)
  end.

Definition mk_level (below : nat → level) (n : nat) : level :=
  {| lV := Vdef below n;
     lE := Edef below (Vdef below n) n;
     lP := Pdef below (Vdef below n) n |}.

Definition dummy_level : level :=
  {| lV := λ _ _ _, False; lE := λ _ _ _, False; lP := λ _ _ _, False |}.

(** [levels n j] is level j, for every j < n (garbage above). *)
Fixpoint levels (n : nat) : nat → level :=
  match n with
  | 0 => λ _, dummy_level
  | S n' => λ j, if decide (j < n') then levels n' j else mk_level (levels n') n'
  end.

Definition level_at (n : nat) : level := levels (S n) n.

Definition Vrel (n : nat) : senv → ty → expr → Prop := lV (level_at n).
Definition Erel (n : nat) : senv → ty → expr → Prop := lE (level_at n).
Definition Prel (n : nat) : senv → ty → proc → Prop := lP (level_at n).

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

Lemma Erel_0 Σ T e : Erel 0 Σ T e.
Proof. unfold Erel. rewrite level_at_eq. simpl. exact I. Qed.

Lemma Prel_0 Σ T p : Prel 0 Σ T p.
Proof. unfold Prel. rewrite level_at_eq. simpl. exact I. Qed.

(** Members of the value relation are values. *)
Lemma Vdef_val below n Σ T v : Vdef below n Σ T v → is_val v.
Proof.
  induction T in Σ, v |- *; simpl.
  - by intros [_ ->].
  - by intros [(eb & -> & _ & _)|(k & -> & _)].
  - intros (v1 & v2 & Σ1 & Σ2 & -> & _ & H1 & H2).
    simpl. apply andb_True. eauto.
  - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
  - by intros (-> & eb & -> & _).
  - by intros (c & s0 & -> & _).
Qed.

Lemma Vrel_val n Σ T v : Vrel n Σ T v → is_val v.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_val. Qed.

(** Values in the relation mention exactly the channels of Σ: the
    linear discipline has no weakening, so a value owns precisely the
    channels occurring in it. Tightness (⊇) is essential for the
    compositionality of outputs — a component's decomposition may not
    park a restricted channel inside a value that never mentions it,
    or the channel's end would leak out of the composite unaccounted. *)
Lemma Vdef_fchans below n Σ T v :
  Vdef below n Σ T v → fchans v = dom Σ.
Proof.
  induction T in Σ, v |- *; simpl.
  - intros [-> ->]. simpl. by rewrite dom_empty_L.
  - intros [(eb & -> & Hsup & _)|(k & -> & -> & _)]; simpl;
      [done|by rewrite dom_empty_L].
  - intros (v1 & v2 & Σ1 & Σ2 & -> & [-> Hd] & H1 & H2). simpl.
    rewrite (IHT1 _ _ H1), (IHT2 _ _ H2), dom_union_L. done.
  - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
  - intros (-> & eb & -> & Hfc & _). simpl.
    rewrite Hfc. by rewrite dom_empty_L.
  - intros (c & s0 & -> & -> & _). simpl. by rewrite dom_singleton_L.
Qed.

Lemma Vrel_fchans n Σ T v : Vrel n Σ T v → fchans v = dom Σ.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_fchans. Qed.

(** Values of primitive type own no channels. *)
Lemma Vdef_prim_empty below n Σ T v :
  prim T → Vdef below n Σ T v → Σ = ∅.
Proof.
  intros Hp. revert Σ v. induction Hp; simpl.
  - by intros ? ? [-> _].
  - intros Σ v (v1 & v2 & Σ1 & Σ2 & -> & [-> Hd] & H1 & H2).
    rewrite (IHHp1 _ _ H1), (IHHp2 _ _ H2).
    apply (left_id ∅ (∪)).
  - intros Σ v [(v' & -> & H)|(v' & -> & H)]; eauto.
  - by intros Σ v (-> & _).
Qed.

Lemma Vrel_prim_empty n Σ T v : prim T → Vrel n Σ T v → Σ = ∅.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_prim_empty. Qed.

(** TLR-VAL: values in V are in E. *)
Lemma Vrel_Erel n Σ T v : Vrel n Σ T v → Erel n Σ T v.
Proof.
  intros HV. assert (is_val v) by eauto using Vrel_val.
  destruct n as [|n']; [apply Erel_0|].
  unfold Erel. rewrite level_at_eq. simpl. split_and!.
  - intros _. unfold Vrel in HV. rewrite level_at_eq in HV. exact HV.
  - intros α e' Hst. exfalso. eauto using val_no_tstep.
Qed.

(** Terminated shape of irreducible related processes. *)
Lemma Prel_S_irred n Σ T p :
  Prel (S n) Σ T p → pirred p →
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) Σ T v ∧
         (∀ e, e ∈ E → e = EUnit).
Proof.
  unfold Prel, Vrel. rewrite level_at_eq. simpl.
  intros (H1 & _) Hirr. exact (H1 Hirr).
Qed.

(** τ steps decrease the index by one (for τ successors whose
    restricted channels stay clear of Σ — always true for Σ = ∅). *)
Lemma Prel_S_tau n Σ T p p' :
  Prel (S n) Σ T p → preduction p p' → p'.1 ## dom Σ → Prel n Σ T p'.
Proof.
  unfold Prel at 1. rewrite level_at_eq. simpl.
  intros (_ & Hstep) Hred Hdisj.
  specialize (Hstep _ _ Hred). simpl in Hstep. specialize (Hstep Hdisj).
  destruct (decide (n < n)); [lia|].
  unfold Prel. rewrite level_at_eq. exact Hstep.
Qed.

(** With an empty session environment, no session-labelled transition
    is allowed by the relation. *)
Lemma Prel_S_empty_no_sess n T p σ p' :
  Prel (S n) ∅ T p → proc_step p (PSess σ) p' → False.
Proof.
  unfold Prel. rewrite level_at_eq. simpl.
  intros (_ & Hstep) Hp. specialize (Hstep _ _ Hp).
  destruct σ as [c w|c w|c|cd]; simpl in Hstep.
  - destruct Hstep as (Σ1 & U & s & Heq & _).
    exact (senv_hd_not_empty _ _ _ Heq).
  - destruct Hstep as (?&?&?&?&?&?&?&?&?&?&?&?&Heq&_).
    exact (senv_hd_not_empty _ _ _ Heq).
  - destruct Hstep as (Σ1 & Heq & _).
    exact (senv_hd_not_empty _ _ _ Heq).
  - (* forwarding: both ends must be in Σ *)
    destruct Hstep as (c & d & Σ1 & sc & sd & _ & _ & Heq & _).
    exact (insert_non_empty _ _ _ (eq_sym Heq)).
Qed.


(** ** Characteristic equations

    Encoding-free unfoldings of the three relations: [Vrel_*_iff] per
    type constructor, [Erel_S_iff] / [Prel_S_iff] per positive step
    index (via the case predicates [Ecase] / [Pcase]). All later
    proofs go through these and never touch [levels]/[level_at]. *)

Lemma Vrel_unit_iff n Σ v : Vrel n Σ TUnit v ↔ Σ = ∅ ∧ v = EUnit.
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_sess_iff n Σ s v :
  Vrel n Σ (TSess s) v ↔
  ∃ c s0, v = Chan c ∧ Σ = {[c := s0]} ∧ unfoldS s0 = unfoldS s.
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_prod_iff n Σ T U v :
  Vrel n Σ (TProd T U) v ↔
  ∃ v1 v2 Σ1 Σ2, v = Pair v1 v2 ∧ senv_split Σ Σ1 Σ2 ∧
    Vrel n Σ1 T v1 ∧ Vrel n Σ2 U v2.
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_sum_iff n Σ T U v :
  Vrel n Σ (TSum T U) v ↔
  (∃ v', v = Inj1 v' ∧ Vrel n Σ T v')
  ∨ (∃ v', v = Inj2 v' ∧ Vrel n Σ U v').
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_box_iff n Σ T v :
  Vrel n Σ (TBox T) v ↔
  Σ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
    ∀ j, j < n → Erel j ∅ T (subst1 (EBox eb) eb).
Proof.
  unfold Vrel, Erel. rewrite (level_at_eq n). cbn [mk_level lV Vdef].
  apply and_iff_compat_l.
  split; intros (eb & -> & Hfc & H); exists eb; (split_and!; [done..|]);
    intros j Hj.
  - rewrite <-(levels_at n j Hj). by apply H.
  - rewrite (levels_at n j Hj). by apply H.
Qed.

Lemma Vrel_box_empty n Σ T v : Vrel n Σ (TBox T) v → Σ = ∅.
Proof. intros [-> _]%Vrel_box_iff. done. Qed.

(** Values at an unlimited type own no channels. One case per
    modality; the structural rules only ever need this much. *)
Lemma Vrel_unl_empty n Σ T v : unlimited T → Vrel n Σ T v → Σ = ∅.
Proof. destruct T; try done. intros _. apply Vrel_box_empty. Qed.

Lemma Vrel_lolli_iff n Σ T U v :
  Vrel n Σ (TLolli T U) v ↔
  (∃ eb, v = Lam eb ∧ fchans eb = dom Σ ∧
     ∀ j Σ' w, j < n → Σ' ##ₘ Σ →
       Vrel j Σ' T w → Erel j (Σ ∪ Σ') U (subst1 w eb))
  ∨ (∃ k, v = Konst k ∧ Σ = ∅ ∧ konst_ty k (TLolli T U)).
Proof.
  unfold Vrel, Erel. rewrite (level_at_eq n). cbn [mk_level lV Vdef].
  apply or_iff_compat_r.
  split; intros (eb & -> & Hsup & H); exists eb; (split_and!; [done..|]);
    intros j Σ' w Hj Hd HV.
  - rewrite <-(levels_at n j Hj). apply H; auto.
    rewrite (levels_at n j Hj). exact HV.
  - rewrite (levels_at n j Hj). apply H; auto.
    rewrite <-(levels_at n j Hj). exact HV.
Qed.

(** The step-clause cases of the term relation at index S n'. *)
Definition Ecase (n' : nat) (Σ : senv) (T : ty) (α : tlabel) (e' : expr)
    : Prop :=
  match α with
  | LBeta =>
      Erel n' Σ T e'
  | LFork c w =>
      c ∉ dom Σ →
      ∃ Σ1 Σ2 s,
        senv_split Σ Σ1 Σ2 ∧
        Vrel (S n') Σ1 (TLolli (TSess s) TUnit) w ∧
        Erel n' (<[c := dual s]> Σ2) T e'
  | LSess (SRecv c w) =>
      ∃ Σ1 U s,
        senv_hd Σ c (SRcv U s) Σ1 ∧ c ∉ dom Σ1 ∧
        ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 →
          Vrel j Σ2 U w →
          Erel j (<[c := s]> (Σ1 ∪ Σ2)) T e'
  | LSess (SSend c w) =>
      ∃ Σ1 Σ2 U s,
        senv_hd Σ c (SSnd U s) (Σ1 ∪ Σ2) ∧
        Σ1 ##ₘ Σ2 ∧ c ∉ dom Σ1 ∧ c ∉ dom Σ2 ∧
        Vrel (S n') Σ2 U w ∧
        Erel n' (<[c := s]> Σ1) T e'
  | LSess (SClos c) =>
      ∃ Σ1, senv_hd Σ c SEnd Σ1 ∧ c ∉ dom Σ1 ∧ Erel n' Σ1 T e'
  | LSess (SLink cd) =>
      ∃ c d Σ1 sc sd,
        cd = {[c; d]} ∧ c ≠ d ∧
        Σ = <[c := sc]> (<[d := sd]> Σ1) ∧
        c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧
        unfoldS sd = unfoldS (dual sc) ∧
        Erel n' Σ1 T e'
  end.

Lemma Erel_S_iff n Σ T e :
  Erel (S n) Σ T e ↔
    (irred e → Vrel (S n) Σ T e) ∧
    (∀ α e', tstep e α e' → Ecase n Σ T α e').
Proof.
  unfold Ecase, Erel, Vrel. rewrite (level_at_eq (S n)).
  cbn [mk_level lV lE Edef].
  rewrite (levels_at (S n) n (Nat.lt_succ_diag_r n)).
  apply and_iff_compat_l.
  split; intros H α e' Hst; specialize (H α e' Hst);
    destruct α as [|[c w|c w|c|cd]|c w]; try exact H.
  - (* recv, → *)
    destruct H as (Σ1 & U & s & HΣ & Hc & H).
    exists Σ1, U, s. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd HV.
    rewrite <-(levels_at (S n) j) in HV by lia.
    specialize (H j Σ2 Hj Hd Hcd HV).
    rewrite (levels_at (S n) j) in H by lia. exact H.
  - (* recv, ← *)
    destruct H as (Σ1 & U & s & HΣ & Hc & H).
    exists Σ1, U, s. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd HV.
    rewrite (levels_at (S n) j) in HV by lia.
    specialize (H j Σ2 Hj Hd Hcd HV).
    rewrite <-(levels_at (S n) j) in H by lia. exact H.
Qed.

(** The step-clause cases of the process relation at index S n'. *)
Definition Pcase (n' : nat) (Σ : senv) (T : ty) (p : proc) (π : plabel)
    (p' : proc) : Prop :=
  match π with
  | PTau =>
      p'.1 ## dom Σ →
      Prel n' Σ T p'
  | PSess (SRecv c w) =>
      ∃ Σ1 U s,
        senv_hd Σ c (SRcv U s) Σ1 ∧ c ∉ dom Σ1 ∧
        ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 → dom Σ2 ## p.1 →
          Vrel j Σ2 U w →
          Prel j (<[c := s]> (Σ1 ∪ Σ2)) T p'
  | PSess (SSend c w) =>
      ∃ Σ0 Σv U s (σe : gmap chan sty) Σw C0 E0 Cw Ew T0 Tw,
        senv_hd Σ c (SSnd U s) (Σ0 ∪ Σv ∪ Σw) ∧
        Σ0 ##ₘ Σv ∧ Σ0 ##ₘ Σw ∧ Σv ##ₘ Σw ∧
        c ∉ dom Σ0 ∧ c ∉ dom Σv ∧ c ∉ dom Σw ∧
        dom σe = fchans w ∩ p.1 ∧
        dom σe ## dom Σ ∧ c ∉ dom σe ∧
        p'.1 = C0 ∪ Cw ∧ C0 ## Cw ∧
        p'.2 = E0 ⊎ Ew ∧
        Vrel (S n') (Σv ∪ (dual <$> σe)) U w ∧
        Prel n' (<[c := s]> Σ0) T0 (C0, E0) ∧
        extrusion_split (Prel n') σe Σw Tw (Cw, Ew) ∧
        ty_one_of T0 Tw T
  | PSess (SClos c) =>
      ∃ Σ1, senv_hd Σ c SEnd Σ1 ∧ c ∉ dom Σ1 ∧ Prel n' Σ1 T p'
  | PSess (SLink cd) =>
      ∃ c d Σ1 sc sd,
        cd = {[c; d]} ∧ c ≠ d ∧
        Σ = <[c := sc]> (<[d := sd]> Σ1) ∧
        c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧
        unfoldS sd = unfoldS (dual sc) ∧
        Prel n' Σ1 T p'
  end.

Lemma Prel_S_iff n Σ T p :
  Prel (S n) Σ T p ↔
    (pirred p →
      ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) Σ T v ∧
             (∀ e, e ∈ E → e = EUnit)) ∧
    (∀ π p', proc_step p π p' → Pcase n Σ T p π p').
Proof.
  unfold Pcase, Prel, Vrel. rewrite (level_at_eq (S n)).
  cbn [mk_level lV lP Pdef].
  rewrite (levels_at (S n) n (Nat.lt_succ_diag_r n)).
  apply and_iff_compat_l.
  split; intros H π p' Hst; specialize (H π p' Hst);
    destruct π as [|[c w|c w|c|cd]]; try exact H.
  - (* recv, → *)
    destruct H as (Σ1 & U & s & HΣ & Hc & H).
    exists Σ1, U, s. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd Hfr HV.
    rewrite <-(levels_at (S n) j) in HV by lia.
    specialize (H j Σ2 Hj Hd Hcd Hfr HV).
    rewrite (levels_at (S n) j) in H by lia. exact H.
  - (* recv, ← *)
    destruct H as (Σ1 & U & s & HΣ & Hc & H).
    exists Σ1, U, s. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd Hfr HV.
    rewrite (levels_at (S n) j) in HV by lia.
    specialize (H j Σ2 Hj Hd Hcd Hfr HV).
    rewrite <-(levels_at (S n) j) in H by lia. exact H.
Qed.

(** Convenient corollaries of the characteristic equations. *)
Lemma Prel_S_intro n Σ T p :
  (pirred p →
    ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) Σ T v ∧
           (∀ e, e ∈ E → e = EUnit)) →
  (∀ π p', proc_step p π p' → Pcase n Σ T p π p') →
  Prel (S n) Σ T p.
Proof. intros. apply Prel_S_iff. done. Qed.

Lemma Prel_S_step n Σ T p π p' :
  Prel (S n) Σ T p → proc_step p π p' → Pcase n Σ T p π p'.
Proof. intros HP Hst. apply Prel_S_iff in HP as (_ & H). auto. Qed.

Lemma Erel_S_step n Σ T e α e' :
  Erel (S n) Σ T e → tstep e α e' → Ecase n Σ T α e'.
Proof. intros HE Hst. apply Erel_S_iff in HE as (_ & H). auto. Qed.

(** ** Semantic judgments (Defs. 3.2 and 3.3) *)

(** Grounding substitutions G_n⟦Σ; Δ⟧: substitutions assigning to each
    available variable of Δ a value in the value relation, splitting Σ
    among them. *)
Fixpoint grounding (n : nat) (Σ : senv) (Δ : lenv) (γ : nat → expr) : Prop :=
  match Δ with
  | [] => Σ = ∅
  | None :: Δ' => grounding n Σ Δ' (γ ∘ S)
  | Some T :: Δ' =>
      ∃ Σ1 Σ2, senv_split Σ Σ1 Σ2 ∧ Vrel n Σ1 T (γ 0) ∧
               grounding n Σ2 Δ' (γ ∘ S)
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

(** Σ; Δ ⊨ e : T.  The channels of e itself are covered by Σ; the
    grounding substitution brings its own (disjoint) Σ'. (Def. 3.3;
    the draft's phrasing conflates the two environments — this is the
    reading under which the rules of Fig. 4, e.g. E-Ch, are
    non-vacuous.)

    The judgment additionally records three pieces of syntactic
    well-formedness that the paper leaves implicit but that Fig. 4's
    linear rules maintain and the ⊸-case of V requires: the channels
    of e are exactly dom Σ, the free variables of e are available in
    Δ, and — relevance, i.e. absence of weakening — every available
    variable of Δ occurs in e. Without them the E-Abs rule (Thm 3.11)
    is false: a λ-value must own exactly its channels. *)
Definition sem_typed (Σ : senv) (Δ : lenv) (e : expr) (T : ty) : Prop :=
  fchans e = dom Σ ∧
  allfv (lenv_avail Δ) e ∧
  (∀ x, lenv_avail_lin Δ x → freevar x e) ∧
  ∀ n Σ' γ, Σ' ##ₘ Σ → grounding n Σ' Δ γ →
    Erel n (Σ ∪ Σ') T (subst γ e).

(** Σ ⊨ p : T *)
Definition sem_ptyped (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ n, Prel n Σ T p.

(** ** The adequacy chain (Lemmas 3.4, 3.5 and Theorem 3.6) *)

(** Lemma 3.4 (for the closed environment, which is what adequacy
    needs; the τ-guard is trivially satisfied at Σ = ∅). *)
Lemma Prel_steps m n T p p' :
  nsteps preduction m p p' → Prel (m + n) ∅ T p → Prel n ∅ T p'.
Proof.
  induction 1 as [|m' x y z Hxy Hyz IH]; simpl; [done|].
  intros HP. apply IH. eapply Prel_S_tau; [done..|]. set_solver.
Qed.

(** Lemma 3.5 *)
Lemma Prel_safe n T p : Prel (S n) ∅ T p → safe p.
Proof.
  intros HP. destruct (proc_progress p) as [Hirr|(π & p' & Hst)].
  - left. destruct (Prel_S_irred _ _ _ _ HP Hirr) as (v & E & -> & Hv & _ & HE).
    exists v, E. auto.
  - right. destruct π as [|σ].
    + by exists p'.
    + exfalso. by eapply Prel_S_empty_no_sess.
Qed.

(** Theorem 3.6 (Adequacy) *)
Theorem adequacy T p : sem_ptyped ∅ p T → deadlock_free p.
Proof.
  intros HP p' Hsteps. apply rtc_nsteps_1 in Hsteps as [m Hm].
  eapply (Prel_safe 0). eapply Prel_steps; [exact Hm|]. exact (HP (m + 1)).
Qed.

(** ** Downward closure (Lemma 3.7) *)

Lemma Vrel_down n m Σ T v : m ≤ n → Vrel n Σ T v → Vrel m Σ T v.
Proof.
  intros Hle. induction T in Σ, v |- *.
  - rewrite !Vrel_unit_iff. done.
  - rewrite !Vrel_lolli_iff.
    intros [(eb & -> & Hsup & H)|Hk]; [left|by right].
    exists eb. split_and!; [done..|]. intros j Σ' w Hj Hd HV.
    apply H; auto. lia.
  - rewrite !Vrel_prod_iff.
    intros (v1 & v2 & Σ1 & Σ2 & -> & Hsp & H1 & H2).
    eexists _, _, _, _. split_and!; eauto.
  - rewrite !Vrel_sum_iff.
    intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
  - rewrite !Vrel_box_iff.
    intros (-> & eb & -> & Hfc & H). split; [done|].
    exists eb. split_and!; [done|done|]. intros j Hj. apply H. lia.
  - rewrite !Vrel_sess_iff. done.
Qed.

Lemma Erel_down n m Σ T e : m ≤ n → Erel n Σ T e → Erel m Σ T e.
Proof.
  revert n Σ T e. induction m as [|m' IH]; intros n Σ T e Hle HE;
    [apply Erel_0|].
  destruct n as [|n']; [lia|].
  apply Erel_S_iff in HE as (H1 & H2).
  apply Erel_S_iff. split_and!.
  - intros He. eapply Vrel_down; [|by apply H1]. lia.
  - intros α e' Hst. specialize (H2 α e' Hst).
    destruct α as [|[c w|c w|c|cd]|c w]; simpl in H2 |- *.
    + eapply IH; [|exact H2]. lia.
    + destruct H2 as (Σ1 & U & s & Hhd & Hc & H2).
      eexists _, _, _. split_and!; [done|done|].
      intros j Σ2 Hj Hd Hcd HV. apply H2; auto. lia.
    + destruct H2 as (Σ1 & Σ2 & U & s & Hhd & ? & ? & ? & HV & HE').
      eexists _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * eapply IH; [|exact HE']. lia.
    + destruct H2 as (Σ1 & Hhd & ? & HE').
      eexists. split_and!; eauto. eapply IH; [|done]. lia.
    + destruct H2 as (c & d & Σ1 & sc & sd & -> & ? & -> & ? & ? & ? & HE').
      eexists _, _, _, _, _. split_and!; [done..|]. eapply IH; [|done]. lia.
    + intros Hc. destruct (H2 Hc) as (Σ1 & Σ2 & s & ? & HV & HE').
      eexists _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * eapply IH; [|done]. lia.
Qed.

Lemma Prel_down n m Σ T p : m ≤ n → Prel n Σ T p → Prel m Σ T p.
Proof.
  revert n Σ T p. induction m as [|m' IH]; intros n Σ T p Hle HP;
    [apply Prel_0|].
  destruct n as [|n']; [lia|].
  apply Prel_S_iff in HP as (H1 & H2).
  apply Prel_S_iff. split_and!.
  - intros Hirr. destruct (H1 Hirr) as (v & E & -> & ? & HV & ?).
    eexists _, _. split_and!; eauto. eapply Vrel_down; [|exact HV]. lia.
  - intros π p' Hst. specialize (H2 π p' Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in H2 |- *.
    + intros Hd. eapply IH; [|by apply H2]. lia.
    + destruct H2 as (Σ1 & U & s & Hhd & Hc & H2).
      eexists _, _, _. split_and!; [done|done|].
      intros j Σ2 Hj Hd Hcd Hfr HV. apply H2; auto. lia.
    + destruct H2 as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew &
                      T0 & Tw & Hhd & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      ? & ? & ? & HV & HP0 & HPw & ?).
      eexists _, _, _, _, _, _, _, _, _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * eapply IH; [|exact HP0]. lia.
      * eapply extrusion_split_mono; [|exact HPw].
        intros ? ? ? ?. eapply IH; [|eauto]. lia.
    + destruct H2 as (Σ1 & Hhd & ? & HP').
      eexists. split_and!; eauto. eapply IH; [|done]. lia.
    + destruct H2 as (c & d & Σ1 & sc & sd & -> & ? & -> & ? & ? & ? & HP').
      eexists _, _, _, _, _. split_and!; [done..|]. eapply IH; [|done]. lia.
Qed.
