(** * The logical relation (Fig. 5) and semantic typing (§3)

    Three step-indexed layers:
      V_n⟦Σ ⊢ T⟧  values      ([Vrel])
      E_n⟦Σ ⊢ T⟧  terms       ([Erel])
      P_n⟦Σ ⊢ T⟧  processes   ([Prel])

    The step-index recursion is implemented by course-of-values
    recursion on n: [fam n] is (structurally in n) the family of all
    levels below n, [mk_level below n] builds level n from it, and
    [lvl n] projects the actual level n. Later proofs only use the
    equations [lvl_eq] and [fam_lvl], never the encoding.

    "Σ = Σ1, c : S" from the paper is rendered as
    Σ = <[c := S]> Σ1 together with c ∉ dom Σ1.

    Proofs of Lemma 3.5 use classical logic (the paper's argument "if p
    is not irreducible then it has some transition"); the alternative
    would be proving decidability of reducibility, which the paper's
    Agda mechanization also lists as tedious. *)

From Coq Require Import Classical.
From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Processes Types Typing.

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
  | TSess s => ∃ c, v = Chan c ∧ Σ = {[c := s]}
  | TLolli T1 U =>
      (∃ eb, v = Lam eb ∧ fchans eb = dom Σ ∧
         ∀ j Σ' w, j < n → Σ' ##ₘ Σ →
           lV (below j) Σ' T1 w →
           lE (below j) (Σ ∪ Σ') U (subst1 w eb))
      ∨ (∃ k, v = Konst k ∧ Σ = ∅ ∧ konst_ty k (TLolli T1 U))
  | TProd T1 U =>
      ∃ v1 v2 Σ1 Σ2, v = Pair v1 v2 ∧ senv_split Σ Σ1 Σ2 ∧
        Vdef below n Σ1 T1 v1 ∧ Vdef below n Σ2 U v2
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
              Σ = <[c := SRcv U s]> Σ1 ∧ c ∉ dom Σ1 ∧
              ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 →
                lV (below j) Σ2 U w →
                lE (below j) (<[c := s]> (Σ1 ∪ Σ2)) T e'
        | LSess (SSend c w) =>                         (* case 4 *)
            ∃ Σ1 Σ2 U s,
              Σ = <[c := SSnd U s]> (Σ1 ∪ Σ2) ∧
              Σ1 ##ₘ Σ2 ∧ c ∉ dom Σ1 ∧ c ∉ dom Σ2 ∧
              Vn Σ2 U w ∧
              lE (below n') (<[c := s]> Σ1) T e'
        | LSess (SClos c) =>                           (* case 5 *)
            ∃ Σ1, Σ = <[c := SEnd]> Σ1 ∧ c ∉ dom Σ1 ∧
              lE (below n') Σ1 T e'
        end)
  end.

(** Type bookkeeping for splitting a process into pieces: of the two
    return types, at most one is not ∗ and it determines the total. *)
Definition ty_one_of (A B C : ty) : Prop :=
  (A = C ∧ B = TUnit) ∨ (A = TUnit ∧ B = C).

(** Iterated decomposition into escaped-channel owners.

    [Powners P σ Σ T p]: the process p decomposes into a family of
    pairwise independent processes, exactly one per channel d ∈ dom σ,
    where the piece for d is in the (parameter) process relation P at
    environment Σd, d : σ(d) — it owns the residual end of d. Σ
    accumulates the Σd's (without the d's themselves) and T the return
    types (at most one ≠ ∗). The base case is the degenerate empty
    process: for no escaped channels, nothing needs to remain.

    This is the iterated form of Fig. 5's ⌈updated⌉ case 3: instead of
    one process owning all escaped channels, one process per escaped
    channel. A single piece owning two escaped channels would create a
    potential cyclic dependency through the environment, so the finer
    decomposition is the semantically meaningful invariant, and it is
    what the compositionality proofs need when a communication
    transfers several restricted channels at once: each transferred
    channel is reconnected to its own owner piece separately. *)
Inductive Powners (P : senv → ty → proc → Prop)
    : gmap chan sty → senv → ty → proc → Prop :=
  | Powners_nil : Powners P ∅ ∅ TUnit (∅, ∅)
  | Powners_cons σ d s Σd Σr Td Tr Tt Cd Ed Cr Er :
      σ !! d = None →
      d ∉ dom Σd → d ∉ dom Σr → d ∉ Cd → d ∉ Cr →
      dom σ ## dom Σd → dom σ ## Cd →
      Σd ##ₘ Σr → Cd ## Cr → Cd ## dom Σr → Cr ## dom Σd →
      P (<[d := s]> Σd) Td (Cd, Ed) →
      Powners P σ Σr Tr (Cr, Er) →
      ty_one_of Td Tr Tt →
      Powners P (<[d := s]> σ) (Σd ∪ Σr) Tt (Cd ∪ Cr, Ed ⊎ Er).

Lemma Powners_mono (P Q : senv → ty → proc → Prop) σ Σ T p :
  (∀ Σ' T' p', P Σ' T' p' → Q Σ' T' p') →
  Powners P σ Σ T p → Powners Q σ Σ T p.
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
      piece for c and one independent owner piece per escaped channel
      ([Powners]), with the value typed against the duals of the
      owners' types. *)
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
              Σ = <[c := SRcv U s]> Σ1 ∧ c ∉ dom Σ1 ∧
              ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 → dom Σ2 ## p.1 →
                lV (below j) Σ2 U w →
                lP (below j) (<[c := s]> (Σ1 ∪ Σ2)) T p'
        | PSess (SSend c w) =>                         (* case 3, iterated *)
            ∃ Σ0 Σv U s (σe : gmap chan sty) Σw C0 E0 Cw Ew T0 Tw,
              Σ = <[c := SSnd U s]> (Σ0 ∪ Σv ∪ Σw) ∧
              Σ0 ##ₘ Σv ∧ Σ0 ##ₘ Σw ∧ Σv ##ₘ Σw ∧
              c ∉ dom Σ0 ∧ c ∉ dom Σv ∧ c ∉ dom Σw ∧
              dom σe = fchans w ∩ p.1 ∧
              dom σe ## dom Σ ∧ c ∉ dom σe ∧
              p'.1 = C0 ∪ Cw ∧ C0 ## Cw ∧
              p'.2 = E0 ⊎ Ew ∧
              Vn (Σv ∪ (dual <$> σe)) U w ∧
              lP (below n') (<[c := s]> Σ0) T0 (C0, E0) ∧
              Powners (lP (below n')) σe Σw Tw (Cw, Ew) ∧
              ty_one_of T0 Tw T
        | PSess (SClos c) =>                           (* case 4 *)
            ∃ Σ1, Σ = <[c := SEnd]> Σ1 ∧ c ∉ dom Σ1 ∧
              lP (below n') Σ1 T p'
        end)
  end.

Definition mk_level (below : nat → level) (n : nat) : level :=
  {| lV := Vdef below n;
     lE := Edef below (Vdef below n) n;
     lP := Pdef below (Vdef below n) n |}.

Definition dummy_level : level :=
  {| lV := λ _ _ _, False; lE := λ _ _ _, False; lP := λ _ _ _, False |}.

(** [fam n j] is level j, for every j < n (garbage above). *)
Fixpoint fam (n : nat) : nat → level :=
  match n with
  | 0 => λ _, dummy_level
  | S n' => λ j, if decide (j < n') then fam n' j else mk_level (fam n') n'
  end.

Definition lvl (n : nat) : level := fam (S n) n.

Definition Vrel (n : nat) : senv → ty → expr → Prop := lV (lvl n).
Definition Erel (n : nat) : senv → ty → expr → Prop := lE (lvl n).
Definition Prel (n : nat) : senv → ty → proc → Prop := lP (lvl n).

(** ** Interface to the encoding *)

Lemma lvl_eq n : lvl n = mk_level (fam n) n.
Proof. unfold lvl. simpl. by destruct (decide (n < n)); [lia|]. Qed.

Lemma fam_lvl n j : j < n → fam n j = lvl j.
Proof.
  revert j. induction n as [|n' IH]; intros j Hj; [lia|].
  simpl. destruct (decide (j < n')) as [H|H].
  - by apply IH.
  - assert (j = n') as -> by lia. by rewrite lvl_eq.
Qed.

Lemma Erel_0 Σ T e : Erel 0 Σ T e.
Proof. unfold Erel. rewrite lvl_eq. simpl. exact I. Qed.

Lemma Prel_0 Σ T p : Prel 0 Σ T p.
Proof. unfold Prel. rewrite lvl_eq. simpl. exact I. Qed.

(** Members of the value relation are values. *)
Lemma Vdef_val below n Σ T v : Vdef below n Σ T v → is_val v.
Proof.
  induction T in Σ, v |- *; simpl.
  - by intros [_ ->].
  - by intros [(eb & -> & _ & _)|(k & -> & _)].
  - intros (v1 & v2 & Σ1 & Σ2 & -> & _ & H1 & H2).
    simpl. apply andb_True. eauto.
  - by intros (c & -> & _).
Qed.

Lemma Vrel_val n Σ T v : Vrel n Σ T v → is_val v.
Proof. unfold Vrel. rewrite lvl_eq. apply Vdef_val. Qed.

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
  - intros (c & -> & ->). simpl. by rewrite dom_singleton_L.
Qed.

Lemma Vrel_fchans n Σ T v : Vrel n Σ T v → fchans v = dom Σ.
Proof. unfold Vrel. rewrite lvl_eq. apply Vdef_fchans. Qed.

(** Values of primitive type own no channels. *)
Lemma Vdef_prim_empty below n Σ T v :
  prim T → Vdef below n Σ T v → Σ = ∅.
Proof.
  intros Hp. revert Σ v. induction Hp; simpl.
  - by intros ? ? [-> _].
  - intros Σ v (v1 & v2 & Σ1 & Σ2 & -> & [-> Hd] & H1 & H2).
    rewrite (IHHp1 _ _ H1), (IHHp2 _ _ H2).
    apply (left_id ∅ (∪)).
Qed.

Lemma Vrel_prim_empty n Σ T v : prim T → Vrel n Σ T v → Σ = ∅.
Proof. unfold Vrel. rewrite lvl_eq. apply Vdef_prim_empty. Qed.

(** TLR-VAL: values in V are in E. *)
Lemma Vrel_Erel n Σ T v : Vrel n Σ T v → Erel n Σ T v.
Proof.
  intros HV. assert (is_val v) by eauto using Vrel_val.
  destruct n as [|n']; [apply Erel_0|].
  unfold Erel. rewrite lvl_eq. simpl. split.
  - intros _. unfold Vrel in HV. rewrite lvl_eq in HV. exact HV.
  - intros α e' Hst. exfalso. eauto using val_no_tstep.
Qed.

(** Terminated shape of irreducible related processes. *)
Lemma Prel_S_irred n Σ T p :
  Prel (S n) Σ T p → pirred p →
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) Σ T v ∧
         (∀ e, e ∈ E → e = EUnit).
Proof.
  unfold Prel, Vrel. rewrite lvl_eq. simpl.
  intros [H1 _] Hirr. exact (H1 Hirr).
Qed.

(** τ steps decrease the index by one (for τ successors whose
    restricted channels stay clear of Σ — always true for Σ = ∅). *)
Lemma Prel_S_tau n Σ T p p' :
  Prel (S n) Σ T p → preduction p p' → p'.1 ## dom Σ → Prel n Σ T p'.
Proof.
  unfold Prel at 1. rewrite lvl_eq. simpl.
  intros [_ Hstep] Hred Hdisj.
  specialize (Hstep _ _ Hred). simpl in Hstep. specialize (Hstep Hdisj).
  destruct (decide (n < n)); [lia|].
  unfold Prel. rewrite lvl_eq. exact Hstep.
Qed.

(** With an empty session environment, no session-labelled transition
    is allowed by the relation. *)
Lemma Prel_S_empty_no_sess n T p σ p' :
  Prel (S n) ∅ T p → proc_step p (PSess σ) p' → False.
Proof.
  unfold Prel. rewrite lvl_eq. simpl.
  intros [_ Hstep] Hp. specialize (Hstep _ _ Hp).
  destruct σ as [c w|c w|c]; simpl in Hstep.
  - destruct Hstep as (Σ1 & U & s & Heq & _).
    exact (insert_non_empty _ _ _ (eq_sym Heq)).
  - destruct Hstep as (?&?&?&?&?&?&?&?&?&?&?&?&Heq&_).
    exact (insert_non_empty _ _ _ (eq_sym Heq)).
  - destruct Hstep as (Σ1 & Heq & _).
    exact (insert_non_empty _ _ _ (eq_sym Heq)).
Qed.

(** ** Characteristic equations

    Encoding-free unfoldings of the three relations: [Vrel_*_iff] per
    type constructor, [Erel_S_iff] / [Prel_S_iff] per positive step
    index (via the case predicates [Ecase] / [Pcase]). All later
    proofs go through these and never touch [fam]/[lvl]. *)

Lemma Vrel_unit_iff n Σ v : Vrel n Σ TUnit v ↔ Σ = ∅ ∧ v = EUnit.
Proof. unfold Vrel. rewrite (lvl_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_sess_iff n Σ s v :
  Vrel n Σ (TSess s) v ↔ ∃ c, v = Chan c ∧ Σ = {[c := s]}.
Proof. unfold Vrel. rewrite (lvl_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_prod_iff n Σ T U v :
  Vrel n Σ (TProd T U) v ↔
  ∃ v1 v2 Σ1 Σ2, v = Pair v1 v2 ∧ senv_split Σ Σ1 Σ2 ∧
    Vrel n Σ1 T v1 ∧ Vrel n Σ2 U v2.
Proof. unfold Vrel. rewrite (lvl_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_lolli_iff n Σ T U v :
  Vrel n Σ (TLolli T U) v ↔
  (∃ eb, v = Lam eb ∧ fchans eb = dom Σ ∧
     ∀ j Σ' w, j < n → Σ' ##ₘ Σ →
       Vrel j Σ' T w → Erel j (Σ ∪ Σ') U (subst1 w eb))
  ∨ (∃ k, v = Konst k ∧ Σ = ∅ ∧ konst_ty k (TLolli T U)).
Proof.
  unfold Vrel, Erel. rewrite (lvl_eq n). cbn [mk_level lV Vdef].
  apply or_iff_compat_r.
  split; intros (eb & -> & Hsup & H); exists eb; (split_and!; [done..|]);
    intros j Σ' w Hj Hd HV.
  - rewrite <-(fam_lvl n j Hj). apply H; auto.
    rewrite (fam_lvl n j Hj). exact HV.
  - rewrite (fam_lvl n j Hj). apply H; auto.
    rewrite <-(fam_lvl n j Hj). exact HV.
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
        Σ = <[c := SRcv U s]> Σ1 ∧ c ∉ dom Σ1 ∧
        ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 →
          Vrel j Σ2 U w →
          Erel j (<[c := s]> (Σ1 ∪ Σ2)) T e'
  | LSess (SSend c w) =>
      ∃ Σ1 Σ2 U s,
        Σ = <[c := SSnd U s]> (Σ1 ∪ Σ2) ∧
        Σ1 ##ₘ Σ2 ∧ c ∉ dom Σ1 ∧ c ∉ dom Σ2 ∧
        Vrel (S n') Σ2 U w ∧
        Erel n' (<[c := s]> Σ1) T e'
  | LSess (SClos c) =>
      ∃ Σ1, Σ = <[c := SEnd]> Σ1 ∧ c ∉ dom Σ1 ∧ Erel n' Σ1 T e'
  end.

Lemma Erel_S_iff n Σ T e :
  Erel (S n) Σ T e ↔
    (irred e → Vrel (S n) Σ T e) ∧
    (∀ α e', tstep e α e' → Ecase n Σ T α e').
Proof.
  unfold Ecase, Erel, Vrel. rewrite (lvl_eq (S n)).
  cbn [mk_level lV lE Edef].
  rewrite (fam_lvl (S n) n (Nat.lt_succ_diag_r n)).
  apply and_iff_compat_l.
  split; intros H α e' Hst; specialize (H α e' Hst);
    destruct α as [|[c w|c w|c]|c w]; try exact H.
  - (* recv, → *)
    destruct H as (Σ1 & U & s & HΣ & Hc & H).
    exists Σ1, U, s. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd HV.
    rewrite <-(fam_lvl (S n) j) in HV by lia.
    specialize (H j Σ2 Hj Hd Hcd HV).
    rewrite (fam_lvl (S n) j) in H by lia. exact H.
  - (* recv, ← *)
    destruct H as (Σ1 & U & s & HΣ & Hc & H).
    exists Σ1, U, s. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd HV.
    rewrite (fam_lvl (S n) j) in HV by lia.
    specialize (H j Σ2 Hj Hd Hcd HV).
    rewrite <-(fam_lvl (S n) j) in H by lia. exact H.
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
        Σ = <[c := SRcv U s]> Σ1 ∧ c ∉ dom Σ1 ∧
        ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 → dom Σ2 ## p.1 →
          Vrel j Σ2 U w →
          Prel j (<[c := s]> (Σ1 ∪ Σ2)) T p'
  | PSess (SSend c w) =>
      ∃ Σ0 Σv U s (σe : gmap chan sty) Σw C0 E0 Cw Ew T0 Tw,
        Σ = <[c := SSnd U s]> (Σ0 ∪ Σv ∪ Σw) ∧
        Σ0 ##ₘ Σv ∧ Σ0 ##ₘ Σw ∧ Σv ##ₘ Σw ∧
        c ∉ dom Σ0 ∧ c ∉ dom Σv ∧ c ∉ dom Σw ∧
        dom σe = fchans w ∩ p.1 ∧
        dom σe ## dom Σ ∧ c ∉ dom σe ∧
        p'.1 = C0 ∪ Cw ∧ C0 ## Cw ∧
        p'.2 = E0 ⊎ Ew ∧
        Vrel (S n') (Σv ∪ (dual <$> σe)) U w ∧
        Prel n' (<[c := s]> Σ0) T0 (C0, E0) ∧
        Powners (Prel n') σe Σw Tw (Cw, Ew) ∧
        ty_one_of T0 Tw T
  | PSess (SClos c) =>
      ∃ Σ1, Σ = <[c := SEnd]> Σ1 ∧ c ∉ dom Σ1 ∧ Prel n' Σ1 T p'
  end.

Lemma Prel_S_iff n Σ T p :
  Prel (S n) Σ T p ↔
    (pirred p →
      ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) Σ T v ∧
             (∀ e, e ∈ E → e = EUnit)) ∧
    (∀ π p', proc_step p π p' → Pcase n Σ T p π p').
Proof.
  unfold Pcase, Prel, Vrel. rewrite (lvl_eq (S n)).
  cbn [mk_level lV lP Pdef].
  rewrite (fam_lvl (S n) n (Nat.lt_succ_diag_r n)).
  apply and_iff_compat_l.
  split; intros H π p' Hst; specialize (H π p' Hst);
    destruct π as [|[c w|c w|c]]; try exact H.
  - (* recv, → *)
    destruct H as (Σ1 & U & s & HΣ & Hc & H).
    exists Σ1, U, s. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd Hfr HV.
    rewrite <-(fam_lvl (S n) j) in HV by lia.
    specialize (H j Σ2 Hj Hd Hcd Hfr HV).
    rewrite (fam_lvl (S n) j) in H by lia. exact H.
  - (* recv, ← *)
    destruct H as (Σ1 & U & s & HΣ & Hc & H).
    exists Σ1, U, s. split_and!; [done|done|].
    intros j Σ2 Hj Hd Hcd Hfr HV.
    rewrite (fam_lvl (S n) j) in HV by lia.
    specialize (H j Σ2 Hj Hd Hcd Hfr HV).
    rewrite <-(fam_lvl (S n) j) in H by lia. exact H.
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
Proof. intros HP Hst. apply Prel_S_iff in HP as [_ H]. auto. Qed.

Lemma Erel_S_step n Σ T e α e' :
  Erel (S n) Σ T e → tstep e α e' → Ecase n Σ T α e'.
Proof. intros HE Hst. apply Erel_S_iff in HE as [_ H]. auto. Qed.

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
  (∀ x, lenv_avail Δ x → freevar x e) ∧
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
  intros HP. destruct (classic (pirred p)) as [Hirr|Hnirr].
  - left. destruct (Prel_S_irred _ _ _ _ HP Hirr) as (v & E & -> & Hv & _ & HE).
    exists v, E. auto.
  - right. apply not_all_ex_not in Hnirr as [π Hπ].
    apply not_all_ex_not in Hπ as [p' Hp'].
    apply NNPP in Hp'.
    destruct π as [|σ].
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
  - rewrite !Vrel_sess_iff. done.
Qed.

Lemma Erel_down n m Σ T e : m ≤ n → Erel n Σ T e → Erel m Σ T e.
Proof.
  revert n Σ T e. induction m as [|m' IH]; intros n Σ T e Hle HE;
    [apply Erel_0|].
  destruct n as [|n']; [lia|].
  apply Erel_S_iff in HE as [H1 H2]. apply Erel_S_iff. split.
  - intros He. eapply Vrel_down; [|by apply H1]. lia.
  - intros α e' Hst. specialize (H2 α e' Hst).
    destruct α as [|[c w|c w|c]|c w]; simpl in H2 |- *.
    + eapply IH; [|exact H2]. lia.
    + destruct H2 as (Σ1 & U & s & -> & Hc & H2).
      eexists _, _, _. split_and!; [done|done|].
      intros j Σ2 Hj Hd Hcd HV. apply H2; auto. lia.
    + destruct H2 as (Σ1 & Σ2 & U & s & -> & ? & ? & ? & HV & HE').
      eexists _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * eapply IH; [|exact HE']. lia.
    + destruct H2 as (Σ1 & -> & ? & HE').
      eexists. split_and!; eauto. eapply IH; [|done]. lia.
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
  apply Prel_S_iff in HP as [H1 H2]. apply Prel_S_iff. split.
  - intros Hirr. destruct (H1 Hirr) as (v & E & -> & ? & HV & ?).
    eexists _, _. split_and!; eauto. eapply Vrel_down; [|exact HV]. lia.
  - intros π p' Hst. specialize (H2 π p' Hst).
    destruct π as [|[c w|c w|c]]; simpl in H2 |- *.
    + intros Hd. eapply IH; [|by apply H2]. lia.
    + destruct H2 as (Σ1 & U & s & -> & Hc & H2).
      eexists _, _, _. split_and!; [done|done|].
      intros j Σ2 Hj Hd Hcd Hfr HV. apply H2; auto. lia.
    + destruct H2 as (Σ0 & Σv & U & s & σe & Σw & C0 & E0 & Cw & Ew &
                      T0 & Tw & -> & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      ? & ? & ? & HV & HP0 & HPw & ?).
      eexists _, _, _, _, _, _, _, _, _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * eapply IH; [|exact HP0]. lia.
      * eapply Powners_mono; [|exact HPw].
        intros ? ? ? ?. eapply IH; [|eauto]. lia.
    + destruct H2 as (Σ1 & -> & ? & HP').
      eexists. split_and!; eauto. eapply IH; [|done]. lia.
Qed.

(** ** Compositionality for terms (Theorem 3.11)

    One lemma per rule of Fig. 4, with ⊢ replaced by ⊨. The
    structural rules (unit, constants, variables, channels) are proved
    here; the binder/splitting rules are stated and admitted. *)

Lemma grounding_lenv_empty n Σ Δ γ :
  grounding n Σ Δ γ → lenv_empty Δ → Σ = ∅.
Proof.
  induction Δ as [|o Δ' IH] in Σ, γ |- *; simpl; intros Hg HΔ; [done|].
  destruct o as [T|].
  - assert (Some T = None) by (apply HΔ; constructor). done.
  - apply (IH _ (γ ∘ S)); [done|].
    intros o Ho. apply HΔ. rewrite elem_of_cons. auto.
Qed.

Lemma grounding_only n Σ Δ γ x T :
  grounding n Σ Δ γ → lenv_only Δ x T → Vrel n Σ T (γ x).
Proof.
  induction Δ as [|o Δ' IH] in Σ, γ, x |- *; intros Hg [Hlk Huniq]; [done|].
  destruct o as [T0|]; destruct x as [|x']; simpl in *; simplify_eq.
  - (* head available, x = 0 *)
    destruct Hg as (Σ1 & Σ2 & [-> Hdisj] & HV & Hg').
    assert (Σ2 = ∅) as ->.
    { eapply grounding_lenv_empty; [done|]. intros o Ho.
      destruct o as [T'|]; [exfalso|done].
      apply list_elem_of_lookup in Ho as [y Hy].
      by destruct (Huniq (S y) T'). }
    rewrite (right_id ∅ (∪)). exact HV.
  - (* head available, x = S x': contradicts uniqueness *)
    exfalso. by destruct (Huniq 0 T0).
  - (* head absent, x = S x' *)
    apply (IH _ (γ ∘ S) x'); [done|]. split; [done|].
    intros y T' Hy. destruct (Huniq (S y) T') as [Hxy ->]; [done|].
    split; [lia|done].
Qed.

(** Grounding substitutions are downward closed, split along splits of
    Δ, and assign channel-bounded values to available variables. *)
Lemma grounding_down m n Σ Δ γ :
  m ≤ n → grounding n Σ Δ γ → grounding m Σ Δ γ.
Proof.
  intros Hm. induction Δ as [|[T|] Δ' IH] in Σ, γ |- *; simpl; [done| |].
  - intros (Σ1 & Σ2 & Hsp & HV & Hg).
    exists Σ1, Σ2. eauto using Vrel_down.
  - apply IH.
Qed.

Lemma grounding_split n Σ Δ Δ1 Δ2 γ :
  lenv_split Δ Δ1 Δ2 → grounding n Σ Δ γ →
  ∃ Σ1 Σ2, senv_split Σ Σ1 Σ2 ∧ grounding n Σ1 Δ1 γ ∧ grounding n Σ2 Δ2 γ.
Proof.
  intros Hs. revert Σ γ. induction Hs; intros Σ γ Hg; simpl in *.
  - exists ∅, ∅. subst. split_and!; try done.
  - destruct (IHHs _ _ Hg) as (Σ1 & Σ2 & ? & ? & ?). eauto 6.
  - destruct Hg as (Σa & Σb & [-> Hd] & HV & Hg).
    destruct (IHHs _ _ Hg) as (Σ1 & Σ2 & [-> Hd2] & Hg1 & Hg2).
    exists (Σa ∪ Σ1), Σ2. split_and!; [| |done].
    + split; [by senv_perm|senv_disj].
    + exists Σa, Σ1. split_and!; try done. split; [done|senv_disj].
  - destruct Hg as (Σa & Σb & [-> Hd] & HV & Hg).
    destruct (IHHs _ _ Hg) as (Σ1 & Σ2 & [-> Hd2] & Hg1 & Hg2).
    exists Σ1, (Σa ∪ Σ2). split_and!; [|done|].
    + split; [by senv_perm|senv_disj].
    + exists Σa, Σ2. split_and!; try done. split; [done|senv_disj].
Qed.

Lemma grounding_fchans n Σ Δ γ x T :
  grounding n Σ Δ γ → Δ !! x = Some (Some T) → fchans (γ x) ⊆ dom Σ.
Proof.
  induction Δ as [|[T0|] Δ' IH] in Σ, γ, x |- *; intros Hg Hx;
    simpl in *; simplify_eq.
  - destruct x as [|x']; simpl in Hx; simplify_eq.
    + destruct Hg as (Σ1 & Σ2 & [-> _] & HV & _).
      pose proof (Vrel_fchans _ _ _ _ HV). senv_dom.
    + destruct Hg as (Σ1 & Σ2 & [-> _] & _ & Hg).
      specialize (IH _ _ _ Hg Hx). senv_dom.
  - destruct x as [|x']; simpl in Hx; simplify_eq.
    exact (IH _ _ _ Hg Hx).
Qed.

(** Conversely, every channel of a grounding's environment occurs in
    the value assigned to some available variable (tightness of V). *)
Lemma grounding_dom n Σ Δ γ ch :
  grounding n Σ Δ γ → ch ∈ dom Σ →
  ∃ x T, Δ !! x = Some (Some T) ∧ ch ∈ fchans (γ x).
Proof.
  induction Δ as [|[T0|] Δ' IH] in Σ, γ |- *; simpl; intros Hg Hch.
  - subst. rewrite dom_empty_L in Hch. set_solver.
  - destruct Hg as (Σ1 & Σ2 & [-> _] & HV & Hg).
    rewrite dom_union_L in Hch. apply elem_of_union in Hch as [Hch|Hch].
    + exists 0, T0. split; [done|].
      rewrite (Vrel_fchans _ _ _ _ HV). done.
    + destruct (IH _ _ Hg Hch) as (x & T & ? & ?). by exists (S x), T.
  - destruct (IH _ _ Hg Hch) as (x & T & ? & ?). by exists (S x), T.
Qed.

Lemma lenv_empty_no_avail Δ x : lenv_empty Δ → ¬ lenv_avail Δ x.
Proof.
  intros HΔ (T & Hx). apply list_elem_of_lookup_2 in Hx.
  apply HΔ in Hx. done.
Qed.

(** E-Unit *)
Lemma sem_typed_unit Δ : lenv_empty Δ → sem_typed ∅ Δ EUnit TUnit.
Proof.
  intros HΔ. split_and!; simpl.
  { by rewrite dom_empty_L. }
  { done. }
  { intros x Hx. exact (lenv_empty_no_avail _ _ HΔ Hx). }
  intros n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite lvl_eq. simpl. done.
Qed.

(** E-Const *)
Lemma sem_typed_konst Δ k T :
  lenv_empty Δ → konst_ty k T → sem_typed ∅ Δ (Konst k) T.
Proof.
  intros HΔ Hk. split_and!; simpl.
  { by rewrite dom_empty_L. }
  { done. }
  { intros x Hx. exact (lenv_empty_no_avail _ _ HΔ Hx). }
  intros n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite lvl_eq.
  destruct Hk; simpl; right; eexists; split_and!; eauto using konst_ty.
Qed.

(** E-LVar *)
Lemma sem_typed_var Δ x T : lenv_only Δ x T → sem_typed ∅ Δ (Var x) T.
Proof.
  intros Ho. split_and!; simpl.
  { by rewrite dom_empty_L. }
  { destruct Ho as [Hlk _]. by exists T. }
  { intros x' (T' & Hx'). destruct Ho as [_ Huniq].
    by destruct (Huniq x' T' Hx') as [-> _]. }
  intros n Σ' γ Hdisj Hg. simpl.
  rewrite (left_id ∅ (∪)).
  apply Vrel_Erel. eauto using grounding_only.
Qed.

(** E-Ch *)
Lemma sem_typed_chan Δ c s :
  lenv_empty Δ → sem_typed {[c := s]} Δ (Chan c) (TSess s).
Proof.
  intros HΔ. split_and!; simpl.
  { by rewrite dom_singleton_L. }
  { done. }
  { intros x Hx. exact (lenv_empty_no_avail _ _ HΔ Hx). }
  intros n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite lvl_eq. simpl.
  exists c. auto.
Qed.

(** ** Canonical values *)

Lemma Vrel_unit n : Vrel n ∅ TUnit EUnit.
Proof. by apply Vrel_unit_iff. Qed.

Lemma Vrel_chan n c s : Vrel n {[c := s]} (TSess s) (Chan c).
Proof. apply Vrel_sess_iff. eauto. Qed.

Lemma Vrel_pair n Σ1 Σ2 T U v1 v2 :
  Σ1 ##ₘ Σ2 → Vrel n Σ1 T v1 → Vrel n Σ2 U v2 →
  Vrel n (Σ1 ∪ Σ2) (TProd T U) (Pair v1 v2).
Proof.
  intros. apply Vrel_prod_iff. exists v1, v2, Σ1, Σ2.
  split_and!; auto. by split.
Qed.

(** ** Closure under evaluation frames

    [Erel_bind]: to run [fill_frame f e], run e — while e is not a
    value the composite's transitions are exactly e's, with the
    frame's environment Σf inert — and hand over to the continuation
    once e has become a value (at any index and any environment the
    hole may have evolved to). *)
Lemma Erel_bind n f Σh Σf Th T eh :
  frame_val f → Σh ##ₘ Σf →
  Erel n Σh Th eh →
  (∀ j Σh' v, j ≤ n → Σh' ##ₘ Σf → Vrel j Σh' Th v →
     Erel j (Σh' ∪ Σf) T (fill_frame f v)) →
  Erel n (Σh ∪ Σf) T (fill_frame f eh).
Proof.
  revert f Σh Σf Th T eh.
  induction n as [n IHn] using lt_wf_ind.
  intros f Σh Σf Th T eh Hf Hd HE HK.
  destruct (is_val eh) eqn:Hval.
  { assert (is_val eh) as Hv by (by rewrite Hval).
    destruct n as [|n']; [apply Erel_0|].
    apply HK; [lia|done|].
    apply Erel_S_iff in HE as [H1 _]. auto using val_irred. }
  assert (¬ is_val eh) as Hv by (rewrite Hval; intros []).
  destruct n as [|n']; [apply Erel_0|].
  apply Erel_S_iff. split.
  { intros Hirr. exfalso. apply Hv.
    assert (irred eh) as Hirr1.
    { intros α eh' Hst. eapply Hirr. by eapply tstep_fill. }
    apply Erel_S_iff in HE as [H1 _]. eauto using Vrel_val. }
  intros α E' Hst.
  apply tstep_fill_inv in Hst as (eh' & Hst & ->); [|done|done].
  pose proof (Erel_S_step _ _ _ _ _ _ HE Hst) as Hc.
  destruct α as [|[c w|c w|c]|c w]; simpl in Hc |- *.
  - (* β *)
    eapply (IHn n'); [lia|done|done|done|].
    intros j Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* recv *)
    destruct Hc as (Σh1 & U0 & s & -> & Hcd & Hc).
    apply map_disjoint_insert_l in Hd as [Hcf Hd].
    exists (Σh1 ∪ Σf), U0, s. split_and!.
    { by rewrite insert_union_l. }
    { apply not_elem_of_dom in Hcd. apply not_elem_of_dom.
      by rewrite lookup_union, Hcd, Hcf. }
    intros j Σn Hj Hdn Hcn HV.
    assert (Σn ##ₘ Σh1) by senv_disj.
    assert (Σn ##ₘ Σf) by senv_disj.
    specialize (Hc j Σn Hj ltac:(done) Hcn HV).
    replace (<[c:=s]> (Σh1 ∪ Σf ∪ Σn)) with (<[c:=s]> (Σh1 ∪ Σn) ∪ Σf)
      by senv_perm.
    eapply (IHn j); [lia|done|senv_disj|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* send *)
    destruct Hc as (Σh1 & Σh2 & U0 & s & -> & Hd12 & Hc1 & Hc2 & HV & HE').
    apply map_disjoint_insert_l in Hd as [Hcf Hd].
    assert (Σh1 ##ₘ Σf) by senv_disj.
    assert (Σh2 ##ₘ Σf) by senv_disj.
    exists (Σh1 ∪ Σf), Σh2, U0, s. split_and!.
    { senv_perm. }
    { senv_disj. }
    { apply not_elem_of_dom in Hc1. apply not_elem_of_dom.
      by rewrite lookup_union, Hc1, Hcf. }
    { done. }
    { done. }
    replace (<[c:=s]> (Σh1 ∪ Σf)) with (<[c:=s]> Σh1 ∪ Σf)
      by (by rewrite insert_union_l).
    eapply (IHn n'); [lia|done|senv_disj|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* close *)
    destruct Hc as (Σh1 & -> & Hcd & HE').
    apply map_disjoint_insert_l in Hd as [Hcf Hd].
    exists (Σh1 ∪ Σf). split_and!.
    { by rewrite insert_union_l. }
    { apply not_elem_of_dom in Hcd. apply not_elem_of_dom.
      by rewrite lookup_union, Hcd, Hcf. }
    eapply (IHn n'); [lia|done|done|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
  - (* fork *)
    intros Hcdom. rewrite dom_union_L in Hcdom.
    assert (c ∉ dom Σh) as Hch by set_solver.
    assert (c ∉ dom Σf) as Hcf by set_solver.
    destruct (Hc Hch) as (Σa & Σb & s & [-> Hdab] & HV & HE').
    exists Σa, (Σb ∪ Σf), s. split_and!.
    { split; [by rewrite (assoc_L (∪))|senv_disj]. }
    { done. }
    replace (<[c:=dual s]> (Σb ∪ Σf)) with (<[c:=dual s]> Σb ∪ Σf)
      by (by rewrite insert_union_l).
    eapply (IHn n'); [lia|done|senv_disj|done|].
    intros j' Σh' v ? ? ?. apply HK; [lia|done|done].
Qed.

(** ** Semantic head reductions *)

(** Applying a related function to a related argument. *)
Lemma Vrel_app_head n Σ1 Σ2 T U v1 v2 :
  Σ1 ##ₘ Σ2 →
  Vrel n Σ1 (TLolli T U) v1 → Vrel n Σ2 T v2 →
  Erel n (Σ1 ∪ Σ2) U (App v1 v2).
Proof.
  intros Hd HV1 HV2.
  pose proof (Vrel_val _ _ _ _ HV1) as Hv1.
  pose proof (Vrel_val _ _ _ _ HV2) as Hv2.
  destruct n as [|n']; [apply Erel_0|].
  apply Erel_S_iff. split.
  { (* an application of a related function is never stuck *)
    intros Hirr. exfalso.
    apply Vrel_lolli_iff in HV1
      as [(eb & -> & Hsup & HL)|(k & -> & -> & Hk)].
    { eapply (Hirr LBeta). apply TStepHead. by apply HeadApp. }
    inversion Hk; subst.
    - eapply (Hirr (LFork (fresh (∅ : gset chan)) v2)).
      apply TStepHead. by apply HeadFork.
    - apply Vrel_sess_iff in HV2 as (c & -> & ->).
      eapply (Hirr (LSess (SRecv c EUnit))). apply TStepHead.
      by apply HeadRecv.
    - apply Vrel_prod_iff in HV2
        as (w & vc & Σa & Σb & -> & Hsp & HVw & HVc).
      apply Vrel_sess_iff in HVc as (c & -> & ->).
      eapply (Hirr (LSess (SSend c w))). apply TStepHead.
      apply HeadSend. eauto using Vrel_val.
    - apply Vrel_sess_iff in HV2 as (c & -> & ->).
      eapply (Hirr (LSess (SClos c))). apply TStepHead. by apply HeadClos. }
  intros α e'' Hst.
  apply tstep_app_inv in Hst
    as [(e1' & Hst1 & ->)|[(_ & e2' & Hst2 & ->)|(_ & _ & Hhd)]].
  { exfalso. eauto using val_no_tstep. }
  { exfalso. eauto using val_no_tstep. }
  inversion Hhd; subst; simpl.
  - (* HeadApp *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & Hsup & HL)|(k & Heq & _)]; simplify_eq.
    apply HL; [lia|senv_disj|]. eapply Vrel_down; [|done]. lia.
  - (* HeadFork *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    intros Hcdom.
    match type of HV2 with Vrel _ _ (TLolli (TSess ?s) TUnit) _ =>
      exists Σ2, ∅, s end.
    refine (conj _ (conj HV2 _)).
    { split; [senv_perm|apply map_disjoint_empty_r]. }
    apply Vrel_Erel. rewrite insert_empty. apply Vrel_chan.
  - (* HeadRecv *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    apply Vrel_sess_iff in HV2 as (c' & Heqc & Heqs). simplify_eq.
    match goal with |- context [SRcv ?t ?s] => exists ∅, t, s end.
    refine (conj _ (conj _ _)).
    { senv_perm. }
    { set_solver. }
    intros j Σn Hj _ Hcn HVw.
    rewrite (left_id ∅ (∪)).
    rewrite insert_as_union; [|done].
    apply Vrel_Erel, Vrel_pair; [|done|apply Vrel_chan].
    by apply map_disjoint_singleton_r, not_elem_of_dom.
  - (* HeadSend *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    apply Vrel_prod_iff in HV2
      as (w' & vc & Σa & Σb & Heqp & [-> Hdab] & HVw & HVc).
    simplify_eq.
    apply Vrel_sess_iff in HVc as (c' & Heqc & ->). simplify_eq.
    assert (Σa !! c' = None) as Hca.
    { by apply map_disjoint_singleton_r in Hdab. }
    match goal with |- context [SSnd ?t ?s] => exists ∅, Σa, t, s end.
    refine (conj _ (conj _ (conj _ (conj _ (conj HVw _))))).
    { senv_perm. }
    { apply map_disjoint_empty_l. }
    { set_solver. }
    { by apply not_elem_of_dom. }
    apply Vrel_Erel. rewrite insert_empty. apply Vrel_chan.
  - (* HeadClos *)
    apply Vrel_lolli_iff in HV1
      as [(eb & Heq & _)|(k & Heq & -> & Hk)]; simplify_eq.
    inversion Hk; subst.
    apply Vrel_sess_iff in HV2 as (c' & Heqc & Heqs). simplify_eq.
    exists ∅. refine (conj _ (conj _ _)).
    { senv_perm. }
    { set_solver. }
    apply Vrel_Erel, Vrel_unit.
Qed.

(** Reducing a let-unit / let-pair redex. *)
Lemma Erel_letu_val n Σ T e2 : Erel n Σ T e2 → Erel n Σ T (LetU EUnit e2).
Proof.
  destruct n as [|n']; [intros; apply Erel_0|].
  intros HE. apply Erel_S_iff. split.
  { intros Hirr. exfalso. eapply (Hirr LBeta).
    apply TStepHead, HeadLetU. }
  intros α e' Hst.
  apply tstep_letu_inv in Hst as [(e1' & Hst1 & _)|(_ & -> & ->)].
  { exfalso. eapply val_no_tstep; [exact Hst1|done]. }
  simpl. eapply Erel_down; [|done]. lia.
Qed.

Lemma Erel_letp_val n Σ T u v f :
  is_val u → is_val v →
  (∀ j, j < n → Erel j Σ T (subst2 u v f)) →
  Erel n Σ T (LetP (Pair u v) f).
Proof.
  destruct n as [|n']; [intros; apply Erel_0|].
  intros Hu Hv HK. apply Erel_S_iff. split.
  { intros Hirr. exfalso. eapply (Hirr LBeta).
    apply TStepHead. by apply HeadLetP. }
  intros α e' Hst.
  apply tstep_letp_inv in Hst
    as [(e1' & Hst1 & _)|(u' & v' & Heq & _ & _ & -> & ->)].
  { exfalso. eapply val_no_tstep; [exact Hst1|]. simpl.
    by apply andb_True. }
  simplify_eq. simpl. apply HK. lia.
Qed.

(** E-Abs *)
Lemma sem_typed_lam Σ Δ e T U :
  sem_typed Σ (Some T :: Δ) e U →
  sem_typed Σ Δ (Lam e) (TLolli T U).
Proof.
  intros (Hfc & Hfv & Hrv & He). split_and!; simpl; [done| | |].
  { eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
    - intros _. done.
    - intros (T' & HT'). by exists T'. }
  { intros x (T' & Hx). apply (Hrv (S x)). by exists T'. }
  intros n Σ' γ Hdisj Hg. simpl.
  apply Vrel_Erel. apply Vrel_lolli_iff. left.
  exists (subst (up γ) e). split_and!; [done| |].
  { (* the substituted body owns exactly the channels of Σ ∪ Σ' *)
    apply (anti_symm (⊆)).
    - etrans; [apply (fchans_subst _ (up γ) (dom Σ'))|].
      + eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
        * intros _. set_solver.
        * intros (T' & HT'). unfold compose. rewrite fchans_rename.
          eapply grounding_fchans; eauto.
      + rewrite dom_union_L. set_solver.
    - rewrite dom_union_L. intros ch Hch.
      apply elem_of_union in Hch as [Hch|Hch].
      + rewrite <-Hfc in Hch. by apply fchans_subst_super.
      + destruct (grounding_dom _ _ _ _ _ Hg Hch) as (x & T' & Hx & Hcx).
        assert (freevar (S x) e) as Hfree by (apply Hrv; by exists T').
        pose proof (fchans_subst_free e (S x) (up γ) Hfree) as Hsub.
        simpl in Hsub. unfold compose in Hsub.
        rewrite fchans_rename in Hsub. set_solver. }
  intros j Σn w Hj Hdn HVw.
  rewrite subst1_subst.
  replace (Σ ∪ Σ' ∪ Σn) with (Σ ∪ (Σn ∪ Σ')) by senv_perm.
  apply He.
  - senv_disj.
  - simpl. exists Σn, Σ'. split_and!.
    + split; [done|senv_disj].
    + exact HVw.
    + eapply grounding_down; [|exact Hg]. lia.
Qed.

(** E-App *)
Lemma sem_typed_app Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 (TLolli T U) → sem_typed Σ2 Δ2 e2 T →
  sem_typed Σ Δ (App e1 e2) U.
Proof.
  intros [-> HdΣ] HΔ (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split.
    - eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv1. by exists T'.
    - right. apply Hrv2. by exists T'. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  apply (Erel_bind n (FAppL (subst γ e2)) _ _ (TLolli T U)); simpl.
  - done.
  - senv_disj.
  - apply He1; [senv_disj|done].
  - intros j Σh' v1 Hj Hdh HV1.
    replace (Σh' ∪ (Σ2 ∪ Σ'2)) with ((Σ2 ∪ Σ'2) ∪ Σh')
      by (apply map_union_comm; senv_disj).
    apply (Erel_bind j (FAppR v1) _ _ T); simpl.
    + eauto using Vrel_val.
    + senv_disj.
    + eapply Erel_down; [|apply He2; [senv_disj|done]]. lia.
    + intros j' Σf' v2 Hj' Hdf HV2.
      replace (Σf' ∪ Σh') with (Σh' ∪ Σf')
        by (apply map_union_comm; senv_disj).
      eapply Vrel_app_head; [senv_disj|..].
      * eapply Vrel_down; [|exact HV1]. lia.
      * exact HV2.
Qed.

(** E-Pair *)
Lemma sem_typed_pair Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 T → sem_typed Σ2 Δ2 e2 U →
  sem_typed Σ Δ (Pair e1 e2) (TProd T U).
Proof.
  intros [-> HdΣ] HΔ (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split.
    - eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv1. by exists T'.
    - right. apply Hrv2. by exists T'. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  apply (Erel_bind n (FPairL (subst γ e2)) _ _ T); simpl.
  - done.
  - senv_disj.
  - apply He1; [senv_disj|done].
  - intros j Σh' v1 Hj Hdh HV1.
    replace (Σh' ∪ (Σ2 ∪ Σ'2)) with ((Σ2 ∪ Σ'2) ∪ Σh')
      by (apply map_union_comm; senv_disj).
    apply (Erel_bind j (FPairR v1) _ _ U); simpl.
    + eauto using Vrel_val.
    + senv_disj.
    + eapply Erel_down; [|apply He2; [senv_disj|done]]. lia.
    + intros j' Σf' v2 Hj' Hdf HV2.
      replace (Σf' ∪ Σh') with (Σh' ∪ Σf')
        by (apply map_union_comm; senv_disj).
      apply Vrel_Erel, Vrel_pair; [senv_disj| |done].
      eapply Vrel_down; [|exact HV1]. lia.
Qed.

(** E-Let* *)
Lemma sem_typed_letu Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 TUnit → sem_typed Σ2 Δ2 e2 T →
  sem_typed Σ Δ (LetU e1 e2) T.
Proof.
  intros [-> HdΣ] HΔ (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split.
    - eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv2]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv1. by exists T'.
    - right. apply Hrv2. by exists T'. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  apply (Erel_bind n (FLetU (subst γ e2)) _ _ TUnit); simpl.
  - done.
  - senv_disj.
  - apply He1; [senv_disj|done].
  - intros j Σh' v1 Hj Hdh HV1.
    apply Vrel_unit_iff in HV1 as [-> ->].
    rewrite (left_id ∅ (∪)).
    apply Erel_letu_val.
    eapply Erel_down; [|apply He2; [senv_disj|done]]. lia.
Qed.

(** E-LetPair *)
Lemma sem_typed_letp Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 U V T :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 (TProd U V) →
  sem_typed Σ2 (Some V :: Some U :: Δ2) e2 T →
  sem_typed Σ Δ (LetP e1 e2) T.
Proof.
  intros [-> HdΣ] HΔ (Hfc1 & Hfv1 & Hrv1 & He1) (Hfc2 & Hfv2 & Hrv2 & He2).
  split_and!.
  { simpl. rewrite dom_union_L. set_solver. }
  { simpl. split.
    - eapply allfv_mono; [|exact Hfv1]. intros x (T' & ?).
      exists T'. eauto using lenv_split_lookup_l.
    - eapply allfv_mono; [|exact Hfv2]. intros [|[|x]]; simpl.
      + intros _. done.
      + intros _. done.
      + intros (T' & ?). exists T'. eauto using lenv_split_lookup_r. }
  { intros x (T' & Hx). simpl.
    destruct (lenv_split_lookup_inv _ _ _ _ _ HΔ Hx) as [Hx1|Hx2].
    - left. apply Hrv1. by exists T'.
    - right. apply (Hrv2 (S (S x))). by exists T'. }
  intros n Σ' γ Hdisj Hg. simpl.
  destruct (grounding_split _ _ _ _ _ _ HΔ Hg)
    as (Σ'1 & Σ'2 & [-> Hd'] & Hg1 & Hg2).
  replace (Σ1 ∪ Σ2 ∪ (Σ'1 ∪ Σ'2)) with ((Σ1 ∪ Σ'1) ∪ (Σ2 ∪ Σ'2))
    by senv_perm.
  apply (Erel_bind n (FLetP (subst (up (up γ)) e2)) _ _ (TProd U V));
    simpl.
  - done.
  - senv_disj.
  - apply He1; [senv_disj|done].
  - intros j Σh' w Hj Hdh HVw.
    apply Vrel_prod_iff in HVw
      as (u & v & Σa & Σb & -> & [-> Hdab] & HVu & HVv).
    apply Erel_letp_val; eauto using Vrel_val.
    intros j' Hj'.
    rewrite subst2_subst.
    replace (Σa ∪ Σb ∪ (Σ2 ∪ Σ'2)) with (Σ2 ∪ (Σb ∪ (Σa ∪ Σ'2)))
      by senv_perm.
    apply He2.
    { senv_disj. }
    simpl. exists Σb, (Σa ∪ Σ'2). split_and!.
    { split; [done|senv_disj]. }
    { eapply Vrel_down; [|exact HVv]. lia. }
    exists Σa, Σ'2. split_and!.
    { split; [done|senv_disj]. }
    { eapply Vrel_down; [|exact HVu]. lia. }
    eapply grounding_down; [|exact Hg2]. lia.
Qed.

(** ** The fundamental property for terms (Theorem 3.13, term half;
    the process half lives in Compositionality.v) *)

Theorem fundamental_term Σ Δ e T : typed Σ Δ e T → sem_typed Σ Δ e T.
Proof.
  induction 1.
  - by apply sem_typed_unit.
  - by apply sem_typed_konst.
  - by apply sem_typed_var.
  - by apply sem_typed_chan.
  - by apply sem_typed_lam.
  - by eapply sem_typed_app.
  - by eapply sem_typed_pair.
  - by eapply sem_typed_letu.
  - by eapply sem_typed_letp.
Qed.
