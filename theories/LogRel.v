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
    (the ∀ j < n quantification in the ⊸ case). *)
Fixpoint Vdef (below : nat → level) (n : nat)
    (Σ : senv) (T : ty) (v : expr) {struct T} : Prop :=
  match T with
  | TUnit => Σ = ∅ ∧ v = EUnit
  | TSess s => ∃ c, v = Chan c ∧ Σ = {[c := s]}
  | TLolli T1 U =>
      (∃ eb, v = Lam eb ∧
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
              ∀ j Σ2, j < n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 →
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

(** Process relation at level n. The output case (case 3, the
    ⌈updated⌉ one in Fig. 5) sends value w to the environment: the
    restricted channels occurring in w (dom Σs = fchans w ∩ C) escape,
    typed by some session types Σs; the residual process splits into
    two independent parts, one connected to c, one to the escaped
    channels, with return types {T1,T2} = {T,∗}. *)
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
            lP (below n') Σ T p'
        | PSess (SRecv c w) =>                         (* case 2 *)
            ∃ Σ1 U s,
              Σ = <[c := SRcv U s]> Σ1 ∧ c ∉ dom Σ1 ∧
              ∀ j Σ2, j < n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 →
                lV (below j) Σ2 U w →
                lP (below j) (<[c := s]> (Σ1 ∪ Σ2)) T p'
        | PSess (SSend c w) =>                         (* case 3 *)
            ∃ Σ1 Σ2 Σ3 U s (Σs : senv) C1' C2' E1' E2' T1 T2,
              Σ = <[c := SSnd U s]> (Σ1 ∪ Σ2 ∪ Σ3) ∧
              Σ1 ##ₘ Σ2 ∧ Σ1 ##ₘ Σ3 ∧ Σ2 ##ₘ Σ3 ∧
              c ∉ dom Σ1 ∧ c ∉ dom Σ2 ∧ c ∉ dom Σ3 ∧
              dom Σs = fchans w ∩ p.1 ∧
              Σs ##ₘ Σ2 ∧ Σs ##ₘ Σ3 ∧ c ∉ dom Σs ∧
              p'.1 = C1' ∪ C2' ∧ C1' ## C2' ∧
              p'.2 = E1' ⊎ E2' ∧
              Vn (Σ3 ∪ (dual <$> Σs)) U w ∧
              lP (below n') (<[c := s]> Σ1) T1 (C1', E1') ∧
              lP (below n') (Σ2 ∪ Σs) T2 (C2', E2') ∧
              ((T1 = T ∧ T2 = TUnit) ∨ (T1 = TUnit ∧ T2 = T))
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
  - by intros [(eb & -> & _)|(k & -> & _)].
  - intros (v1 & v2 & Σ1 & Σ2 & -> & _ & H1 & H2).
    simpl. apply andb_True. eauto.
  - by intros (c & -> & _).
Qed.

Lemma Vrel_val n Σ T v : Vrel n Σ T v → is_val v.
Proof. unfold Vrel. rewrite lvl_eq. apply Vdef_val. Qed.

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

(** τ steps decrease the index by one. *)
Lemma Prel_S_tau n Σ T p p' :
  Prel (S n) Σ T p → preduction p p' → Prel n Σ T p'.
Proof.
  unfold Prel at 1. rewrite lvl_eq. simpl.
  intros [_ Hstep] Hred. specialize (Hstep _ _ Hred). simpl in Hstep.
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

(** Σ; Δ ⊨ e : T.  The channels of e itself are covered by Σ; the
    grounding substitution brings its own (disjoint) Σ'. (Def. 3.3;
    the draft's phrasing conflates the two environments — this is the
    reading under which the rules of Fig. 4, e.g. E-Ch, are
    non-vacuous.) *)
Definition sem_typed (Σ : senv) (Δ : lenv) (e : expr) (T : ty) : Prop :=
  ∀ n Σ' γ, Σ' ##ₘ Σ → grounding n Σ' Δ γ →
    Erel n (Σ ∪ Σ') T (subst γ e).

(** Σ ⊨ p : T *)
Definition sem_ptyped (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ n, Prel n Σ T p.

(** ** The adequacy chain (Lemmas 3.4, 3.5 and Theorem 3.6) *)

(** Lemma 3.4 *)
Lemma Prel_steps m n Σ T p p' :
  nsteps preduction m p p' → Prel (m + n) Σ T p → Prel n Σ T p'.
Proof.
  induction 1 as [|m' x y z Hxy Hyz IH]; simpl; [done|].
  intros HP. apply IH. by eapply Prel_S_tau.
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
  intros HP p' Hsteps. apply rtc_nsteps in Hsteps as [m Hm].
  eapply (Prel_safe 0). eapply Prel_steps; [exact Hm|]. exact (HP (m + 1)).
Qed.

(** ** Downward closure (Lemma 3.7) *)

Lemma Vrel_down n m Σ T v : m ≤ n → Vrel n Σ T v → Vrel m Σ T v.
Proof. Admitted.

Lemma Erel_down n m Σ T e : m ≤ n → Erel n Σ T e → Erel m Σ T e.
Proof. Admitted.

Lemma Prel_down n m Σ T p : m ≤ n → Prel n Σ T p → Prel m Σ T p.
Proof. Admitted.

(** ** Compositionality for processes (Lemmas 3.8–3.10) *)

(** Lemma 3.8 (Compositionality: TERM) *)
Lemma Prel_term n Σ T e :
  prim T → Erel n Σ T e → Prel n Σ T (∅, {[+ e +]}).
Proof. Admitted.

(** Lemma 3.9 (Compositionality: INDEPENDENT) *)
Lemma Prel_independent n Σ Σ1 Σ2 C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  Prel n Σ1 T (C1, E1) → Prel n Σ2 TUnit (C2, E2) →
  Prel n Σ T (C1 ∪ C2, E1 ⊎ E2).
Proof. Admitted.

(** Lemma 3.10 (Compositionality: CONNECT) *)
Lemma Prel_connect n Σ Σ1 Σ2 c s C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  Prel n (<[c := s]> Σ1) T (C1, E1) →
  Prel n (<[c := dual s]> Σ2) TUnit (C2, E2) →
  Prel n Σ T (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2).
Proof. Admitted.

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
      apply elem_of_list_lookup in Ho as [y Hy].
      by destruct (Huniq (S y) T'). }
    rewrite (right_id ∅ (∪)). exact HV.
  - (* head available, x = S x': contradicts uniqueness *)
    exfalso. by destruct (Huniq 0 T0).
  - (* head absent, x = S x' *)
    apply (IH _ (γ ∘ S) x'); [done|]. split; [done|].
    intros y T' Hy. destruct (Huniq (S y) T') as [Hxy ->]; [done|].
    split; [lia|done].
Qed.

(** E-Unit *)
Lemma sem_typed_unit Δ : lenv_empty Δ → sem_typed ∅ Δ EUnit TUnit.
Proof.
  intros HΔ n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite lvl_eq. simpl. done.
Qed.

(** E-Const *)
Lemma sem_typed_konst Δ k T :
  lenv_empty Δ → konst_ty k T → sem_typed ∅ Δ (Konst k) T.
Proof.
  intros HΔ Hk n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite lvl_eq.
  destruct Hk; simpl; right; eexists; split_and!; eauto using konst_ty.
Qed.

(** E-LVar *)
Lemma sem_typed_var Δ x T : lenv_only Δ x T → sem_typed ∅ Δ (Var x) T.
Proof.
  intros Ho n Σ' γ Hdisj Hg. simpl.
  rewrite (left_id ∅ (∪)).
  apply Vrel_Erel. eauto using grounding_only.
Qed.

(** E-Ch *)
Lemma sem_typed_chan Δ c s :
  lenv_empty Δ → sem_typed {[c := s]} Δ (Chan c) (TSess s).
Proof.
  intros HΔ n Σ' γ Hdisj Hg.
  assert (Σ' = ∅) as -> by eauto using grounding_lenv_empty.
  rewrite (right_id ∅ (∪)). simpl.
  apply Vrel_Erel. unfold Vrel. rewrite lvl_eq. simpl.
  exists c. auto.
Qed.

(** E-Abs *)
Lemma sem_typed_lam Σ Δ e T U :
  sem_typed Σ (Some T :: Δ) e U →
  sem_typed Σ Δ (Lam e) (TLolli T U).
Proof. Admitted.

(** E-App *)
Lemma sem_typed_app Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 (TLolli T U) → sem_typed Σ2 Δ2 e2 T →
  sem_typed Σ Δ (App e1 e2) U.
Proof. Admitted.

(** E-Pair *)
Lemma sem_typed_pair Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 T → sem_typed Σ2 Δ2 e2 U →
  sem_typed Σ Δ (Pair e1 e2) (TProd T U).
Proof. Admitted.

(** E-Let* *)
Lemma sem_typed_letu Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 TUnit → sem_typed Σ2 Δ2 e2 T →
  sem_typed Σ Δ (LetU e1 e2) T.
Proof. Admitted.

(** E-LetPair *)
Lemma sem_typed_letp Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 U V T :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 (TProd U V) →
  sem_typed Σ2 (Some V :: Some U :: Δ2) e2 T →
  sem_typed Σ Δ (LetP e1 e2) T.
Proof. Admitted.

(** ** Compositionality for processes, judgment form (Theorem 3.12) *)

(** P-Term *)
Lemma sem_ptyped_term Σ e T :
  prim T → sem_typed Σ [] e T → sem_ptyped Σ (∅, {[+ e +]}) T.
Proof.
  intros Hp He n. apply Prel_term; [done|].
  specialize (He n ∅ Var (map_disjoint_empty_l _) eq_refl).
  by rewrite (right_id ∅ (∪)), subst_ids in He.
Qed.

(** P-Independent *)
Lemma sem_ptyped_independent Σ Σ1 Σ2 C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  sem_ptyped Σ1 (C1, E1) T → sem_ptyped Σ2 (C2, E2) TUnit →
  sem_ptyped Σ (C1 ∪ C2, E1 ⊎ E2) T.
Proof. intros. intro n. by eapply Prel_independent. Qed.

(** P-Connect *)
Lemma sem_ptyped_connect Σ Σ1 Σ2 c s C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  sem_ptyped (<[c := s]> Σ1) (C1, E1) T →
  sem_ptyped (<[c := dual s]> Σ2) (C2, E2) TUnit →
  sem_ptyped Σ (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) T.
Proof. intros. intro n. by eapply Prel_connect. Qed.

(** ** The fundamental property (Theorem 3.13) *)

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

Theorem fundamental_proc Σ p T : ptyped Σ p T → sem_ptyped Σ p T.
Proof.
  induction 1.
  - apply sem_ptyped_term; auto using fundamental_term.
  - eapply sem_ptyped_independent; eauto using ptyped_prim.
  - eapply sem_ptyped_connect; eauto using ptyped_prim.
Qed.

(** Corollary: syntactically typed closed processes are deadlock free. *)
Corollary typed_deadlock_free p T : ptyped ∅ p T → deadlock_free p.
Proof. eauto using adequacy, fundamental_proc. Qed.
