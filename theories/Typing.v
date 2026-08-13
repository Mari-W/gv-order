(** * Syntactic session typing for GV♯ (Fig. 4)

    Term judgments Σ; Δ ⊢ e : T and process judgments Σ ⊢ (C,E) : T.

    The linear variable environment Δ is a "resource vector": a list
    over all in-scope de Bruijn indices, where [Some T] marks an
    available linear binding and [None] an absent/spent one (cf. the
    paper's §5 on the Agda mechanization). Splitting Δ = Δ1, Δ2 sends
    every available binding to exactly one side. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Export Semantics Types.

Definition lenv := list (option ty).

(** No available bindings. *)
Definition lenv_empty (Δ : lenv) : Prop := ∀ o, o ∈ Δ → o = None.

(** Exactly one available binding, x : T. *)
Definition lenv_only (Δ : lenv) (x : nat) (T : ty) : Prop :=
  Δ !! x = Some (Some T) ∧
  ∀ y T', Δ !! y = Some (Some T') → y = x ∧ T' = T.

Inductive lenv_split : lenv → lenv → lenv → Prop :=
  | lsplit_nil :
      lenv_split [] [] []
  | lsplit_none Δ Δ1 Δ2 :
      lenv_split Δ Δ1 Δ2 →
      lenv_split (None :: Δ) (None :: Δ1) (None :: Δ2)
  | lsplit_l T Δ Δ1 Δ2 :
      lenv_split Δ Δ1 Δ2 →
      lenv_split (Some T :: Δ) (Some T :: Δ1) (None :: Δ2)
  | lsplit_r T Δ Δ1 Δ2 :
      lenv_split Δ Δ1 Δ2 →
      lenv_split (Some T :: Δ) (None :: Δ1) (Some T :: Δ2)
  | lsplit_unl U Δ Δ1 Δ2 :                 (* contraction at unlimited types *)
      unlimited U →
      lenv_split Δ Δ1 Δ2 →
      lenv_split (Some U :: Δ) (Some U :: Δ1) (Some U :: Δ2).

Lemma lenv_split_lookup_l Δ Δ1 Δ2 x T :
  lenv_split Δ Δ1 Δ2 → Δ1 !! x = Some (Some T) → Δ !! x = Some (Some T).
Proof.
  intros Hs. revert x. induction Hs; intros [|x] Hx; simpl in *;
    simplify_eq; auto.
Qed.

Lemma lenv_split_comm Δ Δ1 Δ2 :
  lenv_split Δ Δ1 Δ2 → lenv_split Δ Δ2 Δ1.
Proof. induction 1; constructor; auto. Qed.

Lemma lenv_split_lookup_inv Δ Δ1 Δ2 x T :
  lenv_split Δ Δ1 Δ2 → Δ !! x = Some (Some T) →
  Δ1 !! x = Some (Some T) ∨ Δ2 !! x = Some (Some T).
Proof.
  intros Hs. revert x. induction Hs; intros [|x] Hx; simpl in *;
    simplify_eq; auto.
Qed.

Lemma lenv_split_lookup_r Δ Δ1 Δ2 x T :
  lenv_split Δ Δ1 Δ2 → Δ2 !! x = Some (Some T) → Δ !! x = Some (Some T).
Proof. eauto using lenv_split_lookup_l, lenv_split_comm. Qed.

(** Splitting is pointwise, so it commutes with concatenation. *)

Lemma lenv_split_app Δ1 Δa1 Δb1 Δ2 Δa2 Δb2 :
  lenv_split Δ1 Δa1 Δb1 → lenv_split Δ2 Δa2 Δb2 →
  lenv_split (Δ1 ++ Δ2) (Δa1 ++ Δa2) (Δb1 ++ Δb2).
Proof. induction 1; simpl; eauto using lenv_split. Qed.

Lemma lenv_split_app_inv Δ1 Δ2 Δa Δb :
  lenv_split (Δ1 ++ Δ2) Δa Δb →
  ∃ Δa1 Δa2 Δb1 Δb2,
    Δa = Δa1 ++ Δa2 ∧ Δb = Δb1 ++ Δb2 ∧
    length Δa1 = length Δ1 ∧ length Δb1 = length Δ1 ∧
    lenv_split Δ1 Δa1 Δb1 ∧ lenv_split Δ2 Δa2 Δb2.
Proof.
  revert Δa Δb. induction Δ1 as [|a Δ1 IH]; intros Δa Δb Hs; simpl in *.
  - exists [], Δa, [], Δb. split_and!; eauto using lenv_split.
  - inversion Hs as [| ??? Hs' | ???? Hs' | ???? Hs' | ????? Hs']; simplify_eq;
      apply IH in Hs' as (Δa1 & Δa2 & Δb1 & Δb2 & -> & -> & ? & ? & ? & ?);
      eexists (_ :: Δa1), Δa2, (_ :: Δb1), Δb2; simpl;
      split_and!; eauto using lenv_split.
Qed.

(** ** Weakening: erasing unlimited entries from the context.

    [lenv_wk Δ' Δ] : Δ' is Δ with some unlimited entries dropped (to
    None); the weakening rule below moves a judgment from Δ' to Δ. *)

Inductive lenv_wk : lenv → lenv → Prop :=
  | lwk_nil : lenv_wk [] []
  | lwk_cons o Δ' Δ :
      lenv_wk Δ' Δ → lenv_wk (o :: Δ') (o :: Δ)
  | lwk_drop U Δ' Δ :
      unlimited U →
      lenv_wk Δ' Δ → lenv_wk (None :: Δ') (Some U :: Δ).

Lemma lenv_wk_refl Δ : lenv_wk Δ Δ.
Proof. induction Δ; by constructor. Qed.

(** Weakening is pointwise too. *)

Lemma lenv_wk_app Δ1' Δ1 Δ2' Δ2 :
  lenv_wk Δ1' Δ1 → lenv_wk Δ2' Δ2 → lenv_wk (Δ1' ++ Δ2') (Δ1 ++ Δ2).
Proof. induction 1; simpl; eauto using lenv_wk. Qed.

Lemma lenv_wk_app_inv Δ' Δ1 Δ2 :
  lenv_wk Δ' (Δ1 ++ Δ2) →
  ∃ Δ1' Δ2', Δ' = Δ1' ++ Δ2' ∧ length Δ1' = length Δ1 ∧
             lenv_wk Δ1' Δ1 ∧ lenv_wk Δ2' Δ2.
Proof.
  revert Δ'. induction Δ1 as [|a Δ1 IH]; intros Δ' Hw; simpl in *.
  - exists [], Δ'. eauto using lenv_wk.
  - inversion Hw as [| ??? Hw' | ???? Hw']; simplify_eq;
      apply IH in Hw' as (Δ1' & Δ2' & -> & ? & ? & ?);
      eexists (_ :: Δ1'), Δ2'; simpl; split_and!; eauto using lenv_wk.
Qed.

(** All available entries are unlimited (the □Γ side condition). *)
Definition lenv_unl (Δ : lenv) : Prop :=
  ∀ o, o ∈ Δ → o = None ∨ ∃ U, o = Some U ∧ unlimited U.

(** ** Typing rules for terms: Σ; Δ ⊢ e : T *)

Inductive typed : senv → lenv → expr → ty → Prop :=
  | typed_unit Δ :                                     (* E-Unit *)
      lenv_empty Δ →
      typed ∅ Δ EUnit TUnit
  | typed_konst Δ k T :                                (* E-Const *)
      lenv_empty Δ → konst_ty k T →
      typed ∅ Δ (Konst k) T
  | typed_var Δ x T :                                  (* E-LVar *)
      lenv_only Δ x T →
      typed ∅ Δ (Var x) T
  | typed_chan Δ c s :                                 (* E-Ch *)
      lenv_empty Δ →
      typed {[c := s]} Δ (Chan c) (TSess s)
  | typed_lam Σ Δ e T U :                              (* E-Abs *)
      typed Σ (Some T :: Δ) e U →
      typed Σ Δ (Lam e) (TLolli T U)
  | typed_app Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :             (* E-App *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e1 (TLolli T U) → typed Σ2 Δ2 e2 T →
      typed Σ Δ (App e1 e2) U
  | typed_pair Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :            (* E-Pair *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e1 T → typed Σ2 Δ2 e2 U →
      typed Σ Δ (Pair e1 e2) (TProd T U)
  | typed_letu Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T :              (* E-Let* *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e1 TUnit → typed Σ2 Δ2 e2 T →
      typed Σ Δ (LetU e1 e2) T
  | typed_letp Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 U V T :          (* E-LetPair *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e1 (TProd U V) →
      (* let ⟨a,b⟩ = e1 in e2: in e2, index 1 = a : U, index 0 = b : V *)
      typed Σ2 (Some V :: Some U :: Δ2) e2 T →
      typed Σ Δ (LetP e1 e2) T
  | typed_inj1 Σ Δ e T U :                             (* E-Inl *)
      typed Σ Δ e T →
      typed Σ Δ (Inj1 e) (TSum T U)
  | typed_inj2 Σ Δ e T U :                             (* E-Inr *)
      typed Σ Δ e U →
      typed Σ Δ (Inj2 e) (TSum T U)
  | typed_case Σ Σ1 Σ2 Δ Δ1 Δ2 e e1 e2 U V T :        (* E-Case *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e (TSum U V) →
      (* each branch binds its payload at index 0 *)
      typed Σ2 (Some U :: Δ2) e1 T →
      typed Σ2 (Some V :: Δ2) e2 T →
      typed Σ Δ (Case e e1 e2) T
  | typed_box Δ e T :                                 (* E-Box *)
      (* a replicable thunk owns no channels and captures only
         unlimited variables; index 0 of the body is the thunk itself,
         at □T — which is unlimited, so the recursive occurrence
         inherits contraction and weakening with no extra bookkeeping *)
      lenv_unl Δ →
      typed ∅ (Some (TBox T) :: Δ) e T →
      typed ∅ Δ (EBox e) (TBox T)
  | typed_wk Σ Δ' Δ e T :                              (* □-weakening *)
      typed Σ Δ' e T →
      lenv_wk Δ' Δ →
      typed Σ Δ e T
  | typed_conv Σ Δ e s s' :                            (* E-Conv: µα.S = S[µα.S/α] *)
      (* equi-recursive conversion at session type, up to unfolding;
         for the head-normal cases the premise is [reflexivity] *)
      unfoldS s = unfoldS s' →
      typed Σ Δ e (TSess s) →
      typed Σ Δ e (TSess s').

(** All-None environments, for typing a konst under an arbitrary Δ. *)
Definition lenv_nones (Δ : lenv) : lenv := (λ _, None) <$> Δ.

Lemma lenv_empty_nones Δ : lenv_empty (lenv_nones Δ).
Proof. intros o (?&->&?)%list_elem_of_fmap. done. Qed.

Lemma lenv_split_nones_l Δ : lenv_split Δ (lenv_nones Δ) Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; unfold lenv_nones; simpl; constructor; auto.
Qed.

(** Derived rule E-Force: force is a konst, so forcing is ordinary
    application ([KTForce]). *)
Lemma typed_force Σ Δ e T :
  typed Σ Δ e (TBox T) → typed Σ Δ (App EForce e) T.
Proof.
  intros H.
  eapply (typed_app _ ∅ Σ _ (lenv_nones Δ) Δ);
    [apply senv_split_empty_l|apply lenv_split_nones_l| |exact H].
  apply typed_konst; [apply lenv_empty_nones|]. apply KTForce.
Qed.

(** ** Derived rule E-Contract

    Two adjacent copies of an unlimited binding may be merged into one.
    The paper's rule instantiates W := □T ([unlimited_box]); the
    semantic counterpart is [Terms.sem_typed_contract].

    Binders push the contracted pair rightward, so the induction runs
    over a contraction at an arbitrary position [length Δ1], with the
    two merged entries tracked by [ocontr]. *)

(** The two contracted entries are each absent or the unlimited [W];
    the entry they merge into is their join. *)
Inductive ocontr (W : ty) : option ty → option ty → option ty → Prop :=
  | ocontr_nn : ocontr W None None None
  | ocontr_sn : ocontr W (Some W) None (Some W)
  | ocontr_ns : ocontr W None (Some W) (Some W)
  | ocontr_ss : ocontr W (Some W) (Some W) (Some W).

(** The index map merging [n] and [n+1]; [cren 0] is [pred]. *)
Definition cren (n x : nat) : nat := if decide (x ≤ n) then x else pred x.

Lemma cren_0 n : cren n 0 = 0.
Proof. unfold cren. case_decide; [done|lia]. Qed.

Lemma cren_S n x : cren (S n) (S x) = S (cren n x).
Proof. unfold cren. repeat case_decide; simpl; lia. Qed.

Lemma cren_pred x : cren 0 x = pred x.
Proof. unfold cren. case_decide; [lia|done]. Qed.

(** Going under a binder shifts the contracted position. *)

Lemma upren_cren n x : upren (cren n) x = cren (S n) x.
Proof. destruct x; simpl; [by rewrite cren_0|by rewrite cren_S]. Qed.

Lemma upren_upren_cren n x : upren (upren (cren n)) x = cren (S (S n)) x.
Proof. by rewrite (upren_ext _ _ (upren_cren n)), upren_cren. Qed.

(** *** Transporting the environment predicates across a contraction. *)

Lemma elem_of_contr W Δ1 o1 o2 o Δ2 x :
  ocontr W o1 o2 o → x ∈ Δ1 ++ o :: Δ2 →
  x = None ∨ x ∈ Δ1 ++ o1 :: o2 :: Δ2.
Proof.
  intros Hc. rewrite !elem_of_app, !elem_of_cons.
  intros [?|[->|?]]; [naive_solver|destruct Hc; naive_solver|naive_solver].
Qed.

Lemma lenv_empty_contr W Δ1 o1 o2 o Δ2 :
  ocontr W o1 o2 o →
  lenv_empty (Δ1 ++ o1 :: o2 :: Δ2) → lenv_empty (Δ1 ++ o :: Δ2).
Proof. intros Hc H x [->|?]%(elem_of_contr _ _ _ _ _ _ _ Hc); auto. Qed.

Lemma lenv_unl_contr W Δ1 o1 o2 o Δ2 :
  ocontr W o1 o2 o →
  lenv_unl (Δ1 ++ o1 :: o2 :: Δ2) → lenv_unl (Δ1 ++ o :: Δ2).
Proof. intros Hc H x [->|?]%(elem_of_contr _ _ _ _ _ _ _ Hc); auto. Qed.

Lemma lookup_contr_fwd W Δ1 o1 o2 o Δ2 x T :
  ocontr W o1 o2 o →
  (Δ1 ++ o1 :: o2 :: Δ2) !! x = Some (Some T) →
  (Δ1 ++ o :: Δ2) !! cren (length Δ1) x = Some (Some T).
Proof.
  intros Hc. revert x. induction Δ1 as [|a Δ1 IH]; intros x Hx; simpl in *.
  - destruct x as [|[|x]]; rewrite cren_pred; simpl in *;
      [inversion Hc|inversion Hc|]; simplify_eq/=; done.
  - destruct x as [|x]; [by rewrite cren_0|]. rewrite cren_S. by apply IH.
Qed.

Lemma lookup_contr_bwd W Δ1 o1 o2 o Δ2 y T :
  ocontr W o1 o2 o →
  (Δ1 ++ o :: Δ2) !! y = Some (Some T) →
  ∃ x, (Δ1 ++ o1 :: o2 :: Δ2) !! x = Some (Some T) ∧ cren (length Δ1) x = y.
Proof.
  intros Hc. revert y. induction Δ1 as [|a Δ1 IH]; intros y Hy; simpl in *.
  - destruct y as [|y]; simpl in *.
    + inversion Hc; simplify_eq/=;
        [exists 0|exists 1|exists 0]; by rewrite cren_pred.
    + exists (S (S y)). by rewrite cren_pred.
  - destruct y as [|y]; simpl in *.
    + exists 0. by rewrite cren_0.
    + apply IH in Hy as (x & ? & <-). exists (S x). by rewrite cren_S.
Qed.

Lemma lenv_only_contr W Δ1 o1 o2 o Δ2 x T :
  ocontr W o1 o2 o →
  lenv_only (Δ1 ++ o1 :: o2 :: Δ2) x T →
  lenv_only (Δ1 ++ o :: Δ2) (cren (length Δ1) x) T.
Proof.
  intros Hc [Hx Hu]. split; [by eapply lookup_contr_fwd|].
  intros y T' Hy.
  apply (lookup_contr_bwd _ _ _ _ _ _ _ _ Hc) in Hy as (z & Hz & <-).
  by destruct (Hu _ _ Hz) as [-> ->].
Qed.

(** *** The contracted pair under a split and under a weakening.

    Each side of a split sees a pair of entries that is again
    contractible, and the two joins split the joined entry — the case
    where both sides keep the entry is exactly [lsplit_unl], which is
    where [unlimited W] is needed (as it is for [lwk_drop] below). *)

Lemma lenv_split_contr2 W o1 o2 o Δ Δa Δb :
  unlimited W → ocontr W o1 o2 o →
  lenv_split (o1 :: o2 :: Δ) Δa Δb →
  ∃ oa1 oa2 Δa' ob1 ob2 Δb' oa ob,
    Δa = oa1 :: oa2 :: Δa' ∧ Δb = ob1 :: ob2 :: Δb' ∧
    ocontr W oa1 oa2 oa ∧ ocontr W ob1 ob2 ob ∧
    lenv_split (o :: Δ) (oa :: Δa') (ob :: Δb').
Proof.
  intros HW Hc Hs.
  inversion Hc; simplify_eq; inversion Hs; clear Hs; simplify_eq;
    match goal with H : lenv_split (_ :: _) _ _ |- _ => inversion H; clear H end;
    simplify_eq; do 8 eexists; split_and!; eauto using ocontr, lenv_split.
Qed.

Lemma lenv_wk_contr2 W o1 o2 o Δ' Δ :
  unlimited W → ocontr W o1 o2 o →
  lenv_wk Δ' (o1 :: o2 :: Δ) →
  ∃ q1 q2 Δ'' q,
    Δ' = q1 :: q2 :: Δ'' ∧ ocontr W q1 q2 q ∧ lenv_wk (q :: Δ'') (o :: Δ).
Proof.
  intros HW Hc Hw.
  inversion Hc; simplify_eq; inversion Hw; clear Hw; simplify_eq;
    match goal with H : lenv_wk _ (_ :: _) |- _ => inversion H; clear H end;
    simplify_eq; do 4 eexists; split_and!; eauto using ocontr, lenv_wk.
Qed.

(** *** Contraction at an arbitrary position *)

(** Decompose a split of the environment along the contracted pair. *)
Local Ltac contr_split H HW Hc :=
  apply lenv_split_app_inv in H
    as (Δa1 & Δa2 & Δb1 & Δb2 & -> & -> & Hla & Hlb & Hsa & H);
  apply (lenv_split_contr2 _ _ _ _ _ _ _ HW Hc) in H
    as (qa1 & qa2 & Δa2' & qb1 & qb2 & Δb2' & qa & qb &
        -> & -> & Hca & Hcb & Hsb).

Lemma typed_contract_gen Σ Δ1 Δ2 o1 o2 o W U e :
  unlimited W → ocontr W o1 o2 o →
  typed Σ (Δ1 ++ o1 :: o2 :: Δ2) e U →
  typed Σ (Δ1 ++ o :: Δ2) (rename (cren (length Δ1)) e) U.
Proof.
  intros HW Hc Ht.
  remember (Δ1 ++ o1 :: o2 :: Δ2) as Δ eqn:HΔ.
  revert Δ1 Δ2 o1 o2 o Hc HΔ.
  induction Ht; intros Ξ Δr p1 p2 p Hc ->; simpl.
  - (* E-Unit *) apply typed_unit. by eapply lenv_empty_contr.
  - (* E-Const *) apply typed_konst; [by eapply lenv_empty_contr|done].
  - (* E-LVar *) apply typed_var. by eapply lenv_only_contr.
  - (* E-Ch *) apply typed_chan. by eapply lenv_empty_contr.
  - (* E-Abs *)
    apply typed_lam. rewrite (rename_ext _ _ _ (upren_cren (length Ξ))).
    by apply (IHHt (Some T :: Ξ) Δr p1 p2 p Hc).
  - (* E-App *)
    contr_split H0 HW Hc.
    eapply typed_app; [done|by apply lenv_split_app| |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2' qa1 qa2 qa Hca).
    + rewrite <-Hlb. by apply (IHHt2 Δb1 Δb2' qb1 qb2 qb Hcb).
  - (* E-Pair *)
    contr_split H0 HW Hc.
    eapply typed_pair; [done|by apply lenv_split_app| |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2' qa1 qa2 qa Hca).
    + rewrite <-Hlb. by apply (IHHt2 Δb1 Δb2' qb1 qb2 qb Hcb).
  - (* E-Let* *)
    contr_split H0 HW Hc.
    eapply typed_letu; [done|by apply lenv_split_app| |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2' qa1 qa2 qa Hca).
    + rewrite <-Hlb. by apply (IHHt2 Δb1 Δb2' qb1 qb2 qb Hcb).
  - (* E-LetPair *)
    contr_split H0 HW Hc.
    eapply typed_letp; [done|by apply lenv_split_app| |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2' qa1 qa2 qa Hca).
    + rewrite (rename_ext _ _ _ (upren_upren_cren (length Ξ))), <-Hlb.
      by apply (IHHt2 (Some V :: Some U :: Δb1) Δb2' qb1 qb2 qb Hcb).
  - (* E-Inl *) apply typed_inj1. by apply (IHHt Ξ Δr p1 p2 p Hc).
  - (* E-Inr *) apply typed_inj2. by apply (IHHt Ξ Δr p1 p2 p Hc).
  - (* E-Case *)
    contr_split H0 HW Hc.
    eapply typed_case; [done|by apply lenv_split_app| | |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2' qa1 qa2 qa Hca).
    + rewrite (rename_ext _ _ _ (upren_cren (length Ξ))), <-Hlb.
      by apply (IHHt2 (Some U :: Δb1) Δb2' qb1 qb2 qb Hcb).
    + rewrite (rename_ext _ _ _ (upren_cren (length Ξ))), <-Hlb.
      by apply (IHHt3 (Some V :: Δb1) Δb2' qb1 qb2 qb Hcb).
  - (* E-Box *)
    apply typed_box; [by eapply lenv_unl_contr|].
    rewrite (rename_ext _ _ _ (upren_cren (length Ξ))).
    by apply (IHHt (Some (TBox T) :: Ξ) Δr p1 p2 p Hc).
  - (* □-weakening *)
    apply lenv_wk_app_inv in H as (Ξ' & Δs & -> & Hl & Hw1 & Hw2).
    apply (lenv_wk_contr2 _ _ _ _ _ _ HW Hc) in Hw2
      as (q1 & q2 & Δs' & q & -> & Hcq & Hw2).
    eapply typed_wk; [|by apply lenv_wk_app].
    rewrite <-Hl. by apply (IHHt Ξ' Δs' q1 q2 q Hcq).
  - (* E-Conv *)
    eapply typed_conv; [done|]. by apply (IHHt Ξ Δr p1 p2 p Hc).
Qed.

(** Derived rule E-Contract. *)
Lemma typed_contract Σ Δ W U e :
  unlimited W →
  typed Σ (Some W :: Some W :: Δ) e U →
  typed Σ (Some W :: Δ) (rename pred e) U.
Proof.
  intros HW Ht.
  rewrite (rename_ext e pred (cren 0)); [|by intros x; rewrite cren_pred].
  by apply (typed_contract_gen Σ [] Δ (Some W) (Some W) (Some W) W);
    [|constructor|].
Qed.

(** ** Derived rule E-Weaken

    A judgment survives adding a fresh unlimited binding to the
    environment. Unlike [typed_wk], which un-spends entries in place
    and leaves the term alone, this inserts a NEW entry, so all indices
    of the term shift past it.

    The insertion is first done at [None] — where no side condition is
    needed at all — and the entry is then filled in with [Some W] by
    [typed_wk]; [unlimited W] is consumed only there, by [lwk_drop].
    Binders push the inserted entry rightward, so the induction runs
    over an insertion at an arbitrary position [length Δ1]. *)

(** The index map inserting a fresh entry at position [n]; [wren 0] is [S]. *)
Definition wren (n x : nat) : nat := if decide (x < n) then x else S x.

Lemma wren_0 x : wren 0 x = S x.
Proof. unfold wren. case_decide; [lia|done]. Qed.

Lemma wren_S_0 n : wren (S n) 0 = 0.
Proof. unfold wren. case_decide; [done|lia]. Qed.

Lemma wren_S n x : wren (S n) (S x) = S (wren n x).
Proof. unfold wren. repeat case_decide; simpl; lia. Qed.

(** Going under a binder shifts the inserted position. *)

Lemma upren_wren n x : upren (wren n) x = wren (S n) x.
Proof. destruct x; simpl; [by rewrite wren_S_0|by rewrite wren_S]. Qed.

Lemma upren_upren_wren n x : upren (upren (wren n)) x = wren (S (S n)) x.
Proof. by rewrite (upren_ext _ _ (upren_wren n)), upren_wren. Qed.

(** *** Transporting the environment predicates across the insertion. *)

Lemma elem_of_thin (Δ1 Δ2 : lenv) o :
  o ∈ Δ1 ++ None :: Δ2 → o = None ∨ o ∈ Δ1 ++ Δ2.
Proof. rewrite !elem_of_app, elem_of_cons. naive_solver. Qed.

Lemma lenv_empty_thin Δ1 Δ2 :
  lenv_empty (Δ1 ++ Δ2) → lenv_empty (Δ1 ++ None :: Δ2).
Proof. intros H x [->|?]%elem_of_thin; auto. Qed.

Lemma lenv_unl_thin Δ1 Δ2 :
  lenv_unl (Δ1 ++ Δ2) → lenv_unl (Δ1 ++ None :: Δ2).
Proof. intros H x [->|?]%elem_of_thin; auto. Qed.

Lemma lookup_thin_fwd (Δ1 Δ2 : lenv) x T :
  (Δ1 ++ Δ2) !! x = Some (Some T) →
  (Δ1 ++ None :: Δ2) !! wren (length Δ1) x = Some (Some T).
Proof.
  revert x. induction Δ1 as [|a Δ1 IH]; intros x Hx; simpl in *.
  - done.
  - destruct x as [|x]; [by rewrite wren_S_0|]. rewrite wren_S. by apply IH.
Qed.

Lemma lookup_thin_bwd (Δ1 Δ2 : lenv) y T :
  (Δ1 ++ None :: Δ2) !! y = Some (Some T) →
  ∃ x, (Δ1 ++ Δ2) !! x = Some (Some T) ∧ wren (length Δ1) x = y.
Proof.
  revert y. induction Δ1 as [|a Δ1 IH]; intros y Hy; simpl in *.
  - destruct y as [|y]; simplify_eq/=. exists y. by rewrite wren_0.
  - destruct y as [|y]; simpl in *.
    + exists 0. by rewrite wren_S_0.
    + apply IH in Hy as (x & ? & <-). exists (S x). by rewrite wren_S.
Qed.

Lemma lenv_only_thin Δ1 Δ2 x T :
  lenv_only (Δ1 ++ Δ2) x T →
  lenv_only (Δ1 ++ None :: Δ2) (wren (length Δ1) x) T.
Proof.
  intros [Hx Hu]. split; [by apply lookup_thin_fwd|].
  intros y T' (z & Hz & <-)%lookup_thin_bwd.
  by destruct (Hu _ _ Hz) as [-> ->].
Qed.

(** *** Insertion of a [None] entry at an arbitrary position *)

(** Decompose a split of the environment along the insertion point. *)
Local Ltac thin_split H :=
  apply lenv_split_app_inv in H
    as (Δa1 & Δa2 & Δb1 & Δb2 & -> & -> & Hla & Hlb & Hsa & Hsb).

Lemma typed_thin Σ Δ1 Δ2 U e :
  typed Σ (Δ1 ++ Δ2) e U →
  typed Σ (Δ1 ++ None :: Δ2) (rename (wren (length Δ1)) e) U.
Proof.
  intros Ht. remember (Δ1 ++ Δ2) as Δ eqn:HΔ. revert Δ1 Δ2 HΔ.
  induction Ht; intros Ξ Δr ->; simpl.
  - (* E-Unit *) apply typed_unit. by apply lenv_empty_thin.
  - (* E-Const *) apply typed_konst; [by apply lenv_empty_thin|done].
  - (* E-LVar *) apply typed_var. by apply lenv_only_thin.
  - (* E-Ch *) apply typed_chan. by apply lenv_empty_thin.
  - (* E-Abs *)
    apply typed_lam. rewrite (rename_ext _ _ _ (upren_wren (length Ξ))).
    by apply (IHHt (Some T :: Ξ) Δr).
  - (* E-App *)
    thin_split H0.
    eapply typed_app; [done|by apply lenv_split_app, lsplit_none| |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2).
    + rewrite <-Hlb. by apply (IHHt2 Δb1 Δb2).
  - (* E-Pair *)
    thin_split H0.
    eapply typed_pair; [done|by apply lenv_split_app, lsplit_none| |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2).
    + rewrite <-Hlb. by apply (IHHt2 Δb1 Δb2).
  - (* E-Let* *)
    thin_split H0.
    eapply typed_letu; [done|by apply lenv_split_app, lsplit_none| |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2).
    + rewrite <-Hlb. by apply (IHHt2 Δb1 Δb2).
  - (* E-LetPair *)
    thin_split H0.
    eapply typed_letp; [done|by apply lenv_split_app, lsplit_none| |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2).
    + rewrite (rename_ext _ _ _ (upren_upren_wren (length Ξ))), <-Hlb.
      by apply (IHHt2 (Some V :: Some U :: Δb1) Δb2).
  - (* E-Inl *) apply typed_inj1. by apply (IHHt Ξ Δr).
  - (* E-Inr *) apply typed_inj2. by apply (IHHt Ξ Δr).
  - (* E-Case *)
    thin_split H0.
    eapply typed_case; [done|by apply lenv_split_app, lsplit_none| | |].
    + rewrite <-Hla. by apply (IHHt1 Δa1 Δa2).
    + rewrite (rename_ext _ _ _ (upren_wren (length Ξ))), <-Hlb.
      by apply (IHHt2 (Some U :: Δb1) Δb2).
    + rewrite (rename_ext _ _ _ (upren_wren (length Ξ))), <-Hlb.
      by apply (IHHt3 (Some V :: Δb1) Δb2).
  - (* E-Box *)
    apply typed_box; [by apply lenv_unl_thin|].
    rewrite (rename_ext _ _ _ (upren_wren (length Ξ))).
    by apply (IHHt (Some (TBox T) :: Ξ) Δr).
  - (* □-weakening *)
    apply lenv_wk_app_inv in H as (Ξ' & Δs & -> & Hl & Hw1 & Hw2).
    eapply typed_wk; [|apply lenv_wk_app; [exact Hw1|by constructor]].
    rewrite <-Hl. by apply (IHHt Ξ' Δs).
  - (* E-Conv *)
    eapply typed_conv; [done|]. by apply (IHHt Ξ Δr).
Qed.

(** Derived rule E-Weaken, at an arbitrary position. *)
Lemma typed_weaken_gen Σ Δ1 Δ2 W U e :
  unlimited W →
  typed Σ (Δ1 ++ Δ2) e U →
  typed Σ (Δ1 ++ Some W :: Δ2) (rename (wren (length Δ1)) e) U.
Proof.
  intros HW Ht. eapply typed_wk; [by apply typed_thin|].
  apply lenv_wk_app; [apply lenv_wk_refl|].
  apply lwk_drop; [done|apply lenv_wk_refl].
Qed.

(** Derived rule E-Weaken. *)
Lemma typed_weaken Σ Δ W U e :
  unlimited W →
  typed Σ Δ e U →
  typed Σ (Some W :: Δ) (rename S e) U.
Proof.
  intros HW Ht.
  rewrite <-(rename_ext e (wren 0) S); [|apply wren_0].
  by apply (typed_weaken_gen Σ [] Δ).
Qed.

(** ** Typing rules for processes: Σ ⊢ (C, E) : T

    As in the paper, Σ and C are implicitly assumed not to share
    channels; here this is enforced by freshness side conditions in
    P-Connect and disjointness in P-Independent. *)

Inductive ptyped : senv → proc → ty → Prop :=
  | ptyped_term Σ e T :                                (* P-Term *)
      prim T →
      typed Σ [] e T →
      ptyped Σ (∅, {[+ e +]}) T
  | ptyped_independent Σ Σ1 Σ2 C1 E1 C2 E2 T :        (* P-Independent *)
      senv_split Σ Σ1 Σ2 →
      C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
      ptyped Σ1 (C1, E1) T →
      ptyped Σ2 (C2, E2) TUnit →
      ptyped Σ (C1 ∪ C2, E1 ⊎ E2) T
  | ptyped_connect Σ Σ1 Σ2 c s C1 E1 C2 E2 T :        (* P-Connect *)
      senv_split Σ Σ1 Σ2 →
      c ∉ dom Σ1 → c ∉ dom Σ2 →
      C1 ## C2 → c ∉ C1 → c ∉ C2 →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      ptyped (<[c := s]> Σ1) (C1, E1) T →
      ptyped (<[c := dual s]> Σ2) (C2, E2) TUnit →
      ptyped Σ (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) T.

(** The return type of a typed process is always primitive (P-Term
    enforces it and the composition rules preserve it). *)
Lemma ptyped_prim Σ p T : ptyped Σ p T → prim T.
Proof. induction 1; auto. Qed.

(** A typed process's restricted channels never overlap its session
    environment (the paper's implicit well-formedness of Σ ⊢ (C,E)). *)
Lemma ptyped_chan_disj Σ p T : ptyped Σ p T → p.1 ## dom Σ.
Proof.
  induction 1; simpl in *;
    repeat match goal with
    | H : senv_split _ _ _ |- _ => destruct H as [-> _]
    | H : _ ## dom (<[_ := _]> _) |- _ => rewrite dom_insert_L in H
    end;
    rewrite ?dom_union_L; set_solver.
Qed.
