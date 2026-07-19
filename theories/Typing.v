(** * Syntactic session typing for GV♯ (Fig. 4)

    Term judgments Σ; Δ ⊢ e : T and process judgments Σ ⊢ (C,E) : T.

    The linear variable environment Δ is a "resource vector": a list
    over all in-scope de Bruijn indices, where [Some T] marks an
    available linear binding and [None] an absent/spent one (cf. the
    paper's §5 on the Agda mechanization). Splitting Δ = Δ1, Δ2 sends
    every available binding to exactly one side. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Export Processes Types.

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
      lenv_split (Some T :: Δ) (None :: Δ1) (Some T :: Δ2).

Lemma lenv_split_lookup_l Δ Δ1 Δ2 x T :
  lenv_split Δ Δ1 Δ2 → Δ1 !! x = Some (Some T) → Δ !! x = Some (Some T).
Proof.
  intros Hs. revert x. induction Hs; intros [|x] Hx; simpl in *;
    simplify_eq; auto.
Qed.

Lemma lenv_split_comm Δ Δ1 Δ2 :
  lenv_split Δ Δ1 Δ2 → lenv_split Δ Δ2 Δ1.
Proof. induction 1; constructor; auto. Qed.

Lemma lenv_split_lookup_r Δ Δ1 Δ2 x T :
  lenv_split Δ Δ1 Δ2 → Δ2 !! x = Some (Some T) → Δ !! x = Some (Some T).
Proof. eauto using lenv_split_lookup_l, lenv_split_comm. Qed.

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
      typed Σ Δ (LetP e1 e2) T.

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
