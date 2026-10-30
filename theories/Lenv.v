(** * Linear variable environments

    The linear variable environment Δ is a "resource vector": a list
    over all in-scope de Bruijn indices, where [Some T] marks an
    available linear binding and [None] an absent/spent one (cf. the
    paper's §5 on the Agda mechanization). Splitting Δ = Δ1, Δ2 sends
    every available binding to exactly one side. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Export Types.

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
