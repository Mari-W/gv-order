(** * Linear variable environments

    The linear variable environment Δ is a "resource vector": a list
    over all in-scope de Bruijn indices, where [Some T] marks an
    available linear binding and [None] an absent/spent one (cf. the
    paper's §5 on the Agda mechanization). Splitting Δ = Δ1, Δ2 sends
    every available binding to exactly one side. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Export types.Types.

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

(** Weakening is pointwise too. *)

(** All available entries are unlimited (the □Γ side condition). *)
Definition lenv_unl (Δ : lenv) : Prop :=
  ∀ o, o ∈ Δ → o = None ∨ ∃ U, o = Some U ∧ unlimited U.
