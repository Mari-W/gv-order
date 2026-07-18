(** * Types, session types, duality, environments (§2.2, Fig. 5 top)

    T, U ::= ∗ | T ⊸ U | T ⊗ U | S
    S    ::= ?T.S | !T.S | Close *)

From stdpp Require Import base strings gmap.
From LRGV Require Export Syntax.

Inductive ty :=
  | TUnit                          (* ∗ *)
  | TLolli (T U : ty)              (* T ⊸ U *)
  | TProd (T U : ty)               (* T ⊗ U *)
  | TSess (S : sty)
with sty :=
  | SRcv (T : ty) (S : sty)        (* ?T.S *)
  | SSnd (T : ty) (S : sty)        (* !T.S *)
  | SEnd.                          (* Close *)

Scheme ty_mut_ind := Induction for ty Sort Prop
  with sty_mut_ind := Induction for sty Sort Prop.
Combined Scheme ty_sty_mut_ind from ty_mut_ind, sty_mut_ind.

(** ** Session duality: swaps the direction of communication. *)

Fixpoint dual (s : sty) : sty :=
  match s with
  | SRcv T s' => SSnd T (dual s')
  | SSnd T s' => SRcv T (dual s')
  | SEnd => SEnd
  end.

Lemma dual_involutive s : dual (dual s) = s.
Proof. induction s; simpl; congruence. Qed.

(** ** Primitive types: possible return types of threads. *)

Inductive prim : ty → Prop :=
  | prim_unit : prim TUnit
  | prim_prod U V : prim U → prim V → prim (TProd U V).

(** ** Session environments: finite maps from channels to session types.

    Splitting Σ = Σ1, Σ2 is disjoint union of the underlying maps. *)

Definition senv := gmap chan sty.

Definition senv_split (Σ Σ1 Σ2 : senv) : Prop :=
  Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2.

Lemma senv_split_empty_l Σ : senv_split Σ ∅ Σ.
Proof.
  split; [by rewrite (left_id ∅ (∪))|]. apply map_disjoint_empty_l.
Qed.

Lemma senv_split_comm Σ Σ1 Σ2 : senv_split Σ Σ1 Σ2 → senv_split Σ Σ2 Σ1.
Proof.
  intros [-> Hd]. split; [by apply map_union_comm|done].
Qed.

(** ** Type-indexed families of type signatures for constants (Fig. 4)

    fork : (S ⊸ ∗) ⊸ dual S     send : (T ⊗ !T.S) ⊸ S
    recv : ?T.S ⊸ T ⊗ S         clos : Close ⊸ ∗ *)

Inductive konst_ty : konst → ty → Prop :=
  | KTFork S :
      konst_ty KFork (TLolli (TLolli (TSess S) TUnit) (TSess (dual S)))
  | KTRecv T S :
      konst_ty KRecv (TLolli (TSess (SRcv T S)) (TProd T (TSess S)))
  | KTSend T S :
      konst_ty KSend (TLolli (TProd T (TSess (SSnd T S))) (TSess S))
  | KTClos :
      konst_ty KClos (TLolli (TSess SEnd) TUnit).
