(** * Session substitution after session renaming

    sinst σ (sren r s) = sinst (σ ∘ r) s, for types and session types
    together. A µ body that mentions a free session variable a carries
    sren S a once a substitution goes under the µ ([sty_up]), and the
    unrolling substitutes the µ for variable 0 of the body. The fusion
    turns that substituend back into a ([unroll_up]), so the unrolling
    of an instantiated µ is the instantiated unrolling. *)

From stdpp Require Import base strings gmap.
From LRGV Require Export types.Types.

Set Default Proof Using "All".

Lemma sty_up_upren σ r : ∀ a, sty_up σ (upren r a) = sty_up (σ ∘ r) a.
Proof. intros [|a]; done. Qed.

Lemma iter_sty_up_upren k σ r :
  ∀ a, Nat.iter k sty_up σ (Nat.iter k upren r a) = Nat.iter k sty_up (σ ∘ r) a.
Proof.
  revert σ r. induction k as [|k IH]; intros σ r a; [done|]. rewrite !Nat.iter_succ.
  rewrite sty_up_upren. apply sty_up_ext. intros b. unfold compose. apply IH.
Qed.

Lemma sinst_sren_mut :
  (∀ T σ r, sinst_ty σ (sren_ty r T) = sinst_ty (σ ∘ r) T) ∧
  (∀ s σ r, sinst σ (sren r s) = sinst (σ ∘ r) s).
Proof.
  apply ty_sty_mut_ind; intros; cbn; f_equal; auto.
  - rewrite H. apply sinst_ext_mut. intros a. unfold compose. apply iter_sty_up_upren.
  - rewrite H. apply sinst_ext. intros a. unfold compose. apply sty_up_upren.
Qed.

Lemma sinst_sren σ r s : sinst σ (sren r s) = sinst (σ ∘ r) s.
Proof. apply sinst_sren_mut. Qed.

Lemma sinst_ty_sren σ r T : sinst_ty σ (sren_ty r T) = sinst_ty (σ ∘ r) T.
Proof. apply sinst_sren_mut. Qed.

(** Substituting for variable 0 after a shift leaves a type alone. *)
Lemma sinst_cons_sren_S u s : sinst (u .: SVar) (sren S s) = s.
Proof. rewrite sinst_sren. by apply sinst_id_mut. Qed.

(** The case of the loop: a µ whose body mentions the shifted outer
    variable unrolls to the body with that variable back in place. *)
Lemma unroll_up b s : sinst (SMu b .: SVar) (sren S s) = s.
Proof. apply sinst_cons_sren_S. Qed.
