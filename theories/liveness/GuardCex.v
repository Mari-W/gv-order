(** * A guarded box that τ-diverges (sharp edges 161)

    Force is call by name: forcing a box runs its body. When the body
    is not a λ, the special case of [ok] for (force x) e lets the body
    force its own self before any channel step, and the unrolled body
    does the same again.

      bad  = !(x. let ∗ = (force x) g in λy. y)      g guarded
      main = (force bad) ∗

    [main] is [guarded] ([cx_guarded]) and its thread has an infinite
    β sequence ([cx_tau_diverges]). The static typing of [main] (with a
    box at one point variable ζ as its upper point, g closing a fresh
    channel below ζ) is not mechanized yet. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.Guard liveness.LiveKob examples.ExampleTools.

Local Set Warnings "-register-all".

Definition cx_C : bcs := BCs [] (λ _, False).
Definition cx_fty : ty := TLolli None None TUnit TUnit.
Definition cx_bty : ty := TBox 1 0 cx_C (TLolli (Some (pvar 0)) None TUnit cx_fty).

(** A guarded unit term: a fresh channel, one end closed by a spawned
    thread, the other by the caller. *)
Definition cx_g : expr :=
  let_new_pair (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1))))) (App EClos (Var 1))).

Definition cx_body : expr := LetU (App (App EForce (Var 0)) cx_g) (Lam (Var 0)).
Definition cx_bad : expr := EBox cx_body.
Definition cx_main : expr := App (App EForce cx_bad) EUnit.

Theorem cx_guarded : guarded cx_main.
Proof. vm_compute. reflexivity. Qed.

(** ** The unrolling never ends *)

(** [cx_main] sits in evaluation position. *)
Inductive cx_pos : expr → Prop :=
  | cxp_here : cx_pos (App EForce cx_bad)
  | cxp_appl e1 e2 : cx_pos e1 → cx_pos (App e1 e2)
  | cxp_letu e1 e2 : cx_pos e1 → cx_pos (LetU e1 e2).

Lemma cx_unroll :
  tstep (App EForce cx_bad) LBeta (LetU (App (App EForce cx_bad) cx_g) (Lam (Var 0))).
Proof.
  apply TStepHead.
  replace (LetU (App (App EForce cx_bad) cx_g) (Lam (Var 0))) with (subst1 cx_bad cx_body)
    by reflexivity.
  apply HeadForce.
Qed.

Lemma cx_pos_step e : cx_pos e → ∃ e', tstep e LBeta e' ∧ cx_pos e'.
Proof.
  induction 1 as [|e1 e2 _ (e1' & Hs & Hp)|e1 e2 _ (e1' & Hs & Hp)].
  - eexists. split; [exact cx_unroll|]. do 3 constructor.
  - exists (App e1' e2). split; [by apply TStepAppL|by constructor].
  - exists (LetU e1' e2). split; [by apply TStepLetU|by constructor].
Qed.

Lemma cx_not_acc q : Acc (λ y x, padmin x y) q →
  ∀ C E e, cx_pos e → q = (C, E ⊎ {[+ e +]}) → False.
Proof.
  induction 1 as [q _ IH]. intros C E e Hp ->.
  destruct (cx_pos_step e Hp) as (e' & Hs & Hp').
  apply (IH (C, E ⊎ {[+ e' +]}) ltac:(by constructor) C E e' Hp' eq_refl).
Qed.

Theorem cx_tau_diverges : ¬ no_tau_divergence (∅, {[+ cx_main +]}).
Proof.
  intros Hnd. apply (cx_not_acc (∅, {[+ cx_main +]}) (Hnd _ (rtc_refl _ _)) ∅ ∅ cx_main);
    [do 2 constructor|]. by rewrite (left_id_L ∅ (⊎)).
Qed.
