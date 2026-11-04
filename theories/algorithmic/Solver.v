(** * The checker over an abstract constraint solver

    [synth] is a total function. It returns a type T and a constraint c,
    and [synth_sound] asks only that c holds under the hypotheses Ψ.
    Type checking an annotated term is therefore one question to a
    theory, csat Ψ c. This file makes the theory a parameter.

    A [solver] answers csat Ψ c with a boolean and is sound. A solver is
    complete on a fragment P when it answers true for every satisfied
    constraint in P. Every decision procedure for csat ([Decision]
    instance, possibly restricted to P) is a complete solver
    ([solver_of_dec], [solver_of_dec_on]).

    [check_sound] and [check_deadlock_free] hold for every solver.
    [check_reflect] makes the algorithmic judgment [alg] decidable on P
    for a solver complete on P. Nothing here fixes a fragment. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export algorithmic.Soundness.

Set Default Proof Using "All".

(** ** Solvers *)

Record solver := Solver {
  solve : hyps → constr → bool;
  solve_sound : ∀ Ψ c, solve Ψ c = true → csat Ψ c
}.

(** S answers true for every satisfied constraint of P. *)
Definition complete_on (S : solver) (P : hyps → constr → Prop) : Prop :=
  ∀ Ψ c, P Ψ c → csat Ψ c → solve S Ψ c = true.

Lemma solve_reflect S P Ψ c :
  complete_on S P → P Ψ c → solve S Ψ c = true ↔ csat Ψ c.
Proof. intros HS HP. split; [apply solve_sound|by apply HS]. Qed.

(** A decision procedure for csat is a solver, complete everywhere. *)
Definition solver_of_dec (D : ∀ Ψ c, Decision (csat Ψ c)) : solver :=
  Solver (λ Ψ c, bool_decide (csat Ψ c)) (λ Ψ c H, bool_decide_eq_true_1 _ H).

Lemma solver_of_dec_complete D : complete_on (solver_of_dec D) (λ _ _, True).
Proof. intros Ψ c _ H. by apply bool_decide_eq_true_2. Qed.

(** A decision procedure on a decidable fragment P is a solver, complete
    on P. Outside P it answers false. *)
Definition solver_of_dec_on (P : hyps → constr → Prop)
    (DP : ∀ Ψ c, Decision (P Ψ c)) (D : ∀ Ψ c, P Ψ c → Decision (csat Ψ c)) : solver.
Proof.
  refine (Solver (λ Ψ c, match DP Ψ c with
                         | left HP => @bool_decide _ (D Ψ c HP)
                         | right _ => false
                         end) _).
  intros Ψ c. destruct (DP Ψ c) as [HP|]; [|discriminate].
  apply (@bool_decide_eq_true_1 _ (D Ψ c HP)).
Defined.

Lemma solver_of_dec_on_complete P DP D : complete_on (solver_of_dec_on P DP D) P.
Proof.
  intros Ψ c HP H. simpl. destruct (DP Ψ c) as [HP'|]; [|done].
  by apply (@bool_decide_eq_true_2 _ (D Ψ c HP')).
Qed.

(** The solver that never answers true. *)
Definition solver_none : solver := Solver (λ _ _, false) (λ _ _ H, False_rect _ (diff_false_true H)).

(** Try S1, then S2. Complete on the union of their fragments. *)
Definition solver_or (S1 S2 : solver) : solver.
Proof.
  refine (Solver (λ Ψ c, solve S1 Ψ c || solve S2 Ψ c) _).
  intros Ψ c H. apply orb_true_iff in H as [H|H]; by eapply solve_sound.
Defined.

Lemma solver_or_complete S1 S2 P1 P2 :
  complete_on S1 P1 → complete_on S2 P2 →
  complete_on (solver_or S1 S2) (λ Ψ c, P1 Ψ c ∨ P2 Ψ c).
Proof.
  intros H1 H2 Ψ c [HP|HP] Hc; simpl; apply orb_true_iff; [left; by apply H1|right; by apply H2].
Qed.

(** ** The checker *)

(** The algorithmic judgment: synth succeeds with T and its constraint
    holds under Ψ. *)
Definition alg (Ψ : hyps) (n : nat) (Φ : fhyps) (Δ : lenv) (F : sfuture) (a : aexpr) (T : ty) : Prop :=
  ∃ c, synth n Φ Δ F a = Some (T, c) ∧ csat Ψ c.

Definition infer (S : solver) (Ψ : hyps) (n : nat) (Φ : fhyps) (Δ : lenv) (F : sfuture) (a : aexpr)
    : option ty :=
  match synth n Φ Δ F a with
  | Some (T, c) => if solve S Ψ c then Some T else None
  | None => None
  end.

Lemma infer_alg S Ψ n Φ Δ F a T : infer S Ψ n Φ Δ F a = Some T → alg Ψ n Φ Δ F a T.
Proof.
  unfold infer, alg. destruct (synth n Φ Δ F a) as [[T' c]|]; [|discriminate].
  destruct (solve S Ψ c) eqn:Hs; [|discriminate]. injection 1 as <-.
  exists c. split; [done|]. by eapply solve_sound.
Qed.

Theorem check_sound S Ψ n Φ Δ F a T :
  fv_below n Φ → infer S Ψ n Φ Δ F a = Some T → styped Φ Ψ Δ F (erase a) T.
Proof.
  intros Hn H. apply infer_alg in H as (c & Hs & Hc). by eapply synth_sound.
Qed.

(** On the fragment of S, [infer] decides [alg]: it finds the type
    exactly when the term has one. The type is unique, because [synth]
    is a function. *)
Theorem check_reflect S P Ψ n Φ Δ F a :
  complete_on S P →
  (∀ T c, synth n Φ Δ F a = Some (T, c) → P Ψ c) →
  ∀ T, infer S Ψ n Φ Δ F a = Some T ↔ alg Ψ n Φ Δ F a T.
Proof.
  intros HS HP T. split; [apply infer_alg|].
  intros (c & Hs & Hc). unfold infer. rewrite Hs.
  rewrite (proj2 (solve_reflect S P Ψ c HS (HP _ _ Hs)) Hc). done.
Qed.

Corollary alg_dec S P Ψ n Φ Δ F a :
  complete_on S P →
  (∀ T c, synth n Φ Δ F a = Some (T, c) → P Ψ c) →
  {T | alg Ψ n Φ Δ F a T} + {∀ T, ¬ alg Ψ n Φ Δ F a T}.
Proof.
  intros HS HP. destruct (infer S Ψ n Φ Δ F a) as [T|] eqn:H.
  - left. exists T. by apply (check_reflect S P _ _ _ _ _ _ HS HP).
  - right. intros T HT. apply (check_reflect S P _ _ _ _ _ _ HS HP) in HT. congruence.
Defined.

(** A closed program accepted by any solver under C₀ is deadlock free. *)
Theorem check_deadlock_free S m C0 a T :
  creation_ok m nofact nofact (λ _, False) C0 → prim T →
  infer S [(C0, ids m)] 0 ∅ [] (∅, None) a = Some T →
  deadlock_free (∅, {[+ erase a +]}).
Proof.
  intros HC HT H. apply infer_alg in H as (c & Hs & Hc).
  by eapply synth_deadlock_free.
Qed.
