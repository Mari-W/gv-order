(** * A guarded box that τ-diverges (sharp edges 161)

    Force is call by name: forcing a box runs its body. When the body
    is not a λ, the special case of [ok] for (force x) e lets the body
    force its own self before any channel step, and the unrolled body
    does the same again.

      bad  = !(x. let ∗ = (force x) g in λy. y)      g guarded
      main = (force bad) ∗

    [main] is statically typed in the world with one constant
    ([cx_main_typed]; the box quantifies its upper point ζ, and g closes
    a fresh channel created below ζ) and [guarded] ([cx_guarded]). Its
    thread has an infinite β sequence ([cx_tau_diverges]). So the live
    fundamental theorem fails for the guarded system of Guard.v
    ([live_guarded_false]). The special case of [ok] for (force x) e is
    sound only when the body of the box is a λ, so that forcing the
    self returns a value at once. *)

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

(** ** Typing *)

Lemma cx_bad_typed W F : world_wf W → typed W ∅ [] ∅ [] F cx_bad cx_bty.
Proof.
  intros HW. unfold cx_bad, cx_bty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  change (bcs_inst (pshift 1) cx_C) with cx_C.
  replace (pup 1 (pshift 1) 0 +ₚ 0) with (pvar 0) by reflexivity.
  change (bcs_inst (pshift 1) cx_C) with cx_C.
  cbn. unfold cx_body. tstep.
  - eapply tv_app; [exact HW|reflexivity| | |apply ubs_none].
    + apply (typed_force0 W _ _ _ _ _ _ 1 cx_C (Some (pvar 0)) cx_fty [pvar 0]); [done|done| | | |tstep].
      * apply bcs_hold_intro. by intros g Hg.
      * apply Forall_singleton. eapply skn_inst; [by left|by left|done].
      * apply ubs_intro; [intros y Hy; mem_cases Hy|]. exists (pvar 0). split; [done|apply sle_refl, HW].
    + cbn. unfold cx_g, let_new_pair.
      apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [] [pvar 0]).
      { cbn. apply Forall_singleton. eapply skn_inst; [by left|by left|done]. }
      { intros l h Hl. by apply elem_of_nil in Hl. }
      fresh_clean. tstep.
      { tstep; [|apply KTSpawn|done|apply ubs_none].
        eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pvar 0))) (Some (pvar 0)) 1).
        { rewrite fhyps_pinst_insert. set_solver. }
        { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
        cbn. tstep; [tstep|]. cbn.
        tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_dual (pvar 0)). split; [done|]. apply sle_refl, HW. }
      cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; set_solver|].
      cbn. exists (pt_inst (pshift 1) (pvar 0)). split.
      { rewrite fhyps_pinst_insert. by rewrite lookup_insert_eq. }
      right. apply (slt_fresh_r W _ (pshift 1) [] [pvar 0] (pvar 0) (pvar 0)); [by right; left|by left].
  - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit None None 1); [set_solver|done|tstep].
Qed.

Lemma cx_main_typed : typed (Wpo [0]) ∅ [] ∅ [] (∅, None) cx_main TUnit.
Proof.
  pose proof (proj1 (Wpo_strict [0])) as HW. unfold cx_main.
  eapply tv_app; [exact HW|reflexivity| | |apply ubs_none].
  - apply (typed_force0 _ _ _ _ _ _ _ 1 cx_C (Some (pvar 0)) cx_fty [pc 0 0]); [done|done| | | |].
    + apply bcs_hold_intro. by intros g Hg.
    + apply Forall_singleton. left. unfold pt_known. simpl. set_solver.
    + apply ubs_intro; [intros y Hy; set_solver|done].
    + apply cx_bad_typed, HW.
  - tstep.
Qed.

(** ** The live fundamental theorem fails for the guarded system *)

Theorem cx_gptyped : gptyped (Wpo [0]) ∅ (∅, {[+ cx_main +]}) TUnit.
Proof.
  split; [apply ptyped_closed; [constructor|apply cx_main_typed]|].
  intros e He. apply gmultiset_elem_of_singleton in He as ->. apply cx_guarded.
Qed.

Theorem live_guarded_false :
  ¬ (∀ W p T, strict W → gptyped W ∅ p T → ∀ n, LPrel n W ∅ T p).
Proof.
  intros H. apply cx_tau_diverges, (live_no_tau_divergence (Wpo [0]) TUnit).
  apply H; [apply Wpo_strict|apply cx_gptyped].
Qed.
