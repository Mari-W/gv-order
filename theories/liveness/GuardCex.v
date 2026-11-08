(** * The unrepaired guard admits a τ-divergent program (sharp edges 161)

    Force is call by name: forcing a box runs its body. The guard of
    entry 160 allowed (force x) e also when the box body is not a λ,
    and then the body forces its own self before any channel step.

      bad  = !(x. let ∗ = (force x) g in λy. y)      g guarded
      main = (force bad) ∗

    [main] is statically typed ([cx_main_typed]), passes the unrepaired
    check [gall0] ([cx_guarded0]), and τ-diverges ([cx_tau_diverges]),
    so the live fundamental theorem fails for the unrepaired guard
    ([live_guarded_unrepaired_false]). The repaired [guarded] of Guard.v
    allows the case only under the λs of a box body. It rejects [main]
    ([cx_not_guarded]) and keeps the examples ([guarded_examples]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.Guard liveness.LiveKob examples.ExampleTools.
From LRGV Require examples.Forwarder examples.TailCall examples.cfst.FirstAction examples.SemRounds.

Local Set Warnings "-register-all".

(** ** The unrepaired guard of entry 160 *)

Fixpoint ok0 (x : nat) (e : expr) : bool :=
  match e with
  | Var y => negb (Nat.eqb x y)
  | EUnit | Konst _ | Chan _ => true
  | Lam b | EBox b => negb (occurs (S x) b)
  | App (App (Konst KForce) (Var y)) e2 =>
      if Nat.eqb x y then gd e2 && ok0 x e2 else ok0 x e2
  | App (Lam b) e2 => ok0 x e2 && (gd e2 || ok0 (S x) b)
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => ok0 x e1 && (gd e1 || ok0 x e2)
  | LetP e1 e2 => ok0 x e1 && (gd e1 || ok0 (S (S x)) e2)
  | Inj1 e | Inj2 e => ok0 x e
  | Case e e1 e2 => ok0 x e && (gd e || (ok0 (S x) e1 && ok0 (S x) e2))
  end.

Fixpoint okv0 (x : nat) (e : expr) : bool :=
  match e with Lam b => okv0 (S x) b | _ => ok0 x e end.

Fixpoint gall0 (e : expr) : bool :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ => true
  | EBox b => okv0 0 b && gall0 b
  | Lam e | Inj1 e | Inj2 e => gall0 e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => gall0 e1 && gall0 e2
  | Case e e1 e2 => gall0 e && gall0 e1 && gall0 e2
  end.

Definition gptyped0 (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ptyped W Σ p T ∧ ∀ e, e ∈ p.2 → gall0 e = true.

Definition cx_C : bcs := BCs [] (λ _, False).
Definition cx_fty : ty := TLolli None None TUnit TUnit.
Definition cx_bty : ty := TBox 1 0 cx_C (TLolli (Some (pv 0 1)) None TUnit cx_fty).

(** A guarded unit term: a channel at the box variable ζ (new@ζ, the
    constant world of sharp edges 172), one end closed by a spawned
    thread, the other by the caller. The upper point of the box is
    ζ+1, so that the close at ζ passes the gate. *)
Definition cx_g : expr :=
  let_new_pair (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1))))) (App EClos (Var 1))).

Definition cx_body : expr := LetU (App (App EForce (Var 0)) cx_g) (Lam (Var 0)).
Definition cx_bad : expr := EBox cx_body.
Definition cx_main : expr := App (App EForce cx_bad) EUnit.

Theorem cx_guarded0 : gall0 cx_main = true.
Proof. vm_compute. reflexivity. Qed.

(** The repaired guard rejects it. *)
Theorem cx_not_guarded : ¬ guarded cx_main.
Proof. unfold guarded. vm_compute. discriminate. Qed.

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

Lemma cx_bad_typed W F : strict W → typed W ∅ [] ∅ [] F cx_bad cx_bty.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold cx_bad, cx_bty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  change (bcs_inst (pshift 1) cx_C) with cx_C.
  replace (pup 1 (pshift 1) 0 +ₚ 1) with (pv 0 1) by reflexivity.
  change (bcs_inst (pshift 1) cx_C) with cx_C.
  cbn. unfold cx_body. tstep.
  - eapply tv_app; [exact HW|reflexivity| | |apply ubs_none].
    + apply (typed_force0 W _ _ _ _ _ _ 1 cx_C (Some (pv 0 1)) cx_fty [pvar 0]); [done|done| | | |tstep].
      * apply bcs_hold_intro. by intros g Hg.
      * apply Forall_singleton. eapply skn_inst; [by left|by left|done].
      * apply ubs_intro; [intros y Hy; mem_cases Hy|]. exists (pv 0 1). split; [done|apply sle_refl, HW].
    + cbn. unfold cx_g, let_new_pair.
      apply (t_new_at W _ _ _ _ _ _ _ SEnd (pvar 0) HWs); [eapply skn_inst; [by left|by left|done]|].
      cbn. tstep.
      { tstep; [|apply KTSpawn|done|apply ubs_none].
        eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pvar 0))) (Some (pvar 0)) 1).
        { set_solver. }
        { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
        cbn. tstep; [tstep|]. cbn.
        tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_dual (pvar 0)). split; [done|]. apply sle_refl, HW. }
      cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; set_solver|].
      cbn. exists (pv 0 1). split; [by rewrite lookup_insert_eq|].
      right. apply (slt_po W _ (pvar 0) HW).
  - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit None None 1); [set_solver|done|tstep].
Qed.

Lemma cx_main_typed : typed (Wpo [0]) ∅ [] ∅ [] (∅, None) cx_main TUnit.
Proof.
  pose proof (proj1 (Wpo_strict [0])) as HW. unfold cx_main.
  eapply tv_app; [exact HW|reflexivity| | |apply ubs_none].
  - apply (typed_force0 _ _ _ _ _ _ _ 1 cx_C (Some (pv 0 1)) cx_fty [pc 0 0]); [done|done| | | |].
    + apply bcs_hold_intro. by intros g Hg.
    + apply Forall_singleton. left. unfold pt_known. simpl. set_solver.
    + apply ubs_intro; [intros y Hy; set_solver|done].
    + apply cx_bad_typed, Wpo_strict.
  - tstep.
Qed.

(** ** The live fundamental theorem fails for the guarded system *)

Theorem cx_gptyped0 : gptyped0 (Wpo [0]) ∅ (∅, {[+ cx_main +]}) TUnit.
Proof.
  split; [apply ptyped_closed; [constructor|apply cx_main_typed]|].
  intros e He. apply gmultiset_elem_of_singleton in He as ->. apply cx_guarded0.
Qed.

Theorem live_guarded_unrepaired_false :
  ¬ (∀ W p T, strict W → gptyped0 W ∅ p T → ∀ n, LPrel n W ∅ T p).
Proof.
  intros H. apply cx_tau_diverges, (live_no_tau_divergence (Wpo [0]) TUnit).
  apply H; [apply Wpo_strict|apply cx_gptyped0].
Qed.

(** ** The repaired guard keeps the examples *)

Theorem guarded_examples :
  guarded Forwarder.fw_main ∧ guarded TailCall.tc_main ∧
  guarded FirstAction.fa_go ∧ guarded FirstAction.fac_go ∧ guarded SemRounds.rK.
Proof. unfold guarded. vm_compute. repeat split. Qed.
