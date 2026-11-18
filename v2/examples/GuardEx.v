(** * The guard against Appendix B (stage S5)

    The rejections. A box that forces itself before it acts
    ([div_not_guarded], #14), PN's ⟨fix λx.x⟩ as a box whose λ applies
    the forced self ([pn_fix_not_guarded], #13), the box of GuardCex,
    which forces itself in the hole of a let ([cx_not_guarded], #15),
    and a recursion that spawns the forced self before any action, the
    shape of the KobForwarder and of the infinite spawn chain
    ([spawn_loop_not_guarded], #12, #40).

    The acceptances. A server loop that receives before it recurses
    ([loop_guarded]) and the stage of the C2 pipeline of B.1 #4, which
    receives, creates a channel and spawns the forced self on one end
    ([stage_guarded]). *)

From GV Require Export lang.Syntax static.Guard.

Local Ltac inv_all :=
  repeat match goal with
  | H : lguard _ _ |- _ => inversion H; subst; clear H
  | H : acts _ |- _ => inversion H; subst; clear H
  | H : sprim _ |- _ => simpl in H; done
  end.

(** !(f = force f) *)
Definition div_box : expr := EBox (EForce (Var 0)).

Lemma div_not_guarded : ¬ ∅ ⊢▷ div_box.
Proof. intros H. unfold div_box in H. inv_all. done. Qed.

(** !(f = λx. (force f) x) *)
Definition pn_fix : expr := EBox (Lam (App (EForce (Var 1)) (Var 0))).

Lemma pn_fix_not_guarded : ¬ ∅ ⊢▷ pn_fix.
Proof. intros H. unfold pn_fix in H. inv_all; done. Qed.

(** !(f = let ∗ = (force f) ∗ in λy. y) *)
Definition cx_box : expr := EBox (LetU (App (EForce (Var 0)) EUnit) (Lam (Var 0))).

Lemma cx_not_guarded : ¬ ∅ ⊢▷ cx_box.
Proof. intros H. unfold cx_box in H. inv_all; done. Qed.

(** !(f = λc. spawn (λ_. (force f) c)) *)
Definition spawn_loop : expr := EBox (Lam (ESpawn (Lam (App (EForce (Var 2)) (Var 1))))).

Lemma spawn_loop_not_guarded : ¬ ∅ ⊢▷ spawn_loop.
Proof. intros H. unfold spawn_loop in H. inv_all; done. Qed.

(** !(f = λx. let ⟨v, x'⟩ = recv x in (force f) x') *)
Definition loop : expr := EBox (Lam (LetP (ERecv (Var 0)) (App (EForce (Var 3)) (Var 0)))).

Lemma loop_guarded : ∅ ⊢▷ loop.
Proof.
  apply gl_box, gl_lam, gl_tick_letp.
  - apply gl_op, gl_var. done.
  - by apply acts_op.
  - apply gl_app; [apply gl_op|]; by apply gl_var.
Qed.

(** The stage of B.1 #4:
    !(f = λin. let ⟨v, in⟩ = recv in in let ∗ = close in in
              let ⟨a, b⟩ = new in let ∗ = spawn (λ_. (force f) b) in close (send ⟨v, a⟩)) *)
Definition stage : expr :=
  EBox (Lam (LetP (ERecv (Var 0))
    (LetU (EClose (Var 0))
      (LetP ENew0
        (LetU (ESpawn (Lam (App (EForce (Var 6)) (Var 1))))
          (EClose (ESend (Pair (Var 3) (Var 1))))))))).

Lemma stage_guarded : ∅ ⊢▷ stage.
Proof.
  apply gl_box, gl_lam, gl_tick_letp; [apply gl_op, gl_var; done|by apply acts_op|].
  apply gl_letu; [apply gl_op, gl_var; done|].
  apply gl_letp; [apply gl_new|].
  apply gl_letu.
  - apply gl_op, gl_lam, gl_app; [apply gl_op|]; by apply gl_var.
  - apply gl_op, gl_op, gl_pair; by apply gl_var.
Qed.
