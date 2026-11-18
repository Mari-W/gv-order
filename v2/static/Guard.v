(** * The guard as guarded recursion (stage S5, Appendix A.2)

      Λ ⊢▷ t    [lguard], Λ : nat → bool the ▷-marked variables
      ∅ ⊢▷ t    the guard of a closed thread, asked by live and
                lock-free typing

    The guard is a judgment beside typing. It is no clause of the
    relation. It keeps the self of a box from being used before the box
    body has acted on a channel, so that a forced box takes a costly
    step before it can force itself again. The live table κ_L has β
    free, and without the guard the box !(f = force f) is typable and
    τ-divergent (Appendix B #13, #14).

    The rules read as guarded recursion. Λ marks the variables at ▷,
    later. A box puts its self at ▷ ([gl_box]). A variable at ▷ cannot
    be used ([gl_var]). A λ keeps the marks of its scope ([gl_lam]),
    because its body may run at the level where the λ is a value. A term
    that acts before it returns ([acts], a send, receive, close, select
    or branch) ticks the context for what runs after it, ▷A becomes A
    ([gl_tick_app] and its siblings), because the rest runs one level
    lower, where the selves are in V.

    The rules are those of theories/liveness/GuardRules.v with two
    simplifications. Marks propagate into λ bodies instead of the
    premise that a λ captures no marked variable, which is more
    permissive and needs no second judgment. The forceable marks under
    the λs of a box body and the rule (force f) e2 for an acting e2 are
    gone. GuardCex, the counterexample to the unrepaired form of that
    rule (Appendix B #15), no longer has a rule to exploit. *)

From GV Require Import lang.Syntax.

(** ** Terms that act before they return *)

Definition sprim (k : prim) : Prop :=
  match k with PSend | PRecv | PClose | PSel _ | PBra => True | _ => False end.

Inductive acts : expr → Prop :=
  | acts_op k e : sprim k → acts (Op k e)
  | acts_op_arg k e : acts e → acts (Op k e)
  | acts_app1 e1 e2 : acts e1 → acts (App e1 e2)
  | acts_app2 e1 e2 : acts e2 → acts (App e1 e2)
  | acts_pair1 e1 e2 : acts e1 → acts (Pair e1 e2)
  | acts_pair2 e1 e2 : acts e2 → acts (Pair e1 e2)
  | acts_letu1 e1 e2 : acts e1 → acts (LetU e1 e2)
  | acts_letu2 e1 e2 : acts e2 → acts (LetU e1 e2)
  | acts_letp1 e1 e2 : acts e1 → acts (LetP e1 e2)
  | acts_letp2 e1 e2 : acts e2 → acts (LetP e1 e2)
  | acts_let1 e1 e2 : acts e1 → acts (ELet e1 e2)
  | acts_let2 e1 e2 : acts e2 → acts (ELet e1 e2)
  | acts_inj1 e : acts e → acts (Inj1 e)
  | acts_inj2 e : acts e → acts (Inj2 e)
  | acts_case e e1 e2 : acts e → acts (Case e e1 e2)
  | acts_branches e e1 e2 : acts e1 → acts e2 → acts (Case e e1 e2).

(** ** The rules *)

(** No variable at ▷. *)
Global Instance marks_empty : Empty (nat → bool) := λ _, false.

Reserved Notation "Λ ⊢▷ t" (at level 74, t at level 60, format "Λ  ⊢▷  t").

Inductive lguard : (nat → bool) → expr → Prop :=
  | gl_var L y : L y = false → L ⊢▷ (Var y)
  | gl_unit L : L ⊢▷ EUnit
  | gl_chan L o : L ⊢▷ (Chan o)
  | gl_new L ℓ : L ⊢▷ (ENew ℓ)
  | gl_lam L b : (false .: L) ⊢▷ b → L ⊢▷ (Lam b)
  | gl_box L b : (true .: L) ⊢▷ b → L ⊢▷ (EBox b)
  | gl_op L k e : L ⊢▷ e → L ⊢▷ (Op k e)
  | gl_app L e1 e2 : L ⊢▷ e1 → L ⊢▷ e2 → L ⊢▷ (App e1 e2)
  | gl_tick_app L e1 e2 : L ⊢▷ e1 → acts e1 → ∅ ⊢▷ e2 → L ⊢▷ (App e1 e2)
  | gl_pair L e1 e2 : L ⊢▷ e1 → L ⊢▷ e2 → L ⊢▷ (Pair e1 e2)
  | gl_tick_pair L e1 e2 : L ⊢▷ e1 → acts e1 → ∅ ⊢▷ e2 → L ⊢▷ (Pair e1 e2)
  | gl_letu L e1 e2 : L ⊢▷ e1 → L ⊢▷ e2 → L ⊢▷ (LetU e1 e2)
  | gl_tick_letu L e1 e2 : L ⊢▷ e1 → acts e1 → ∅ ⊢▷ e2 → L ⊢▷ (LetU e1 e2)
  | gl_letp L e1 e2 : L ⊢▷ e1 → (false .: false .: L) ⊢▷ e2 → L ⊢▷ (LetP e1 e2)
  | gl_tick_letp L e1 e2 : L ⊢▷ e1 → acts e1 → ∅ ⊢▷ e2 → L ⊢▷ (LetP e1 e2)
  | gl_let L e1 e2 : L ⊢▷ e1 → (false .: L) ⊢▷ e2 → L ⊢▷ (ELet e1 e2)
  | gl_tick_let L e1 e2 : L ⊢▷ e1 → acts e1 → ∅ ⊢▷ e2 → L ⊢▷ (ELet e1 e2)
  | gl_inj1 L e : L ⊢▷ e → L ⊢▷ (Inj1 e)
  | gl_inj2 L e : L ⊢▷ e → L ⊢▷ (Inj2 e)
  | gl_case L e e1 e2 : L ⊢▷ e → (false .: L) ⊢▷ e1 → (false .: L) ⊢▷ e2 →
      L ⊢▷ (Case e e1 e2)
  | gl_tick_case L e e1 e2 : L ⊢▷ e → acts e → ∅ ⊢▷ e1 → ∅ ⊢▷ e2 →
      L ⊢▷ (Case e e1 e2)
where "Λ ⊢▷ t" := (lguard Λ t).

(** ** Structure *)

Lemma marks_empty_cons : ∀ x, (false .: ∅) x = ∅ x.
Proof. by intros []. Qed.

Lemma guard_ext L L' e : (∀ x, L x = L' x) → lguard L e → lguard L' e.
Proof.
  intros HL H. revert L' HL. induction H; intros L' HL; try (by constructor; auto).
  - constructor. by rewrite <-HL.
  - constructor. apply IHlguard. intros [|x]; simpl; auto.
  - constructor. apply IHlguard. intros [|x]; simpl; auto.
  - constructor; [auto|]. apply IHlguard2. intros [|[|x]]; simpl; auto.
  - constructor; [auto|]. apply IHlguard2. intros [|x]; simpl; auto.
  - constructor; [auto| |]; [apply IHlguard2|apply IHlguard3]; intros [|x]; simpl; auto.
Qed.

Lemma acts_rename_inv e : ∀ r, acts (rename r e) → acts e.
Proof.
  induction e; intros r H; simpl in H; inversion H; subst; try (by constructor; eauto); by apply acts_branches; eauto.
Qed.

Local Ltac marks := intros [|[|x]]; simpl; done.

(** A renaming of the variables moves the marks with it. *)
Lemma guard_rename e : ∀ L r, lguard L (rename r e) → lguard (λ x, L (r x)) e.
Proof.
  induction e; intros L r H; simpl in H; inversion H; subst.
  all: try (by constructor).
  all: try (by constructor; eauto).
  - (* Lam *)
    constructor. eapply guard_ext; [|by apply IHe]. marks.
  - (* App *) apply gl_tick_app; [eauto|by eapply acts_rename_inv|].
    eapply guard_ext; [|by apply IHe2]. done.
  - apply gl_tick_pair; [eauto|by eapply acts_rename_inv|].
    eapply guard_ext; [|by apply IHe2]. done.
  - apply gl_tick_letu; [eauto|by eapply acts_rename_inv|].
    eapply guard_ext; [|by apply IHe2]. done.
  - apply gl_letp; [eauto|]. eapply guard_ext; [|by apply IHe2]. marks.
  - apply gl_tick_letp; [eauto|by eapply acts_rename_inv|].
    eapply guard_ext; [|by apply IHe2]. done.
  - apply gl_let; [eauto|]. eapply guard_ext; [|by apply IHe2]. marks.
  - apply gl_tick_let; [eauto|by eapply acts_rename_inv|].
    eapply guard_ext; [|by apply IHe2]. done.
  - apply gl_case; [eauto| |].
    + eapply guard_ext; [|by apply IHe2]. marks.
    + eapply guard_ext; [|by apply IHe3]. marks.
  - apply gl_tick_case; [eauto|by eapply acts_rename_inv| |].
    + eapply guard_ext; [|by apply IHe2]. done.
    + eapply guard_ext; [|by apply IHe3]. done.
  - (* EBox *)
    constructor. eapply guard_ext; [|by apply IHe]. marks.
Qed.
