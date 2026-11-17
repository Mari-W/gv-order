(** * The guard (stage S5, Appendix A.2)

      guarded t    [guarded], rules [glive]

    The guard is a restriction on terms, beside the typing judgment. It
    is no clause of the relation. It keeps the self of a box from being
    used before the box body has acted on a channel, so that a forced box
    takes a costly step before it can force itself again. The live table
    κ_L has β free, and without the guard the box !(f = force f) is
    typable and τ-divergent (Appendix B #13, #14).

    [glive L e] reads marks L : nat → bool on the variables of e. A
    marked variable is the self of an enclosing box, or a variable
    captured from such a scope. It may not occur as such
    ([glive_var]). A box marks its own self ([glive_box]). A λ keeps the
    marks of its scope ([glive_lam]), because its body may run at the
    level where the λ is a value. A term that acts before it returns
    ([acts], a send, receive, close, select or branch) clears every mark
    for what runs after it ([glive_app_acts] and its siblings), because
    the rest runs one level lower, where the selves are in V.

    The rules are those of theories/liveness/GuardRules.v with two
    simplifications. Marks propagate into λ bodies instead of the
    premise that a λ captures no marked variable, which is more
    permissive and needs no second judgment. The forceable marks under
    the λs of a box body and the rule (force f) e2 for an acting e2 are
    gone. GuardCex, the counterexample to the unrepaired form of that
    rule (Appendix B #15), no longer has a rule to exploit. *)

From GV Require Export lang.Syntax.

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

Definition noL : nat → bool := λ _, false.

Inductive glive : (nat → bool) → expr → Prop :=
  | glive_var L y : L y = false → glive L (Var y)
  | glive_unit L : glive L EUnit
  | glive_chan L o : glive L (Chan o)
  | glive_new L ℓ : glive L (ENew ℓ)
  | glive_lam L b : glive (false .: L) b → glive L (Lam b)
  | glive_box L b : glive (true .: L) b → glive L (EBox b)
  | glive_op L k e : glive L e → glive L (Op k e)
  | glive_app L e1 e2 : glive L e1 → glive L e2 → glive L (App e1 e2)
  | glive_app_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (App e1 e2)
  | glive_pair L e1 e2 : glive L e1 → glive L e2 → glive L (Pair e1 e2)
  | glive_pair_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (Pair e1 e2)
  | glive_letu L e1 e2 : glive L e1 → glive L e2 → glive L (LetU e1 e2)
  | glive_letu_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (LetU e1 e2)
  | glive_letp L e1 e2 : glive L e1 → glive (false .: false .: L) e2 → glive L (LetP e1 e2)
  | glive_letp_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (LetP e1 e2)
  | glive_let L e1 e2 : glive L e1 → glive (false .: L) e2 → glive L (ELet e1 e2)
  | glive_let_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (ELet e1 e2)
  | glive_inj1 L e : glive L e → glive L (Inj1 e)
  | glive_inj2 L e : glive L e → glive L (Inj2 e)
  | glive_case L e e1 e2 : glive L e → glive (false .: L) e1 → glive (false .: L) e2 →
      glive L (Case e e1 e2)
  | glive_case_acts L e e1 e2 : glive L e → acts e → glive noL e1 → glive noL e2 →
      glive L (Case e e1 e2).

Definition guarded (t : expr) : Prop := glive noL t.

(** ** Structure *)

Lemma noL_cons : ∀ x, (false .: noL) x = noL x.
Proof. by intros []. Qed.

Lemma glive_ext L L' e : (∀ x, L x = L' x) → glive L e → glive L' e.
Proof.
  intros HL H. revert L' HL. induction H; intros L' HL; try (by constructor; auto).
  - constructor. by rewrite <-HL.
  - constructor. apply IHglive. intros [|x]; simpl; auto.
  - constructor. apply IHglive. intros [|x]; simpl; auto.
  - constructor; [auto|]. apply IHglive2. intros [|[|x]]; simpl; auto.
  - constructor; [auto|]. apply IHglive2. intros [|x]; simpl; auto.
  - constructor; [auto| |]; [apply IHglive2|apply IHglive3]; intros [|x]; simpl; auto.
Qed.

Lemma acts_rename_inv e : ∀ r, acts (rename r e) → acts e.
Proof.
  induction e; intros r H; simpl in H; inversion H; subst; try (by constructor; eauto); by apply acts_branches; eauto.
Qed.

Local Ltac marks := intros [|[|x]]; simpl; done.

(** A renaming of the variables moves the marks with it. *)
Lemma glive_rename e : ∀ L r, glive L (rename r e) → glive (λ x, L (r x)) e.
Proof.
  induction e; intros L r H; simpl in H; inversion H; subst.
  all: try (by constructor).
  all: try (by constructor; eauto).
  - (* Lam *)
    constructor. eapply glive_ext; [|by apply IHe]. marks.
  - (* App *) apply glive_app_acts; [eauto|by eapply acts_rename_inv|].
    eapply glive_ext; [|by apply IHe2]. done.
  - apply glive_pair_acts; [eauto|by eapply acts_rename_inv|].
    eapply glive_ext; [|by apply IHe2]. done.
  - apply glive_letu_acts; [eauto|by eapply acts_rename_inv|].
    eapply glive_ext; [|by apply IHe2]. done.
  - apply glive_letp; [eauto|]. eapply glive_ext; [|by apply IHe2]. marks.
  - apply glive_letp_acts; [eauto|by eapply acts_rename_inv|].
    eapply glive_ext; [|by apply IHe2]. done.
  - apply glive_let; [eauto|]. eapply glive_ext; [|by apply IHe2]. marks.
  - apply glive_let_acts; [eauto|by eapply acts_rename_inv|].
    eapply glive_ext; [|by apply IHe2]. done.
  - apply glive_case; [eauto| |].
    + eapply glive_ext; [|by apply IHe2]. marks.
    + eapply glive_ext; [|by apply IHe3]. marks.
  - apply glive_case_acts; [eauto|by eapply acts_rename_inv| |].
    + eapply glive_ext; [|by apply IHe2]. done.
    + eapply glive_ext; [|by apply IHe3]. done.
  - (* EBox *)
    constructor. eapply glive_ext; [|by apply IHe]. marks.
Qed.
