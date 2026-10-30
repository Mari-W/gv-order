(** * Typing of Padovani and Novara on our terms

    Table 2 (pdf p. 8), [T-APP-POLY] (p. 10), the constant schemes
    (p. 7) and wrapping (p. 13) of Padovani and Novara, FORTE 2015, on
    the terms of lang/Syntax.v. A derivation Γ ⊢ e : t & τ also produces
    the term e′ of the static system it translates to, so the judgment
    is [pn_typed Γ e t τ e′]. The translation needs the types, because a
    function of level ⊤ becomes a box and its application a force.

    The source syntax of fragment v1.

    - Var, λ (Lam), application (App) and () (EUnit) as in the paper.
    - fix λf.e is [EBox e], f the index 0 of e (repair R2 of
      padovani-novara-counterexamples.txt). The type of f is an arrow of
      level ⊤.
    - let a = new() in e is [LetP (App ENew EUnit) e]. The name a of
      type #[t]ⁿ becomes two variables, its ? end at index 1 and its ! end
      at index 0, because our variables are linear and our new returns
      both ends.
    - send e₁ e₂, recv e and fork e are [App (App ESend e₁) e₂],
      [App ERecv e] and [App ESpawn e]. Constants appear only applied.
      An unapplied constant is η-expanded by the programmer, with the
      same type.
    - inj₁ e, inj₂ e and case for sums of unlimited types.
    - wrap and unwrap are erased. [T-Conv] folds and unfolds a recursive
      channel and converts ⌈t⌉ᵐ to ⇑ᵐ t and back, at the top of a type.

    Every discrepancy with the paper is listed in
    docs/extensions/adequacy/padovani-novara.md §7. *)

From stdpp Require Import base list numbers.
From LRGV Require Export lang.Syntax pn.PNTypes.

(** ** Environments

    Lists over de Bruijn indices, [None] for a spent binding. *)

Definition penv := list (option pty).

(** un(Γ). *)
Definition penv_un (Γ : penv) : Prop := ∀ t, Some t ∈ Γ → un t.

(** Γ = Γ′, x : t with un(Γ′). *)
Definition penv_only_un (Γ : penv) (x : nat) (t : pty) : Prop :=
  Γ !! x = Some (Some t) ∧ ∀ y t', y ≠ x → Γ !! y = Some (Some t') → un t'.

(** Γ = Γ₁ + Γ₂ (p. 8). An unlimited binding goes to both sides
    (t + t = t), a linear one to exactly one side. *)
Inductive pn_split : penv → penv → penv → Prop :=
  | ps_nil : pn_split [] [] []
  | ps_none Γ Γ1 Γ2 : pn_split Γ Γ1 Γ2 → pn_split (None :: Γ) (None :: Γ1) (None :: Γ2)
  | ps_l t Γ Γ1 Γ2 : pn_split Γ Γ1 Γ2 → pn_split (Some t :: Γ) (Some t :: Γ1) (None :: Γ2)
  | ps_r t Γ Γ1 Γ2 : pn_split Γ Γ1 Γ2 → pn_split (Some t :: Γ) (None :: Γ1) (Some t :: Γ2)
  | ps_un t Γ Γ1 Γ2 : un t → pn_split Γ Γ1 Γ2 → pn_split (Some t :: Γ) (Some t :: Γ1) (Some t :: Γ2).

(** |Γ|, the least level of a binding, ⊤ ([None]) when there is none. *)
Fixpoint env_lev (Γ : penv) : option Z :=
  match Γ with
  | [] => None
  | None :: Γ => env_lev Γ
  | Some t :: Γ => omin (tlev t) (env_lev Γ)
  end.

(** ** Conversion: fold, unfold, wrap and unwrap at the top of a type *)

Inductive pconv1 : pty → pty → Prop :=
  | pc_unfold p m n : pconv1 (PRec p m n) (PChan p (PDisp m (PRec p m n)) n)
  | pc_wrap m t : pconv1 (PDisp m t) (lshift m t).

Inductive pconv : pty → pty → Prop :=
  | pconv_refl t : pconv t t
  | pconv_fw t t' t'' : pconv1 t t' → pconv t' t'' → pconv t t''
  | pconv_bw t t' t'' : pconv1 t' t → pconv t' t'' → pconv t t''.

(** ** Terms of the translation

    () becomes a box of ∗, because unit is unlimited in P&N and ∗ is
    linear here. send, recv and fork become closed λ terms. Each linear
    channel is a session with one message followed by Close, so send and
    recv close the channel after the message. *)

Definition unitv : expr := EBox EUnit.

Definition send_tr : expr :=
  Lam (Lam (LetU (App EClos (App ESend (Pair (Var 0) (Var 1)))) unitv)).

Definition recv_tr : expr :=
  Lam (LetP (App ERecv (Var 0)) (LetU (App EClos (Var 0)) (Var 1))).

(** The thunk of fork is applied to (), and forced first when it has
    level ⊤. *)
Definition fork_tr (poly : bool) : expr :=
  Lam (LetU (App ESpawn (Lam (LetU (Var 0)
         (App EForce (App (if poly then App EForce (Var 1) else Var 1) unitv)))))
       unitv).

Definition inj1_tr : expr := Lam (EBox (Inj1 (Var 1))).
Definition inj2_tr : expr := Lam (EBox (Inj2 (Var 1))).

(** A λ of level ⊤ becomes a box. Inside the box the index 0 is the box
    itself, so the body skips it. *)
Definition lam_tr (r : option Z) (e : expr) : expr :=
  match r with
  | Some _ => Lam e
  | None => EBox (Lam (rename (upren S) e))
  end.

(** ** The judgment Γ ⊢ e : t & τ ⇝ e′ *)

Inductive pn_typed : penv → expr → pty → lvl → expr → Prop :=
  | pn_name Γ x t :                                          (* T-Name *)
      penv_only_un Γ x t →
      pn_typed Γ (Var x) t LBot (Var x)
  | pn_unit Γ :                                              (* T-Const () *)
      penv_un Γ →
      pn_typed Γ EUnit PUnit LBot unitv
  | pn_fun Γ e e' t s ρ :                                    (* T-Fun *)
      pn_typed (Some t :: Γ) e s ρ e' →
      pn_typed Γ (Lam e) (PArr t (env_lev Γ) ρ s) LBot (lam_tr (env_lev Γ) e')
  | pn_app Γ Γ1 Γ2 e1 e2 e1' e2' t r σ s τ1 τ2 :            (* T-App, ρ ∈ ℤ *)
      pn_split Γ Γ1 Γ2 →
      pn_typed Γ1 e1 (PArr t (Some r) σ s) τ1 e1' →
      pn_typed Γ2 e2 t τ2 e2' →
      lvl_lt τ1 (olvl (env_lev Γ2)) → lvl_lt τ2 (LZ r) →
      pn_typed Γ (App e1 e2) s (lvl_max σ (lvl_max τ1 τ2)) (App e1' e2')
  | pn_app_poly Γ Γ1 Γ2 e1 e2 e1' e2' t σ s τ1 τ2 n :      (* T-App-Poly *)
      pn_split Γ Γ1 Γ2 →
      pn_typed Γ1 e1 (PArr t None σ s) τ1 e1' →
      pn_typed Γ2 e2 (lshift n t) τ2 e2' →
      lvl_lt τ1 (olvl (env_lev Γ2)) → lvl_lt τ2 LTop →
      pn_typed Γ (App e1 e2) (lshift n s) (lvl_max (lvl_sh n σ) (lvl_max τ1 τ2))
        (App (App EForce e1') e2')
  | pn_new Γ e e' t n s τ :                                  (* let a = new() in e *)
      lvl_lt (LZ n) (olvl (tlev t)) → payok t →
      pn_typed (Some (PChan false t n) :: Some (PChan true t n) :: Γ) e s τ e' →
      pn_typed Γ (LetP (App ENew EUnit) e) s τ (LetP (App ENew EUnit) e')
  | pn_send Γ Γ1 Γ2 e1 e2 e1' e2' t n τ1 τ2 :               (* send e₁ e₂ *)
      pn_split Γ Γ1 Γ2 →
      pn_typed Γ1 e1 (PChan false t n) τ1 e1' →
      pn_typed Γ2 e2 t τ2 e2' →
      lvl_lt (LZ n) (olvl (tlev t)) → payok t →
      lvl_lt τ1 (olvl (env_lev Γ2)) → lvl_lt τ2 (LZ n) →
      pn_typed Γ (App (App ESend e1) e2) PUnit (lvl_max (LZ n) (lvl_max τ1 τ2))
        (App (App send_tr e1') e2')
  | pn_recv Γ e e' t n τ :                                   (* recv e *)
      pn_typed Γ e (PChan true t n) τ e' →
      lvl_lt (LZ n) (olvl (tlev t)) → payok t →
      pn_typed Γ (App ERecv e) t (lvl_max (LZ n) τ) (App recv_tr e')
  | pn_fork Γ e e' r σ τ :                                   (* fork e *)
      pn_typed Γ e (PArr PUnit r σ PUnit) τ e' →
      pn_typed Γ (App ESpawn e) PUnit τ
        (App (fork_tr (match r with Some _ => false | None => true end)) e')
  | pn_fix Γ e e' t σ s :                                    (* fix λf.e *)
      penv_un Γ →
      pn_typed (Some (PArr t None σ s) :: Γ) e (PArr t None σ s) LBot e' →
      pn_typed Γ (EBox e) (PArr t None σ s) LBot (EBox (App EForce e'))
  | pn_inj1 Γ e e' t s τ :
      pn_typed Γ e t τ e' → un t → un s →
      pn_typed Γ (Inj1 e) (PSum t s) τ (App inj1_tr e')
  | pn_inj2 Γ e e' t s τ :
      pn_typed Γ e s τ e' → un t → un s →
      pn_typed Γ (Inj2 e) (PSum t s) τ (App inj2_tr e')
  | pn_case Γ Γ1 Γ2 e e1 e2 e' e1' e2' t s u τ1 τ2 :
      pn_split Γ Γ1 Γ2 →
      pn_typed Γ1 e (PSum t s) τ1 e' → un t → un s →
      pn_typed (Some t :: Γ2) e1 u τ2 e1' →
      pn_typed (Some s :: Γ2) e2 u τ2 e2' →
      lvl_lt τ1 (olvl (env_lev Γ2)) →
      pn_typed Γ (Case e e1 e2) u (lvl_max τ1 τ2) (Case (App EForce e') e1' e2')
  | pn_conv Γ e e' t t' τ :                                  (* wrap, unwrap, fold *)
      pn_typed Γ e t τ e' → pconv t t' →
      pn_typed Γ e t' τ e'.

(** [T-App] at a function of level ⊤ is [T-App-Poly] at the shift 0. *)
Lemma pn_app_top Γ Γ1 Γ2 e1 e2 e1' e2' t σ s τ1 τ2 :
  pn_split Γ Γ1 Γ2 →
  pn_typed Γ1 e1 (PArr t None σ s) τ1 e1' →
  pn_typed Γ2 e2 t τ2 e2' →
  lvl_lt τ1 (olvl (env_lev Γ2)) → lvl_lt τ2 LTop →
  pn_typed Γ (App e1 e2) s (lvl_max σ (lvl_max τ1 τ2)) (App (App EForce e1') e2').
Proof.
  intros Hs H1 H2 Hl1 Hl2.
  assert (lvl_sh 0 σ = σ) as Eσ by (destruct σ; simpl; zeq).
  rewrite <-Eσ, <-(lshift_0 s) at 1. eapply pn_app_poly; [done|done| |done|done].
  by rewrite lshift_0.
Qed.

(** ** Sugar

    let x = e₁ in e₂ and e₁; e₂ are (λx.e₂) e₁, as in the paper (p. 5). *)
Definition plet (e1 e2 : expr) : expr := App (Lam e2) e1.
