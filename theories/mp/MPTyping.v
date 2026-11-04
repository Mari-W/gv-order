(** * Typing of Mordido and Pérez on our terms

    Figs. 5, 6, 13 and 14 (pp. 11, 12, 25, 26) of Mordido and Pérez,
    with repairs R1 to R6 and the restrictions of fragment v1
    (docs/extensions/adequacy/mordido-perez.md, restriction log). A
    derivation Θ | Γ ⊢ e : T ⋄ σs also yields the term e′ of the static
    system it translates to, so the judgment is [mtyped Θ Γ e T σs e′],
    as [pn_typed] for Padovani and Novara.

    Source terms are the terms of lang/Syntax.v with priorities erased
    (R5 erases inst, and priority and type applications have no run-time
    content).

    - Var, λ (Lam) and application as in the paper. let x = e₁ in e₂ is
      [App (Lam e₂) e₁] and e₁; e₂ is [LetU e₁ e₂].
    - rec f. Λιs. λx.e is [EBox (Lam e)], with x at index 0 and f at
      index 1 (repair R4 in the λ form). Without f it is T-PAbs followed
      by T-AbsUn.
    - let (x, y) = new S n₁ n₂ in e is [LetP (App ENew EUnit) e], with
      the end of type S at index 1 and its dual at index 0. The
      translation emits the encoded let of the existential new,
      [let_new_pair e′].
    - send e₁ e₂ is [App ESend (Pair e₁ e₂)], let (x, c) = receive e in
      e′ is [LetP (App ERecv e) e′], close and wait are [App EClos e].
    - select ℓᵢ e is [App ESel1 e] or [App ESel2 e], and
      match e with {ℓ₁ → e₁, ℓ₂ → e₂} is [Case (App EBra e) e₁ e₂].
    - fork e is [App ESpawn e] with a linear thunk (repair R2).

    Effects are lists of priorities read as their maximum and lower
    bounds lists read as their minimum, so ⊔ and |Γ| need no symbolic
    join. Priority comparisons hold at every valuation of the priority
    context Θ. *)

From stdpp Require Import base list numbers.
From LRGV Require Export lang.Syntax mp.MPTypes.

(** ** Priority contexts

    Θ is a number of variables and a list of strict inequalities. An
    interval ι ∈ (a, b) is the pair a < ι, ι < b, and a closed end
    [a, … is a − 1 < ι. *)

Record pctx := PCtx { pc_nv : nat; pc_cs : list (prio * prio) }.

Definition models (Θ : pctx) (v : val) : Prop :=
  length v = pc_nv Θ ∧ Forall (λ c, xlt (evalp v c.1) (evalp v c.2)) (pc_cs Θ).

(** max σs < min ρs at every valuation. *)
Definition plt (Θ : pctx) (ef lo : list prio) : Prop :=
  ∀ v, models Θ v → ∀ ρ, ρ ∈ lo → xlt (xmaxl v ef) (evalp v ρ).

(** σs ≤ σs′ for a latent effect: a segment of it, an effect with ⊤,
    or strictly below at every valuation. *)
Definition hle (Θ : pctx) (ef ef' : list prio) : Prop :=
  ef = [] ∨ PTop ∈ ef' ∨ (∃ l1 l2, ef' = l1 ++ ef ++ l2) ∨
  (ef' ≠ [] ∧ ∀ v, models Θ v → xlt (xmaxl v ef) (xmaxl v ef')).

(** The effect is not ⊤ (ρ₂ < ⊤ for an argument of T-AbsUn). *)
Definition pntop (Θ : pctx) (ef : list prio) : Prop :=
  ∀ v, models Θ v → xlt (xmaxl v ef) XT.

Definition evalZ (v : val) (ρ : prio) : Z :=
  match evalp v ρ with XZ z => z | _ => 0%Z end.

(** σs instantiates Θ′ under Θ (T-PApp, ρ ∈ φ). *)
Definition pinst_ok (Θ Θ' : pctx) (σ : list prio) : Prop :=
  length σ = pc_nv Θ' ∧ Forall pfin σ ∧ ∀ v, models Θ v → models Θ' (evalZ v <$> σ).

(** ** Environments *)

Definition menv := list (option mty).

Definition menv_un (Γ : menv) : Prop := ∀ t, Some t ∈ Γ → mun t.

Definition menv_only_un (Γ : menv) (x : nat) (t : mty) : Prop :=
  Γ !! x = Some (Some t) ∧ ∀ y t', y ≠ x → Γ !! y = Some (Some t') → mun t'.

(** Γ = Γ₁ ∘ Γ₂ (Fig. 12): a type of priority ⊤ to both sides. *)
Inductive msplit : menv → menv → menv → Prop :=
  | ms_nil : msplit [] [] []
  | ms_none Γ Γ1 Γ2 : msplit Γ Γ1 Γ2 → msplit (None :: Γ) (None :: Γ1) (None :: Γ2)
  | ms_l t Γ Γ1 Γ2 : msplit Γ Γ1 Γ2 → msplit (Some t :: Γ) (Some t :: Γ1) (None :: Γ2)
  | ms_r t Γ Γ1 Γ2 : msplit Γ Γ1 Γ2 → msplit (Some t :: Γ) (None :: Γ1) (Some t :: Γ2)
  | ms_un t Γ Γ1 Γ2 : mun t → msplit Γ Γ1 Γ2 → msplit (Some t :: Γ) (Some t :: Γ1) (Some t :: Γ2).

(** |Γ| as a list. *)
Fixpoint envp (Γ : menv) : list prio :=
  match Γ with
  | [] => []
  | None :: Γ => envp Γ
  | Some t :: Γ => tprios t ++ envp Γ
  end.

(** A priority abstraction captures only units and abstractions. *)
Definition menv_poly (Γ : menv) : Prop :=
  ∀ t, Some t ∈ Γ → t = MUnit ∨ ∃ nv cs T ef V, t = MPoly nv cs T ef V.

(** ** Terms of the translation

    Unit has priority ⊤ and is copied freely, so it becomes the box
    of ∗, and a close returns it. fork forces the unit its thunk
    returns. *)

Definition unitv : expr := EBox EUnit.

Definition fork_tr : expr :=
  Lam (LetU (App ESpawn (Lam (LetU (Var 0) (App EForce (App (Var 1) unitv))))) unitv).

(** ** The judgment Θ | Γ ⊢ e : T ⋄ σs ⇝ e′ *)

Inductive mtyped (Θ : pctx) : menv → expr → mty → list prio → expr → Prop :=
  | m_var Γ x t :                                            (* T-Var *)
      menv_only_un Γ x t →
      mtyped Θ Γ (Var x) t [] (Var x)
  | m_unit Γ :                                               (* T-Const () *)
      menv_un Γ →
      mtyped Θ Γ EUnit MUnit [] unitv
  | m_lam Γ e e' T V ef :                                    (* T-AbsLin *)
      envp Γ ≠ [] →
      mtyped Θ (Some T :: Γ) e V ef e' →
      mtyped Θ Γ (Lam e) (MArr T (envp Γ) ef V) [] (Lam e')
  | m_app Γ Γ1 Γ2 e1 e2 e1' e2' T lo σ V ef1 ef2 :           (* T-App *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 (MArr T lo σ V) ef1 e1' →
      mtyped Θ Γ2 e2 T ef2 e2' →
      plt Θ ef1 (envp Γ2) → plt Θ ef2 lo →
      mtyped Θ Γ (App e1 e2) V (ef1 ++ ef2 ++ σ) (App e1' e2')
  | m_app_poly Γ Γ1 Γ2 e1 e2 e1' e2' nv cs T σ V ef1 ef2 σs : (* T-PApp, T-App *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 (MPoly nv cs T σ V) ef1 e1' →
      pinst_ok Θ (PCtx nv cs) σs →
      mtyped Θ Γ2 e2 (msub σs T) ef2 e2' →
      plt Θ ef1 (envp Γ2) → pntop Θ ef2 →
      mtyped Θ Γ (App e1 e2) (msub σs V) (ef1 ++ ef2 ++ (psub σs <$> σ))
        (App (App EForce e1') e2')
  | m_fix Γ e e' nv cs T σ V ef :                           (* R4, T-PAbs, T-AbsUn *)
      menv_poly Γ →
      mtyped (PCtx nv cs) (Some T :: Some (MPoly nv cs T σ V) :: Γ) e V ef e' →
      hle (PCtx nv cs) ef σ →
      mtyped Θ Γ (EBox (Lam e)) (MPoly nv cs T σ V) [] (EBox (Lam e'))
  | m_let Γ Γ1 Γ2 e1 e2 e1' e2' T V ef1 ef2 :                (* T-Let *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 T ef1 e1' →
      mtyped Θ (Some T :: Γ2) e2 V ef2 e2' →
      plt Θ ef1 (envp Γ2) →
      mtyped Θ Γ (App (Lam e2) e1) V (ef1 ++ ef2) (App (Lam e2') e1')
  | m_letu Γ Γ1 Γ2 e1 e2 e1' e2' V ef1 ef2 :                 (* e₁; e₂ *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 MUnit ef1 e1' →
      mtyped Θ Γ2 e2 V ef2 e2' →
      plt Θ ef1 (envp Γ2) →
      mtyped Θ Γ (LetU e1 e2) V (ef1 ++ ef2) (LetU (App EForce e1') e2')
  | m_new Γ e e' Q n d V ef :                                (* T-New, T-NewPoly *)
      mwf Q → pfin n →
      mtyped Θ (Some (MChan true Q n d) :: Some (MChan false Q n d) :: Γ) e V ef e' →
      mtyped Θ Γ (LetP (App ENew EUnit) e) V ef (let_new_pair e')
  | m_send Γ Γ1 Γ2 e1 e2 e1' e2' pol Q h d a P K ef1 ef2 :   (* send, R1, R3 *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 (payty P) ef1 e1' →
      mtyped Θ Γ2 e2 (MChan pol Q h d) ef2 e2' →
      mview pol (mhd Q h d).1 = ASnd a P K → mwf Q → pfin a →
      plt Θ ef1 (envp Γ2) → plt Θ ef2 (tprios (payty P)) →
      plt Θ [a] (tprios (payty P)) → plt Θ [a] [chead K (mhd Q h d).2 d] →
      mtyped Θ Γ (App ESend (Pair e1 e2)) (MChan pol K (mhd Q h d).2 d) (ef1 ++ ef2 ++ [a])
        (App ESend (Pair e1' e2'))
  | m_recv Γ Γ1 Γ2 e e2 e' e2' pol Q h d a P K V ef1 ef2 :   (* receive, T-LetPair *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e (MChan pol Q h d) ef1 e' →
      mview pol (mhd Q h d).1 = ARcv a P K → mwf Q → pfin a →
      mtyped Θ (Some (MChan pol K (mhd Q h d).2 d) :: Some (payty P) :: Γ2) e2 V ef2 e2' →
      plt Θ (ef1 ++ [a]) (envp Γ2) →
      plt Θ [a] (tprios (payty P)) → plt Θ [a] [chead K (mhd Q h d).2 d] →
      mtyped Θ Γ (LetP (App ERecv e) e2) V (ef1 ++ [a] ++ ef2) (LetP (App ERecv e') e2')
  | m_close Γ e e' pol Q h d a ef :                          (* close, wait *)
      mtyped Θ Γ e (MChan pol Q h d) ef e' →
      mview pol (mhd Q h d).1 = AEnd a → mwf Q → pfin a →
      mtyped Θ Γ (App EClos e) MUnit (ef ++ [a]) (LetU (App EClos e') unitv)
  | m_sel1 Γ e e' pol Q h d a K1 K2 ef :                     (* T-Sel *)
      mtyped Θ Γ e (MChan pol Q h d) ef e' →
      mview pol (mhd Q h d).1 = ASel a K1 K2 → mwf Q → pfin a →
      plt Θ [a] [chead K1 (mhd Q h d).2 d; chead K2 (mhd Q h d).2 d] →
      mtyped Θ Γ (App ESel1 e) (MChan pol K1 (mhd Q h d).2 d) (ef ++ [a]) (App ESel1 e')
  | m_sel2 Γ e e' pol Q h d a K1 K2 ef :
      mtyped Θ Γ e (MChan pol Q h d) ef e' →
      mview pol (mhd Q h d).1 = ASel a K1 K2 → mwf Q → pfin a →
      plt Θ [a] [chead K1 (mhd Q h d).2 d; chead K2 (mhd Q h d).2 d] →
      mtyped Θ Γ (App ESel2 e) (MChan pol K2 (mhd Q h d).2 d) (ef ++ [a]) (App ESel2 e')
  | m_match Γ Γ1 Γ2 e e1 e2 e' e1' e2' pol Q h d a K1 K2 V ef1 ef2 : (* T-Match, R6 *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e (MChan pol Q h d) ef1 e' →
      mview pol (mhd Q h d).1 = ABra a K1 K2 → mwf Q → pfin a →
      mtyped Θ (Some (MChan pol K1 (mhd Q h d).2 d) :: Γ2) e1 V ef2 e1' →
      mtyped Θ (Some (MChan pol K2 (mhd Q h d).2 d) :: Γ2) e2 V ef2 e2' →
      plt Θ (ef1 ++ [a]) (envp Γ2) →
      plt Θ [a] [chead K1 (mhd Q h d).2 d; chead K2 (mhd Q h d).2 d] →
      mtyped Θ Γ (Case (App EBra e) e1 e2) V (ef1 ++ [a] ++ ef2) (Case (App EBra e') e1' e2')
  | m_fork Γ e e' lo σ ef :                                  (* fork, R2 *)
      mtyped Θ Γ e (MArr MUnit lo σ MUnit) ef e' →
      mtyped Θ Γ (App ESpawn e) MUnit ef (App fork_tr e')
  | m_inst Γ e e' pol S0 h d ef :                            (* T-Inst, R5 *)
      mtyped Θ Γ e (MChan pol (MRec S0) h d) ef e' → rbody S0 → mact S0 →
      mtyped Θ Γ e (MChan pol (munf S0 h) (padd h d) d) ef e'
  | m_fold Γ e e' pol S0 h d ef :                            (* T-Eq *)
      mtyped Θ Γ e (MChan pol (munf S0 h) (padd h d) d) ef e' → rbody S0 → mact S0 →
      mtyped Θ Γ e (MChan pol (MRec S0) h d) ef e'
  | m_sub Γ e e' T ef ef' :                                  (* a larger effect *)
      mtyped Θ Γ e T ef e' → hle Θ ef ef' →
      mtyped Θ Γ e T ef' e'.
