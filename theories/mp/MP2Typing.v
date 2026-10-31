(** * Typing of Mordido and Pérez on our terms, version 2

    Figs. 5, 6, 13 and 14 (pp. 11, 12, 25, 26) of Mordido and Pérez with
    repairs R1 to R6, context-free session types, session type
    variables and functions over unbounded segments
    (docs/extensions/adequacy/mordido-perez.md, sections 12 and 13). A
    derivation Θ | Γ ⊢ e : T ⋄ σs also yields the term e′ of the static
    system it translates to, so the judgment is [mtyped Θ Γ e T σs e′].

    Source terms are the terms of lang/Syntax.v as in version 1. Two
    rules are new.

    - rec f. Λαs. λx.e over a segment ([m_fixseg]) types e under any
      valuation, with x at an abstract position.
    - f[τs] e for such an f ([m_appseg]) returns the channel at a later
      end point, [MEx]. Opening it ([m_open]) gives a channel at an
      abstract position, and an action there has effect ⊤, the latent
      effect after receiveTree (p. 21).

    Priority comparisons hold at every valuation of the priority and
    session type variables that the predicate of Θ admits. T-Eq asks the
    erasures to be equivalent at every instance and the two channel
    points to be equivalent at every valuation. *)

From stdpp Require Import base list numbers.
From LRGV Require Export lang.Syntax mp.MP2World.

(** ** Comparisons *)

(** max σs < min ls at every valuation. *)
Definition plt (Θ : pctx) (ef : list prio) (lo : list lbi) : Prop :=
  ef = [] ∨ ∀ v ts, models Θ v ts → ∀ l, l ∈ lo → xlt (xmaxl v ef) (evlb v ts l).

(** σs ≤ σs′ for a latent effect. *)
Definition hle (Θ : pctx) (ef ef' : list prio) : Prop :=
  ef = [] ∨ PTop ∈ ef' ∨ (∃ l1 l2, ef' = l1 ++ ef ++ l2) ∨
  (ef' ≠ [] ∧ ∀ v ts, models Θ v ts → xlt (xmaxl v ef) (xmaxl v ef')).

(** The effect is not ⊤. *)
Definition pntop (Θ : pctx) (ef : list prio) : Prop :=
  ∀ v ts, models Θ v ts → xlt (xmaxl v ef) XT.

(** ** Scoping of session types

    The session type variables lie below k, outside the body of a µ.
    A body has no µ and no session type variable, and its payloads are
    closed (F-PAbsS, p. 22, forms ∀^S under an empty Θ). *)

Fixpoint rclosed (Q : msty) : Prop :=
  match Q with
  | MSkip | MEnd _ _ => True
  | MSeq A B | MSel _ A B | MBra _ A B => rclosed A ∧ rclosed B
  | MSnd _ P | MRcv _ P => match P with MPUnit => True | MPChan _ Q _ _ => rclosed Q end
  | MRec _ | MVar | MTV _ => False
  end.

Fixpoint rbody (Q : msty) : Prop :=
  match Q with
  | MSkip | MEnd _ _ | MVar => True
  | MSeq A B | MSel _ A B | MBra _ A B => rbody A ∧ rbody B
  | MSnd _ P | MRcv _ P => match P with MPUnit => True | MPChan _ Q _ _ => rclosed Q end
  | MRec _ | MTV _ => False
  end.

Fixpoint msc (k : nat) (Q : msty) : Prop :=
  match Q with
  | MSkip | MEnd _ _ => True
  | MSeq A B | MSel _ A B | MBra _ A B => msc k A ∧ msc k B
  | MSnd _ P | MRcv _ P => match P with MPUnit => True | MPChan _ Q _ _ => msc k Q end
  | MRec S0 => rbody S0
  | MVar => False
  | MTV j => j < k
  end.

(** A type that a priority abstraction may take or return: scoped, no
    abstract position and no unopened segment result. *)
Fixpoint tpure (k : nat) (T : mty) : Prop :=
  match T with
  | MUnit => True
  | MPoly Θ' T _ V => tpure (pc_nt Θ') T ∧ tpure (pc_nt Θ') V
  | MSeg _ k' Qa Qr => msc k' Qa ∧ msc k' Qr
  | MCh _ Q (PR _ _) => msc k Q
  | MCh _ _ (PX _ _) | MEx _ _ => False
  | MArr T lo _ V => tpure k T ∧ tpure k V ∧ Forall (λ l, match l with LC Q _ _ => msc k Q | _ => True end) lo
  end.

(** The instances of the session type variables are hereditarily
    contractive at every instance of the caller's own. *)
Definition hcinst (Θ : pctx) (τ : list msty) : Prop :=
  ∀ ss, length ss = pc_nt Θ → Forall hcontractive ss →
    Forall (λ q, hcontractive (sinst (slist ss) (ers q))) τ.

(** σs, τs instantiate Θ′ under Θ (T-PApp, T-TApp). *)
Definition pinst_ok (Θ Θ' : pctx) (σ : list prio) (τ : list msty) : Prop :=
  length σ = pc_nv Θ' ∧ length τ = pc_nt Θ' ∧ Forall pfin σ ∧ Forall (msc (pc_nt Θ)) τ ∧
  hcinst Θ τ ∧ ∀ v ts, models Θ v ts → models Θ' (evalZ v <$> σ) (mclose v ts <$> τ).

(** T-Eq: equivalent erasures at every instance, and the same point at
    every valuation, or the same abstract position. *)
Definition pos_eq (Θ : pctx) (Q : msty) (p : mpos) (Q' : msty) (p' : mpos) : Prop :=
  match p, p' with
  | PR h d, PR h' d' =>
      d = d' ∧ ∀ v ts, models Θ v ts → oeq (DCh (mclose v ts Q) (pclose v h) d) (DCh (mclose v ts Q') (pclose v h') d)
  | PX n w, PX n' w' => n = n' ∧ w = w'
  | _, _ => False
  end.

Definition meq_ok (Θ : pctx) (Q : msty) (p : mpos) (Q' : msty) (p' : mpos) : Prop :=
  (∀ ss, length ss = pc_nt Θ → Forall hcontractive ss →
     seq (sinst (slist ss) (ers Q)) (sinst (slist ss) (ers Q'))) ∧ pos_eq Θ Q p Q' p'.

(** ** Actions at a position

    At a sequence the action has its priority, the payload lies above
    it and the continuation rises (R1, R3). At an abstract position the
    action has effect ⊤ and sends only unit. *)

Definition sndQ (pol : bool) (a : prio) (P : mpay) (K : msty) : msty :=
  MSeq (if pol then MRcv a P else MSnd a P) K.
Definition rcvQ (pol : bool) (a : prio) (P : mpay) (K : msty) : msty :=
  MSeq (if pol then MSnd a P else MRcv a P) K.
Definition selQ (pol : bool) (a : prio) (K1 K2 : msty) : msty :=
  if pol then MBra a K1 K2 else MSel a K1 K2.
Definition braQ (pol : bool) (a : prio) (K1 K2 : msty) : msty :=
  if pol then MSel a K1 K2 else MBra a K1 K2.

Definition aeff (p : mpos) (a : prio) : prio := match p with PR _ _ => a | PX _ _ => PTop end.
Definition pnext (p : mpos) : mpos := match p with PR h d => PR h d | PX n w => PX n (w ++ [WS]) end.
Definition pbr (p : mpos) (b : bool) : mpos := match p with PR h d => PR h d | PX n w => PX n (w ++ [WB b]) end.

Definition rpayty (p : mpos) (P : mpay) : mty :=
  match p, P with PX n w, MPChan pp Qp _ _ => MCh pp Qp (PX n (w ++ [WL 0])) | _, _ => payty P end.

Definition snd_ok (Θ : pctx) (p : mpos) (a : prio) (P : mpay) (K : msty) : Prop :=
  match p with
  | PR h d => pfin a ∧ plt Θ [a] (tprios (payty P)) ∧ plt Θ [a] [LC K h d]
  | PX _ _ => P = MPUnit
  end.

Definition rcv_ok (Θ : pctx) (p : mpos) (a : prio) (P : mpay) (K : msty) : Prop :=
  match p with
  | PR h d => pfin a ∧ plt Θ [a] (tprios (payty P)) ∧ plt Θ [a] [LC K h d]
  | PX _ _ => True
  end.

Definition br_ok (Θ : pctx) (p : mpos) (a : prio) (K1 K2 : msty) : Prop :=
  match p with
  | PR h d => pfin a ∧ plt Θ [a] [LC K1 h d; LC K2 h d]
  | PX _ _ => True
  end.

Definition end_ok (p : mpos) (a : prio) : Prop := match p with PR _ _ => pfin a | PX _ _ => True end.

(** ** Environments *)

Definition menv := list (option mty).

Definition menv_un (Γ : menv) : Prop := ∀ t, Some t ∈ Γ → mun t.

Definition menv_only_un (Γ : menv) (x : nat) (t : mty) : Prop :=
  Γ !! x = Some (Some t) ∧ ∀ y t', y ≠ x → Γ !! y = Some (Some t') → mun t'.

Inductive msplit : menv → menv → menv → Prop :=
  | ms_nil : msplit [] [] []
  | ms_none Γ Γ1 Γ2 : msplit Γ Γ1 Γ2 → msplit (None :: Γ) (None :: Γ1) (None :: Γ2)
  | ms_l t Γ Γ1 Γ2 : msplit Γ Γ1 Γ2 → msplit (Some t :: Γ) (Some t :: Γ1) (None :: Γ2)
  | ms_r t Γ Γ1 Γ2 : msplit Γ Γ1 Γ2 → msplit (Some t :: Γ) (None :: Γ1) (Some t :: Γ2)
  | ms_un t Γ Γ1 Γ2 : mun t → msplit Γ Γ1 Γ2 → msplit (Some t :: Γ) (Some t :: Γ1) (Some t :: Γ2).

Fixpoint envp (Γ : menv) : list lbi :=
  match Γ with
  | [] => []
  | None :: Γ => envp Γ
  | Some t :: Γ => tprios t ++ envp Γ
  end.

Fixpoint menames (Γ : menv) : list nat :=
  match Γ with
  | [] => []
  | None :: Γ => menames Γ
  | Some t :: Γ => tnames t ++ menames Γ
  end.

(** An abstraction captures only units and abstractions. *)
Definition menv_poly (Γ : menv) : Prop := ∀ t, Some t ∈ Γ → mun t ∧ tpure 0 t.

(** ** Terms of the translation *)

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
      mtyped Θ (Some T :: Γ) e V ef e' →
      mtyped Θ Γ (Lam e) (MArr T (envp Γ) ef V) [] (Lam e')
  | m_app Γ Γ1 Γ2 e1 e2 e1' e2' T lo σ V ef1 ef2 :           (* T-App *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 (MArr T lo σ V) ef1 e1' →
      mtyped Θ Γ2 e2 T ef2 e2' →
      plt Θ ef1 (envp Γ2) → plt Θ ef2 lo →
      mtyped Θ Γ (App e1 e2) V (ef1 ++ ef2 ++ σ) (App e1' e2')
  | m_app_poly Γ Γ1 Γ2 e1 e2 e1' e2' Θ' T σ V ef1 ef2 σs τs : (* T-PApp, T-TApp, T-App *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 (MPoly Θ' T σ V) ef1 e1' →
      pinst_ok Θ Θ' σs τs → tpure (pc_nt Θ') T → tpure (pc_nt Θ') V →
      mtyped Θ Γ2 e2 (msub σs τs T) ef2 e2' →
      plt Θ ef1 (envp Γ2) → pntop Θ ef2 →
      mtyped Θ Γ (App e1 e2) (msub σs τs V) (ef1 ++ ef2 ++ (psub σs <$> σ))
        (App (App EForce e1') e2')
  | m_fix Γ e e' Θ' T σ V ef :                              (* R4, T-PAbs, T-TAbs, T-AbsUn *)
      menv_poly Γ → tpure (pc_nt Θ') T → tpure (pc_nt Θ') V → (∃ v ts, pc_ok Θ' v ts) →
      mtyped Θ' (Some T :: Some (MPoly Θ' T σ V) :: Γ) e V ef e' →
      hle Θ' ef σ →
      mtyped Θ Γ (EBox (Lam e)) (MPoly Θ' T σ V) [] (EBox (Lam e'))
  | m_fixseg Γ e e' pol k Qa Qr ef :                        (* a function over a segment *)
      menv_poly Γ → msc k Qa → msc k Qr →
      mtyped (Θany k) (Some (MCh pol Qa (PX 0 [])) :: Some (MSeg pol k Qa Qr) :: Γ) e (MEx pol Qr) ef e' →
      mtyped Θ Γ (EBox (Lam e)) (MSeg pol k Qa Qr) [] (EBox (Lam e'))
  | m_appseg Γ Γ1 Γ2 e1 e2 e1' e2' pol k Qa Qr τs p ef1 ef2 : (* T-TApp, T-App at a segment *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 (MSeg pol k Qa Qr) ef1 e1' →
      length τs = k → Forall (msc (pc_nt Θ)) τs → hcinst Θ τs → msc k Qa → msc k Qr →
      mtyped Θ Γ2 e2 (MCh pol (tsub τs Qa) p) ef2 e2' →
      plt Θ ef1 (envp Γ2) → pntop Θ ef2 →
      mtyped Θ Γ (App e1 e2) (MEx pol (tsub τs Qr)) (ef1 ++ ef2 ++ [PTop])
        (App (App EForce e1') e2')
  | m_open Γ e e' i pol Q n V ef :                           (* the end point of a segment *)
      Γ !! i = Some (Some (MEx pol Q)) → n ∉ menames Γ → n ∉ tnames V →
      mtyped Θ (<[i := Some (MCh pol Q (PX n []))]> Γ) e V ef e' →
      mtyped Θ Γ e V ef e'
  | m_pack Γ e e' pol Q p ef :                               (* a later end point *)
      mtyped Θ Γ e (MCh pol Q p) ef e' →
      mtyped Θ Γ e (MEx pol Q) ef e'
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
      mtyped Θ (Some (MCh true Q (PR n d)) :: Some (MCh false Q (PR n d)) :: Γ) e V ef e' →
      mtyped Θ Γ (LetP (App ENew EUnit) e) V ef (LetP (App ENew EUnit) e')
  | m_send Γ Γ1 Γ2 e1 e2 e1' e2' pol a P K p ef1 ef2 :       (* send, R1, R3 *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e1 (payty P) ef1 e1' →
      mtyped Θ Γ2 e2 (MCh pol (sndQ pol a P K) p) ef2 e2' →
      snd_ok Θ p a P K →
      plt Θ ef1 (envp Γ2) → plt Θ ef2 (tprios (payty P)) →
      mtyped Θ Γ (App ESend (Pair e1 e2)) (MCh pol K (pnext p)) (ef1 ++ ef2 ++ [aeff p a])
        (App ESend (Pair e1' e2'))
  | m_recv Γ Γ1 Γ2 e e2 e' e2' pol a P K p V ef1 ef2 :       (* receive, T-LetPair *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e (MCh pol (rcvQ pol a P K) p) ef1 e' →
      rcv_ok Θ p a P K →
      mtyped Θ (Some (MCh pol K (pnext p)) :: Some (rpayty p P) :: Γ2) e2 V ef2 e2' →
      plt Θ (ef1 ++ [aeff p a]) (envp Γ2) →
      mtyped Θ Γ (LetP (App ERecv e) e2) V (ef1 ++ [aeff p a] ++ ef2) (LetP (App ERecv e') e2')
  | m_close Γ e e' pol a w p ef :                            (* close, wait *)
      mtyped Θ Γ e (MCh pol (MEnd a w) p) ef e' → end_ok p a →
      mtyped Θ Γ (App EClos e) MUnit (ef ++ [aeff p a]) (LetU (App EClos e') unitv)
  | m_sel Γ e e' pol a K1 K2 p ef (b : bool) :              (* T-Sel *)
      mtyped Θ Γ e (MCh pol (selQ pol a K1 K2) p) ef e' → br_ok Θ p a K1 K2 →
      mtyped Θ Γ (App (if b then ESel2 else ESel1) e) (MCh pol (if b then K2 else K1) (pbr p b))
        (ef ++ [aeff p a]) (App (if b then ESel2 else ESel1) e')
  | m_match Γ Γ1 Γ2 e e1 e2 e' e1' e2' pol a K1 K2 p V ef1 ef2 : (* T-Match, R6 *)
      msplit Γ Γ1 Γ2 →
      mtyped Θ Γ1 e (MCh pol (braQ pol a K1 K2) p) ef1 e' → br_ok Θ p a K1 K2 →
      mtyped Θ (Some (MCh pol K1 (pbr p false)) :: Γ2) e1 V ef2 e1' →
      mtyped Θ (Some (MCh pol K2 (pbr p true)) :: Γ2) e2 V ef2 e2' →
      plt Θ (ef1 ++ [aeff p a]) (envp Γ2) →
      mtyped Θ Γ (Case (App EBra e) e1 e2) V (ef1 ++ [aeff p a] ++ ef2) (Case (App EBra e') e1' e2')
  | m_fork Γ e e' lo σ ef :                                  (* fork, R2 *)
      mtyped Θ Γ e (MArr MUnit lo σ MUnit) ef e' →
      mtyped Θ Γ (App ESpawn e) MUnit ef (App fork_tr e')
  | m_eq Γ e e' pol Q Q' p p' ef :                           (* T-Eq, T-Inst, R5 *)
      mtyped Θ Γ e (MCh pol Q p) ef e' → meq_ok Θ Q p Q' p' →
      mtyped Θ Γ e (MCh pol Q' p') ef e'
  | m_sub Γ e e' T ef ef' :                                  (* a larger effect *)
      mtyped Θ Γ e T ef e' → hle Θ ef ef' →
      mtyped Θ Γ e T ef' e'.
