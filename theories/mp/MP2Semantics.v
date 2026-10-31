(** * The operational semantics of Mordido and Pérez, version 2

    Fig. 15 (pdf p. 30) and Definition 1 (p. 16) of Mordido and Pérez,
    on the source terms of [mtyped] (MP2Typing.v), with repairs R4 and
    R5. The translation e′ runs in lang/Semantics.v, and
    MP2Simulation.v relates the two.

    Deviations, listed in docs/extensions/adequacy/mordido-perez.md,
    section 14.

    - Processes are flat, a set C of restricted names and a multiset of
      threads, as in lang/Semantics.v. Scope extrusion and the other
      rules of ≡ bring every closed configuration into this form.
    - Both ends of a channel carry one name, as in lang/Semantics.v.
      let (x, y) = new S in e is [LetP (App ENew EUnit) e]. R-New and
      R-NewPoly are one rule. The sequence of R-NewPoly lives in the
      types and has no run-time trace.
    - Type and priority applications are erased. R4 makes recursion
      rec f. Λιs αs. λx.e, which is [EBox (Lam e)], with the β rule
      (rec f. λx.e) v → e[v/x][rec f. λx.e/f]. R5 erases inst.
    - match y with {ℓ → eℓ} is [Case (App EBra y) e1 e2], and R-Ch
      substitutes the channel into the chosen branch in one step.
    - R-Close drops the restriction of the closed name. Fig. 15 keeps it
      and ≡ removes it once no thread mentions the name. A name closes
      once, so a program that closes a name twice gets stuck here.
    - R-Com and R-Ch fire on every name, restricted or not. In Fig. 15
      a thread that mentions a name always runs under its restriction,
      because ≡ drops a restriction only when no thread mentions it.
    - The fresh name of new is fresh for the whole process. *)

From stdpp Require Import base gmap gmultiset relations.
From LRGV Require Export lang.Syntax.

(** ** Labels

    β for the expression steps, the fresh name of new, the value of
    fork, and the halves of R-Com, R-Ch and R-Close. *)

Inductive slab :=
  | SBeta
  | SNew (a : chan)
  | SSpawn (v : expr)
  | SOut (a : chan) (v : expr)
  | SIn (a : chan) (v : expr)
  | SSl (a : chan) (b : bool)
  | SBr (a : chan) (b : bool)
  | SCl (a : chan).

(** ** Head steps (Fig. 15)

    E-App and E-LetElim ([m_let] is an application), the β of R4,
    E-UnitElim and E-PairElim, then the redexes of R-New, R-Fork,
    R-Com, R-Ch and R-Close. *)

Inductive src_head : expr → slab → expr → Prop :=
  | SHApp e v :
      is_val v → src_head (App (Lam e) v) SBeta (subst1 v e)
  | SHFix e v :
      is_val v → src_head (App (EBox (Lam e)) v) SBeta (subst (v .: EBox (Lam e) .: Var) e)
  | SHLetU e :
      src_head (LetU EUnit e) SBeta e
  | SHLetP u v e :
      is_val u → is_val v → src_head (LetP (Pair u v) e) SBeta (subst2 u v e)
  | SHNew a :
      src_head (App ENew EUnit) (SNew a) (Pair (Chan a) (Chan a))
  | SHSpawn v :
      is_val v → src_head (App ESpawn v) (SSpawn v) EUnit
  | SHSend a v :
      is_val v → src_head (App ESend (Pair v (Chan a))) (SOut a v) (Chan a)
  | SHRecv a v :
      is_val v → src_head (App ERecv (Chan a)) (SIn a v) (Pair v (Chan a))
  | SHSel a (b : bool) :
      src_head (App (if b then ESel2 else ESel1) (Chan a)) (SSl a b) (Chan a)
  | SHBra a (b : bool) e1 e2 :
      src_head (Case (App EBra (Chan a)) e1 e2) (SBr a b) (subst1 (Chan a) (if b then e2 else e1))
  | SHClose a :
      src_head (App EClos (Chan a)) (SCl a) EUnit.

(** ** Evaluation contexts (Fig. 15)

    E ::= [ ] | E e | v E | (E, e) | (v, E) | E; e | let (x, y) = E in e
        | match E with {…}. let x = E in e is v E with v a λ. *)

Inductive src_step : expr → slab → expr → Prop :=
  | SSHead e α e' :
      src_head e α e' → src_step e α e'
  | SSAppL e1 α e1' e2 :
      src_step e1 α e1' → src_step (App e1 e2) α (App e1' e2)
  | SSAppR v e2 α e2' :
      is_val v → src_step e2 α e2' → src_step (App v e2) α (App v e2')
  | SSPairL e1 α e1' e2 :
      src_step e1 α e1' → src_step (Pair e1 e2) α (Pair e1' e2)
  | SSPairR v e2 α e2' :
      is_val v → src_step e2 α e2' → src_step (Pair v e2) α (Pair v e2')
  | SSLetU e1 α e1' e2 :
      src_step e1 α e1' → src_step (LetU e1 e2) α (LetU e1' e2)
  | SSLetP e1 α e1' e2 :
      src_step e1 α e1' → src_step (LetP e1 e2) α (LetP e1' e2)
  | SSCase e α e' e1 e2 :
      src_step e α e' → src_step (Case e e1 e2) α (Case e' e1 e2).

(** ** Configurations (Fig. 15)

    R-LiftE, R-New with R-NewPoly, R-Fork, R-Com, R-Ch and R-Close on
    flat processes. R-Par, R-Bind and R-Cong are the flat form. *)

Inductive src_pstep : proc → proc → Prop :=
  | SPBeta C E e e' :
      src_step e SBeta e' →
      src_pstep (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]})
  | SPNew C E e a e' :
      src_step e (SNew a) e' →
      a ∉ C → a ∉ echans E → a ∉ fchans e →
      src_pstep (C, E ⊎ {[+ e +]}) (C ∪ {[a]}, E ⊎ {[+ e' +]})
  | SPSpawn C E e v e' :
      src_step e (SSpawn v) e' →
      src_pstep (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]})
  | SPCom C E a v e e' f f' :
      src_step e (SOut a v) e' → src_step f (SIn a v) f' →
      src_pstep (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | SPCh C E a b e e' f f' :
      src_step e (SSl a b) e' → src_step f (SBr a b) f' →
      src_pstep (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | SPClose C E a e e' f f' :
      src_step e (SCl a) e' → src_step f (SCl a) f' → a ∈ C →
      src_pstep (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (C ∖ {[a]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]}).

Definition src_irred (p : proc) : Prop := ∀ q, ¬ src_pstep p q.

(** C ≡ •⟨v⟩. The child threads are () and drop by C ≡ ◦⟨()⟩ ∥ C, no
    restriction is left, and the main thread is a value. Definition 1
    also asks |T| = ⊤ for the type T of v. We do not track types along
    reduction, so we only show that the main thread is a value. *)
Definition src_final (p : proc) : Prop :=
  p.1 = ∅ ∧ ∃ v E, p.2 = {[+ v +]} ⊎ E ∧ is_val v ∧ ∀ e, e ∈ E → e = EUnit.

(** Definition 1 (p. 16) for the closed program •⟨e⟩. C →* C′ ↛
    implies C′ ≡ •⟨v⟩. *)
Definition mp_deadlock_free_src (e : expr) : Prop :=
  ∀ q, rtc src_pstep (∅, {[+ e +]}) q → src_irred q → src_final q.

(** ** Basic facts *)

Lemma src_head_not_val e α e' : src_head e α e' → is_val e = false.
Proof. by destruct 1. Qed.

Lemma src_step_not_val e α e' : src_step e α e' → is_val e = false.
Proof.
  induction 1 as [e α e' H| | | e1 α e1' e2 H IH|v e2 α e2' Hv H IH| | |].
  - by eapply src_head_not_val.
  - done.
  - done.
  - simpl. by rewrite IH.
  - simpl. rewrite IH. by destruct (is_val v).
  - done.
  - done.
  - done.
Qed.

Lemma src_val_no_step v α e : is_val v → src_step v α e → False.
Proof. intros Hv H. apply src_step_not_val in H. by rewrite H in Hv. Qed.

Ltac src_ind H := induction H as [? ? ? Hh| | | | | | |].

(** The fresh name of new can be any name. *)
Lemma src_step_new_any e a e' :
  src_step e (SNew a) e' → ∀ b, ∃ e'', src_step e (SNew b) e''.
Proof.
  remember (SNew a) as α eqn:Hα. intros H. revert Hα.
  induction H as [e α e' H| | | | | | |]; intros -> b;
    try (destruct (IHsrc_step eq_refl b) as [? ?]; eexists; by econstructor).
  inversion H; subst. eexists. by apply SSHead, SHNew.
Qed.

(** A receive accepts any value. *)
Lemma src_step_recv_any e a v e' :
  src_step e (SIn a v) e' → ∀ w, is_val w → ∃ e'', src_step e (SIn a w) e''.
Proof.
  remember (SIn a v) as α eqn:Hα. intros H. revert Hα.
  induction H as [e α e' H| | | | | | |]; intros -> w Hw;
    try (destruct (IHsrc_step eq_refl w Hw) as [? ?]; eexists; by econstructor).
  inversion H; subst. eexists. by apply SSHead, SHRecv.
Qed.

(** A match accepts either label. *)
Lemma src_step_bra_any e a b e' :
  src_step e (SBr a b) e' → ∀ b', ∃ e'', src_step e (SBr a b') e''.
Proof.
  remember (SBr a b) as α eqn:Hα. intros H. revert Hα.
  induction H as [e α e' H| | | | | | |]; intros -> b';
    try (destruct (IHsrc_step eq_refl b') as [? ?]; eexists; by econstructor).
  inversion H; subst. eexists. by apply SSHead, SHBra.
Qed.

Lemma src_step_send_val e a v e' : src_step e (SOut a v) e' → is_val v.
Proof.
  remember (SOut a v) as α eqn:Hα. intros H. revert Hα.
  induction H as [e α e' H| | | | | | |]; intros ->; auto.
  by inversion H; subst.
Qed.
