(** * The operational semantics of Padovani and Novara

    Table 1 (pdf p. 5) and Definition 1 (p. 14) of Padovani and Novara,
    FORTE 2015, on the source syntax of [pn_typed] (PNTyping.v). This is
    the semantics the source program e runs in. The translation e′ runs
    in lang/Semantics.v, and PNSimulation.v relates the two.

    Every deviation from the paper is listed in
    docs/extensions/adequacy/padovani-novara.md §8. In short.

    - Processes are flat, a set C of restricted names and a multiset of
      threads, as in lang/Semantics.v. The standard rules of ≡ bring
      every process (νa₁)…(νaₙ)(⟨e₁⟩ | … | ⟨eₖ⟩) into this form.
    - let a = new() in e is [LetP (App ENew EUnit) e]. new() steps to the
      pair (a, a) of the one fresh name, and the let binds both ends.
    - Sums add the contexts inj₁ E, inj₂ E and case E of …, and their β.
    - The fresh name of new is fresh for the whole process, not only for
      the thread (a ∉ fn(E) on p. 5), which α-renaming of bound names
      allows.
    - wrap and unwrap are erased, so unwrap (wrap v) → v is no step. *)

From stdpp Require Import base gmap gmultiset relations.
From LRGV Require Export pn.PNTyping.

(** ** Values (p. 5)

    v ::= k | a | λx.e | send v, plus () among the constants, injections
    of values and the pair (a, a) that new() returns. fix λf.e ([EBox])
    is no value, because fix λf.e reduces. *)

Fixpoint is_sval (e : expr) : bool :=
  match e with
  | EUnit | Konst _ | Chan _ | Lam _ => true
  | App (Konst KSend) v => is_sval v
  | Pair e1 e2 => is_sval e1 && is_sval e2
  | Inj1 e | Inj2 e => is_sval e
  | _ => false
  end.

(** ** Labels

    β for the expression steps, the fresh name of new, the thunk of fork,
    and the two halves of a communication. *)

Inductive slab :=
  | SBeta
  | SNew (a : chan)
  | SSpawn (v : expr)
  | SOut (a : chan) (v : expr)
  | SIn (a : chan) (v : expr).

(** ** Head steps (p. 5)

    (λx.e) v → e{v/x} and fix λx.e → e{fix λx.e/x}. The rest are the
    redexes of the four process rules of Table 1, and the β of let and
    case. *)

Inductive src_head : expr → slab → expr → Prop :=
  | SHApp e v :
      is_sval v → src_head (App (Lam e) v) SBeta (subst1 v e)
  | SHFix e :
      src_head (EBox e) SBeta (subst1 (EBox e) e)
  | SHLetP u v e :
      is_sval u → is_sval v → src_head (LetP (Pair u v) e) SBeta (subst2 u v e)
  | SHCase1 v e1 e2 :
      is_sval v → src_head (Case (Inj1 v) e1 e2) SBeta (subst1 v e1)
  | SHCase2 v e1 e2 :
      is_sval v → src_head (Case (Inj2 v) e1 e2) SBeta (subst1 v e2)
  | SHNew a :
      src_head (App ENew EUnit) (SNew a) (Pair (Chan a) (Chan a))
  | SHSpawn v :
      is_sval v → src_head (App ESpawn v) (SSpawn v) EUnit
  | SHSend a v :
      is_sval v → src_head (App (App ESend (Chan a)) v) (SOut a v) EUnit
  | SHRecv a v :
      is_sval v → src_head (App ERecv (Chan a)) (SIn a v) v.

(** ** Reduction contexts (p. 5)

    E ::= [ ] | E e | v E, plus inj₁ E, inj₂ E, case E of … and
    let (a, a) = E in e. *)

Inductive src_step : expr → slab → expr → Prop :=
  | SSHead e α e' :
      src_head e α e' → src_step e α e'
  | SSAppL e1 α e1' e2 :
      src_step e1 α e1' → src_step (App e1 e2) α (App e1' e2)
  | SSAppR v e2 α e2' :
      is_sval v → src_step e2 α e2' → src_step (App v e2) α (App v e2')
  | SSInj1 e α e' :
      src_step e α e' → src_step (Inj1 e) α (Inj1 e')
  | SSInj2 e α e' :
      src_step e α e' → src_step (Inj2 e) α (Inj2 e')
  | SSCase e α e' e1 e2 :
      src_step e α e' → src_step (Case e e1 e2) α (Case e' e1 e2)
  | SSLetP e α e' e2 :
      src_step e α e' → src_step (LetP e e2) α (LetP e' e2).

(** ** Processes (Table 1)

    A process is (C, E) as in lang/Semantics.v. The label is [None] for
    τ and [Some a] for a communication on a free name a. A communication
    on a restricted name is τ and removes the restriction, because
    channels are linear (p. 5). *)

Inductive src_pstep : proc → option chan → proc → Prop :=
  | SPBeta C E e e' :
      src_step e SBeta e' →
      src_pstep (C, E ⊎ {[+ e +]}) None (C, E ⊎ {[+ e' +]})
  | SPNew C E e a e' :
      src_step e (SNew a) e' →
      a ∉ C → a ∉ echans E → a ∉ fchans e →
      src_pstep (C, E ⊎ {[+ e +]}) None (C ∪ {[a]}, E ⊎ {[+ e' +]})
  | SPSpawn C E e v e' :
      src_step e (SSpawn v) e' →
      src_pstep (C, E ⊎ {[+ e +]}) None (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]})
  | SPCommRes C E a v e e' f f' :
      src_step e (SOut a v) e' → src_step f (SIn a v) f' → a ∈ C →
      src_pstep (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) None (C ∖ {[a]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | SPCommFree C E a v e e' f f' :
      src_step e (SOut a v) e' → src_step f (SIn a v) f' → a ∉ C →
      src_pstep (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) (Some a) (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]}).

Definition src_tau (p q : proc) : Prop := src_pstep p None q.

(** Q ↛, Q has no reduction with any label. *)
Definition src_irred (p : proc) : Prop := ∀ l q, ¬ src_pstep p l q.

(** Q ≡ ⟨()⟩. ⟨()⟩ is the inert process (p. 5), so a flat process is
    congruent to ⟨()⟩ exactly when every thread is (). *)
Definition src_final (p : proc) : Prop := ∀ e, e ∈ p.2 → e = EUnit.

(** Definition 1 (p. 14) for the closed program ⟨e⟩. P →τ* Q ↛ implies
    Q ≡ ⟨()⟩. *)
Definition pn_deadlock_free_src (e : expr) : Prop :=
  ∀ q, rtc src_tau (∅, {[+ e +]}) q → src_irred q → src_final q.

(** ** Basic facts *)

Lemma src_head_not_val e α e' : src_head e α e' → is_sval e = false.
Proof. by destruct 1. Qed.

Lemma src_step_not_val e α e' : src_step e α e' → is_sval e = false.
Proof.
  induction 1 as [e α e' H|e1 α e1' e2 H IH|v e2 α e2' Hv H IH
                 |e α e' H IH|e α e' H IH|e α e' e1 e2 H IH|e α e' e2 H IH].
  - by eapply src_head_not_val.
  - simpl. destruct e1 as [| | [] | | | | | | | | | |]; try done.
  - simpl. by destruct v as [| | [] | | | | | | | | | |].
  - done.
  - done.
  - done.
  - done.
Qed.

(** The fresh name of new can be any name. *)
Lemma src_step_new_any e a e' :
  src_step e (SNew a) e' → ∀ b, ∃ e'', src_step e (SNew b) e''.
Proof.
  remember (SNew a) as α eqn:Hα. intros H. revert Hα.
  induction H as [e α e' H| | | | | |]; intros -> b.
  - inversion H; subst. eexists. by apply SSHead, SHNew.
  - destruct (IHsrc_step eq_refl b) as [? ?]. eexists. by apply SSAppL.
  - destruct (IHsrc_step eq_refl b) as [? ?]. eexists. by apply SSAppR.
  - destruct (IHsrc_step eq_refl b) as [? ?]. eexists. by apply SSInj1.
  - destruct (IHsrc_step eq_refl b) as [? ?]. eexists. by apply SSInj2.
  - destruct (IHsrc_step eq_refl b) as [? ?]. eexists. by apply SSCase.
  - destruct (IHsrc_step eq_refl b) as [? ?]. eexists. by apply SSLetP.
Qed.

(** A receive accepts any value. *)
Lemma src_step_recv_any e a v e' :
  src_step e (SIn a v) e' → ∀ w, is_sval w → ∃ e'', src_step e (SIn a w) e''.
Proof.
  remember (SIn a v) as α eqn:Hα. intros H. revert Hα.
  induction H as [e α e' H| | | | | |]; intros -> w Hw.
  - inversion H; subst. eexists. by apply SSHead, SHRecv.
  - destruct (IHsrc_step eq_refl w Hw) as [? ?]. eexists. by apply SSAppL.
  - destruct (IHsrc_step eq_refl w Hw) as [? ?]. eexists. by apply SSAppR.
  - destruct (IHsrc_step eq_refl w Hw) as [? ?]. eexists. by apply SSInj1.
  - destruct (IHsrc_step eq_refl w Hw) as [? ?]. eexists. by apply SSInj2.
  - destruct (IHsrc_step eq_refl w Hw) as [? ?]. eexists. by apply SSCase.
  - destruct (IHsrc_step eq_refl w Hw) as [? ?]. eexists. by apply SSLetP.
Qed.

Lemma src_step_send_val e a v e' : src_step e (SOut a v) e' → is_sval v.
Proof.
  remember (SOut a v) as α eqn:Hα. intros H. revert Hα.
  induction H as [e α e' H| | | | | |]; intros ->; auto.
  by inversion H; subst.
Qed.
