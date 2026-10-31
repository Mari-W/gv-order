(** * Types of Mordido and Pérez on our terms, version 2

    A. Mordido and J. A. Pérez, Deadlock-Free Context-Free Session
    Types, LNCS 2026 (arXiv 2506.20356v4), Fig. 1 (p. 6), Fig. 4 and
    Fig. 5 (p. 11). Version 2 of docs/extensions/adequacy/mordido-perez.md,
    section 12, with the restriction log of section 13.

    - A priority is ⊥, ⊤, an integer n, a priority variable ι_j + n of
      the enclosing abstraction, or ι + n for the binder of ∀^S ([PI]).
    - Session types are context free (Fig. 1): Skip, S;S, !^ρ P, ?^ρ P,
      ⊕^ρ(S, S), &^ρ(S, S), Close^ρ and Wait^ρ ([MEnd]), µβ.∀^S ι.S
      ([MRec]), β ([MVar]) and the session type variables of the
      enclosing abstraction ([MTV]). ∀^S without µ is [MRec] whose body
      has no β, µβ.S without ∀^S is [MRec] whose body has no ι.
    - A channel type [MCh pol S p] is S with a position p. A position is
      either a priority sequence [PR h d], the sequence h + k·d of the
      channel (decision D3 of version 1), or an abstract position [PX n w]
      after an unbounded segment, the walk w from the end point n that a
      segment call returned (section 12). [pol] marks the dual end.
    - [MEx pol S] is the result of a segment call, the channel at a later
      end point, and [MSeg pol k Sa Sr] is the type of a function over an
      unbounded segment, ∀αs. Sa →^{⊤,⊤} ∃. Sr.
    - Functional types are unit, channel types, linear arrows
      T →^{ρs,σs} U whose lower bound is the minimum of a list of
      lower-bound items and whose latent effect is the maximum of a list
      of priorities, and priority abstractions ∀ιs αs ∈ Θ. T →^{⊤,σs}_un U
      whose constraint Θ is a predicate on valuations. *)

From stdpp Require Import base countable list numbers.
From LRGV Require Export types.SessionEquiv.

(** ** Priorities *)

Inductive prio := PBot | PTop | PZ (n : Z) | PV (j : nat) (n : Z) | PI (n : Z).

Global Instance prio_eq_dec : EqDecision prio.
Proof. solve_decision. Defined.

(** Extended integers, the values of priorities. *)
Inductive ext := XB | XZ (z : Z) | XT.

Global Instance ext_eq_dec : EqDecision ext.
Proof. solve_decision. Defined.

Definition xlt (a b : ext) : Prop :=
  match a, b with
  | XB, XB => False
  | XB, _ => True
  | XZ z, XZ z' => (z < z')%Z
  | XZ _, XT => True
  | _, _ => False
  end.

Definition xle (a b : ext) : Prop :=
  match a, b with
  | XB, _ => True
  | XZ z, XZ z' => (z ≤ z')%Z
  | _, XT => True
  | _, _ => False
  end.

Definition xmax (a b : ext) : ext :=
  match a, b with
  | XB, x | x, XB => x
  | XT, _ | _, XT => XT
  | XZ z, XZ z' => XZ (Z.max z z')
  end.

Definition xmin (a b : ext) : ext :=
  match a, b with
  | XT, x | x, XT => x
  | XB, _ | _, XB => XB
  | XZ z, XZ z' => XZ (Z.min z z')
  end.

(** A valuation of the priority variables of an abstraction. *)
Abbreviation val := (list Z).

Definition evalp (v : val) (ρ : prio) : ext :=
  match ρ with
  | PBot => XB
  | PTop => XT
  | PZ n | PI n => XZ n
  | PV j n => XZ (default 0%Z (v !! j) + n)
  end.

Definition padd (ρ : prio) (k : Z) : prio :=
  match ρ with
  | PZ n => PZ (n + k)
  | PV j n => PV j (n + k)
  | PI n => PI (n + k)
  | x => x
  end.

Definition pclose (v : val) (ρ : prio) : prio :=
  match ρ with PV j n => PZ (default 0%Z (v !! j) + n) | x => x end.

Definition psub (σ : list prio) (ρ : prio) : prio :=
  match ρ with PV j n => padd (default (PZ 0) (σ !! j)) n | x => x end.

Definition pinI (h : prio) (ρ : prio) : prio :=
  match ρ with PI n => padd h n | x => x end.

Definition xmaxl (v : val) (l : list prio) : ext := foldr (λ ρ a, xmax (evalp v ρ) a) XB l.
Definition xminl (v : val) (l : list prio) : ext := foldr (λ ρ a, xmin (evalp v ρ) a) XT l.

Definition pfin (ρ : prio) : Prop :=
  match ρ with PZ _ | PV _ _ => True | _ => False end.

(** ** Session types *)

Inductive msty :=
  | MSkip
  | MSeq (S1 S2 : msty)
  | MSnd (ρ : prio) (P : mpay)
  | MRcv (ρ : prio) (P : mpay)
  | MSel (ρ : prio) (K1 K2 : msty)
  | MBra (ρ : prio) (K1 K2 : msty)
  | MEnd (ρ : prio) (w : bool)            (* Close^ρ, or Wait^ρ when w *)
  | MRec (Q : msty)                       (* µβ.∀^S ι.Q *)
  | MVar                                  (* β *)
  | MTV (j : nat)                         (* a session type variable *)
with mpay :=
  | MPUnit
  | MPChan (pol : bool) (Q : msty) (h : prio) (d : Z).

Scheme msty_mut := Induction for msty Sort Prop
  with mpay_mut := Induction for mpay Sort Prop.
Combined Scheme msty_mpay_mut from msty_mut, mpay_mut.

Definition prio_enc (ρ : prio) : gen_tree Z :=
  match ρ with
  | PBot => GenNode 0 [] | PTop => GenNode 1 []
  | PZ n => GenNode 2 [GenLeaf n] | PV j n => GenNode 3 [GenLeaf (Z.of_nat j); GenLeaf n]
  | PI n => GenNode 4 [GenLeaf n]
  end.
Definition prio_dec (t : gen_tree Z) : prio :=
  match t with
  | GenNode 1 [] => PTop
  | GenNode 2 [GenLeaf n] => PZ n
  | GenNode 3 [GenLeaf j; GenLeaf n] => PV (Z.to_nat j) n
  | GenNode 4 [GenLeaf n] => PI n
  | _ => PBot
  end.

Lemma prio_dec_enc ρ : prio_dec (prio_enc ρ) = ρ.
Proof. destruct ρ; simpl; try done. by rewrite Nat2Z.id. Qed.

Global Instance prio_countable : Countable prio.
Proof. apply (inj_countable' prio_enc prio_dec). apply prio_dec_enc. Qed.

Definition b_enc (b : bool) : gen_tree Z := GenNode (if b then 1 else 0) [].
Definition b_dec (t : gen_tree Z) : bool := match t with GenNode 1 [] => true | _ => false end.

Fixpoint msty_enc (Q : msty) : gen_tree Z :=
  match Q with
  | MSkip => GenNode 0 []
  | MSeq A B => GenNode 1 [msty_enc A; msty_enc B]
  | MSnd a P => GenNode 2 [prio_enc a; mpay_enc P]
  | MRcv a P => GenNode 3 [prio_enc a; mpay_enc P]
  | MSel a K1 K2 => GenNode 4 [prio_enc a; msty_enc K1; msty_enc K2]
  | MBra a K1 K2 => GenNode 5 [prio_enc a; msty_enc K1; msty_enc K2]
  | MEnd a w => GenNode 6 [prio_enc a; b_enc w]
  | MRec Q => GenNode 7 [msty_enc Q]
  | MVar => GenNode 8 []
  | MTV j => GenNode 9 [GenLeaf (Z.of_nat j)]
  end
with mpay_enc (P : mpay) : gen_tree Z :=
  match P with
  | MPUnit => GenNode 10 []
  | MPChan p Q h d => GenNode 11 [b_enc p; msty_enc Q; prio_enc h; GenLeaf d]
  end.

Fixpoint msty_dec (t : gen_tree Z) : msty :=
  match t with
  | GenNode 1 [A; B] => MSeq (msty_dec A) (msty_dec B)
  | GenNode 2 [a; P] => MSnd (prio_dec a) (mpay_dec P)
  | GenNode 3 [a; P] => MRcv (prio_dec a) (mpay_dec P)
  | GenNode 4 [a; K1; K2] => MSel (prio_dec a) (msty_dec K1) (msty_dec K2)
  | GenNode 5 [a; K1; K2] => MBra (prio_dec a) (msty_dec K1) (msty_dec K2)
  | GenNode 6 [a; w] => MEnd (prio_dec a) (b_dec w)
  | GenNode 7 [Q] => MRec (msty_dec Q)
  | GenNode 8 [] => MVar
  | GenNode 9 [GenLeaf j] => MTV (Z.to_nat j)
  | _ => MSkip
  end
with mpay_dec (t : gen_tree Z) : mpay :=
  match t with
  | GenNode 11 [p; Q; h; GenLeaf d] => MPChan (b_dec p) (msty_dec Q) (prio_dec h) d
  | _ => MPUnit
  end.

Lemma msty_dec_enc : (∀ Q, msty_dec (msty_enc Q) = Q) ∧ (∀ P, mpay_dec (mpay_enc P) = P).
Proof.
  apply msty_mpay_mut; intros; simpl; rewrite ?prio_dec_enc; try congruence.
  - by destruct w.
  - by rewrite Nat2Z.id.
  - destruct pol; simpl; congruence.
Qed.

Global Instance msty_eq_dec : EqDecision msty.
Proof.
  intros S1 S2. destruct (decide (msty_enc S1 = msty_enc S2)) as [E|E].
  - left. rewrite <-(proj1 msty_dec_enc S1), <-(proj1 msty_dec_enc S2). by rewrite E.
  - right. congruence.
Defined.

Global Instance mpay_eq_dec : EqDecision mpay.
Proof.
  intros P1 P2. destruct (decide (mpay_enc P1 = mpay_enc P2)) as [E|E].
  - left. rewrite <-(proj2 msty_dec_enc P1), <-(proj2 msty_dec_enc P2). by rewrite E.
  - right. congruence.
Defined.

Global Instance msty_countable : Countable msty.
Proof. apply (inj_countable' msty_enc msty_dec). apply msty_dec_enc. Qed.

(** ** Operations on session types *)

Fixpoint mmap (f : prio → prio) (Q : msty) : msty :=
  match Q with
  | MSkip => MSkip
  | MSeq A B => MSeq (mmap f A) (mmap f B)
  | MSnd a P => MSnd (f a) (mmapp f P)
  | MRcv a P => MRcv (f a) (mmapp f P)
  | MSel a K1 K2 => MSel (f a) (mmap f K1) (mmap f K2)
  | MBra a K1 K2 => MBra (f a) (mmap f K1) (mmap f K2)
  | MEnd a w => MEnd (f a) w
  | MRec Q => MRec (mmap f Q)
  | MVar => MVar
  | MTV j => MTV j
  end
with mmapp (f : prio → prio) (P : mpay) : mpay :=
  match P with
  | MPUnit => MPUnit
  | MPChan p Q h d => MPChan p (mmap f Q) (f h) d
  end.

(** The session type variables replaced by a list of session types. *)
Fixpoint tsub (τ : list msty) (Q : msty) : msty :=
  match Q with
  | MSkip => MSkip
  | MSeq A B => MSeq (tsub τ A) (tsub τ B)
  | MSnd a P => MSnd a (tsubp τ P)
  | MRcv a P => MRcv a (tsubp τ P)
  | MSel a K1 K2 => MSel a (tsub τ K1) (tsub τ K2)
  | MBra a K1 K2 => MBra a (tsub τ K1) (tsub τ K2)
  | MEnd a w => MEnd a w
  | MRec Q => MRec (tsub τ Q)
  | MVar => MVar
  | MTV j => default (MTV j) (τ !! j)
  end
with tsubp (τ : list msty) (P : mpay) : mpay :=
  match P with
  | MPUnit => MPUnit
  | MPChan p Q h d => MPChan p (tsub τ Q) h d
  end.

(** β replaced by X in a recursive body: the replacement enters neither
    a payload nor a nested µ. *)
Fixpoint msubV (X : msty) (Q : msty) : msty :=
  match Q with
  | MSeq A B => MSeq (msubV X A) (msubV X B)
  | MSel a K1 K2 => MSel a (msubV X K1) (msubV X K2)
  | MBra a K1 K2 => MBra a (msubV X K1) (msubV X K2)
  | MVar => X
  | Q => Q
  end.

(** One unfolding of µβ.∀^S ι.S₀ at the head h of the sequence. *)
Definition munf (S0 : msty) (h : prio) : msty := msubV (MRec S0) (mmap (pinI h) S0).

(** ** Head normal form

    [hdt h d Q] is the head of Q at the head h of the sequence of
    increment d, with the head of the sequence after it. [None] is Skip.
    A continuation is joined like [hseq] of the core joins it. A µ
    unfolds once, and its body is walked by [hdb] under the unfolding,
    so both functions are structural. *)

Inductive mhv :=
  | VSnd (a : prio) (P : mpay) (K : msty)
  | VRcv (a : prio) (P : mpay) (K : msty)
  | VSel (a : prio) (K1 K2 : msty)
  | VBra (a : prio) (K1 K2 : msty)
  | VEnd (a : prio)
  | VTV (j : nat) (K : msty)
  | VNone.

Definition kapp (K B : msty) : msty := match K with MSkip => B | _ => MSeq K B end.

Definition vapp (v : mhv) (B : msty) : mhv :=
  match v with
  | VSnd a P K => VSnd a P (kapp K B)
  | VRcv a P K => VRcv a P (kapp K B)
  | VSel a K1 K2 => VSel a (MSeq K1 B) (MSeq K2 B)
  | VBra a K1 K2 => VBra a (MSeq K1 B) (MSeq K2 B)
  | VTV j K => VTV j (kapp K B)
  | x => x
  end.

Fixpoint hdb (f : prio → prio) (X : msty) (Q : msty) : option mhv :=
  match Q with
  | MSkip => None
  | MSeq A B =>
      match hdb f X A with
      | Some v => Some (vapp v (msubV X (mmap f B)))
      | None => hdb f X B
      end
  | MSnd a P => Some (VSnd (f a) (mmapp f P) MSkip)
  | MRcv a P => Some (VRcv (f a) (mmapp f P) MSkip)
  | MSel a A B => Some (VSel (f a) (msubV X (mmap f A)) (msubV X (mmap f B)))
  | MBra a A B => Some (VBra (f a) (msubV X (mmap f A)) (msubV X (mmap f B)))
  | MEnd a _ => Some (VEnd (f a))
  | MTV j => Some (VTV j MSkip)
  | MRec _ | MVar => Some VNone
  end.

Fixpoint hdt (h : prio) (d : Z) (Q : msty) : option mhv * prio :=
  match Q with
  | MSkip => (None, h)
  | MSeq A B =>
      match hdt h d A with
      | (Some v, h') => (Some (vapp v B), h')
      | (None, h') => hdt h' d B
      end
  | MSnd a P => (Some (VSnd a P MSkip), h)
  | MRcv a P => (Some (VRcv a P MSkip), h)
  | MSel a A B => (Some (VSel a A B), h)
  | MBra a A B => (Some (VBra a A B), h)
  | MEnd a _ => (Some (VEnd a), h)
  | MTV j => (Some (VTV j MSkip), h)
  | MRec S0 => (hdb (pinI h) (MRec S0) S0, padd h d)
  | MVar => (Some VNone, h)
  end.

Definition vprio (o : option mhv) : option prio :=
  match o with
  | Some (VSnd a _ _ | VRcv a _ _ | VSel a _ _ | VBra a _ _ | VEnd a) => Some a
  | _ => None
  end.

(** ** Valuations of priority and session type variables

    A session type under the valuation v of the priority variables and
    ts of the session type variables, and the priority of its head. A
    channel at Skip has priority ⊤ (Fig. 4 has no case for Skip). *)

Definition mclose (v : val) (ts : list msty) (Q : msty) : msty := tsub ts (mmap (pclose v) Q).

Definition hext (o : option prio) : ext :=
  match o with Some a => evalp [] a | None => XT end.

Definition cprio (v : val) (ts : list msty) (Q : msty) (h : prio) (d : Z) : ext :=
  hext (vprio (hdt (pclose v h) d (mclose v ts Q)).1).

(** Items of lower bounds: a priority, or the head of a channel type. *)
Inductive lbi := LP (ρ : prio) | LC (Q : msty) (h : prio) (d : Z).

Global Instance lbi_eq_dec : EqDecision lbi.
Proof. solve_decision. Defined.

Global Instance lbi_countable : Countable lbi.
Proof.
  apply (inj_countable' (λ l, match l with LP ρ => inl ρ | LC Q h d => inr (Q, h, d) end)
                        (λ s, match s with inl ρ => LP ρ | inr (Q, h, d) => LC Q h d end)).
  by intros [].
Qed.

Definition evlb (v : val) (ts : list msty) (l : lbi) : ext :=
  match l with LP ρ => evalp v ρ | LC Q h d => cprio v ts Q h d end.

(** ** Walks and positions *)

Inductive wstep := WS | WB (b : bool) | WL (i : nat).

Global Instance wstep_eq_dec : EqDecision wstep.
Proof. solve_decision. Defined.

Inductive mpos :=
  | PR (h : prio) (d : Z)              (* the priority sequence h + k·d *)
  | PX (n : nat) (w : list wstep).     (* the walk w from end point n *)

(** ** Functional types *)

Record pctx := PCtx { pc_nv : nat; pc_nt : nat; pc_ok : val → list msty → Prop }.

Inductive mty :=
  | MUnit
  | MCh (pol : bool) (Q : msty) (p : mpos)
  | MEx (pol : bool) (Q : msty)
  | MArr (T : mty) (lo : list lbi) (ef : list prio) (V : mty)
  | MPoly (Θ : pctx) (T : mty) (ef : list prio) (V : mty)
  | MSeg (pol : bool) (k : nat) (Qa Qr : msty).

(** Substitution of an abstraction's variables by σ and τ. *)
Definition msq (σ : list prio) (τ : list msty) (Q : msty) : msty := tsub τ (mmap (psub σ) Q).

Definition lsub (σ : list prio) (τ : list msty) (l : lbi) : lbi :=
  match l with LP ρ => LP (psub σ ρ) | LC Q h d => LC (msq σ τ Q) (psub σ h) d end.

Definition possub (σ : list prio) (p : mpos) : mpos :=
  match p with PR h d => PR (psub σ h) d | x => x end.

Fixpoint msub (σ : list prio) (τ : list msty) (T : mty) : mty :=
  match T with
  | MUnit => MUnit
  | MCh pol Q p => MCh pol (msq σ τ Q) (possub σ p)
  | MEx pol Q => MEx pol (msq σ τ Q)
  | MArr T lo ef V => MArr (msub σ τ T) (lsub σ τ <$> lo) (psub σ <$> ef) (msub σ τ V)
  | x => x
  end.

Definition payty (P : mpay) : mty :=
  match P with MPUnit => MUnit | MPChan p Q h d => MCh p Q (PR h d) end.

(** |T| as the list whose minimum it is (Fig. 4). An abstract position
    lies at ⊥: no action may precede it, and nothing that holds it may
    act first. *)
Definition tprios (T : mty) : list lbi :=
  match T with
  | MCh _ Q (PR h d) => [LC Q h d]
  | MCh _ _ (PX _ _) | MEx _ _ => [LP PBot]
  | MArr _ lo _ _ => lo
  | _ => []
  end.

Definition mun (T : mty) : Prop :=
  match T with MUnit | MPoly _ _ _ _ | MSeg _ _ _ _ => True | _ => False end.

(** The end points a type mentions. *)
Fixpoint tnames (T : mty) : list nat :=
  match T with
  | MCh _ _ (PX n _) => [n]
  | MArr T _ _ V => tnames T ++ tnames V
  | _ => []
  end.

(** ** Erasure into the session types of the core *)

Definition U : ty := TBox 0 0 (BCs [] (λ _, False)) (TLolli None None TUnit TUnit).

Definition polS (pol : bool) (s : sty) : sty := if pol then dual s else s.

Definition pm (P : mpay) : nat := match P with MPUnit => 0 | MPChan _ _ _ _ => 1 end.

Fixpoint ers (Q : msty) : sty :=
  match Q with
  | MSkip => SSkip
  | MSeq A B => SSeq (ers A) (ers B)
  | MSnd _ P => SSnd (pm P) (ersp P)
  | MRcv _ P => SRcv (pm P) (ersp P)
  | MSel _ K1 K2 => SPlus (ers K1) (ers K2)
  | MBra _ K1 K2 => SWith (ers K1) (ers K2)
  | MEnd _ _ => SEnd
  | MRec S0 => SMu (ers S0)
  | MVar => SVar 0
  | MTV j => SVar j
  end
with ersp (P : mpay) : ty :=
  match P with
  | MPUnit => U
  | MPChan p Q _ _ => TSess (polS p (ers Q)) (pvar 0)
  end.

Lemma ers_mmap f : (∀ Q, ers (mmap f Q) = ers Q) ∧ (∀ P, pm (mmapp f P) = pm P ∧ ersp (mmapp f P) = ersp P).
Proof.
  apply msty_mpay_mut; intros; simpl; try done;
    repeat match goal with H : _ ∧ _ |- _ => destruct H end; try congruence.
  split; [done|]. by rewrite H.
Qed.
