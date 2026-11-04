(** * Types of Mordido and Pérez on our terms

    A. Mordido and J. A. Pérez, Deadlock-Free Context-Free Session
    Types, LNCS 2026 (arXiv 2506.20356v4), Fig. 1 (p. 6), Fig. 4 and
    Fig. 5 (p. 11). Fragment v1 of
    docs/extensions/adequacy/mordido-perez.md, with the restriction log
    of that file.

    - A priority is ⊥, ⊤, an integer n, a priority variable ι_j + n of
      the enclosing abstraction, or ι + n for the binder of ∀^S ([PI]).
    - A session type carries its continuation (!^ρ P.S). Choice is
      binary. Close^ρ and Wait^ρ are [MEnd]. [MRec S] is µβ.∀^S ι.S,
      the only recursive and the only priority-polymorphic session type
      (F-PAbsS, p. 7, puts ∀^S under an empty Θ, so it never nests).
    - The priority map Ψ moves into the types (decision D3). A channel
      type [MChan pol S h d] is S with the priority sequence
      [h + k·d ∣ k ∈ ℕ] of its channel. [pol] marks the dual end, so
      duality is a flag. inst unfolds [MRec] at the head of S,
      instantiates ι with h, and pops the sequence to h + d.
    - A payload is unit or a channel type with its own sequence.
    - Functional types are unit, channel types, linear arrows
      T →^{ρs,σs} U whose lower bound is the minimum of a nonempty list
      of priorities and whose latent effect is the maximum of a list,
      and priority abstractions ∀ιs∈Θ. T →^{⊤,σs}_un U. *)

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

(** ρ under a valuation, the variables replaced by integers. *)
Definition pclose (v : val) (ρ : prio) : prio :=
  match ρ with PV j n => PZ (default 0%Z (v !! j) + n) | x => x end.

(** ρ[σ/ιs] for the variables of an abstraction. *)
Definition psub (σ : list prio) (ρ : prio) : prio :=
  match ρ with PV j n => padd (default (PZ 0) (σ !! j)) n | x => x end.

(** ρ[h/ι] for the binder of ∀^Q. *)
Definition pinI (h : prio) (ρ : prio) : prio :=
  match ρ with PI n => padd h n | x => x end.

(** The latent effect max σs and the lower bound min ρs. *)
Definition xmaxl (v : val) (l : list prio) : ext := foldr (λ ρ a, xmax (evalp v ρ) a) XB l.
Definition xminl (v : val) (l : list prio) : ext := foldr (λ ρ a, xmin (evalp v ρ) a) XT l.

(** A finite priority, no ⊥, ⊤ or binder. *)
Definition pfin (ρ : prio) : Prop :=
  match ρ with PZ _ | PV _ _ => True | _ => False end.

(** ** Session types *)

Inductive msty :=
  | MSnd (ρ : prio) (P : mpay) (K : msty)
  | MRcv (ρ : prio) (P : mpay) (K : msty)
  | MSel (ρ : prio) (K1 K2 : msty)
  | MBra (ρ : prio) (K1 K2 : msty)
  | MEnd (ρ : prio) (w : bool)            (* Close^ρ, or Wait^ρ when w *)
  | MRec (Q : msty)                       (* µβ.∀^Q ι.Q *)
  | MVar                                  (* β *)
with mpay :=
  | MPUnit
  | MPChan (pol : bool) (Q : msty) (h : prio) (d : Z).

Scheme msty_mut := Induction for msty Sort Prop
  with mpay_mut := Induction for mpay Sort Prop.
Combined Scheme msty_mpay_mut from msty_mut, mpay_mut.

(** Countability, for priorities and session types inside the items of carried points. *)
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
  | MSnd a P K => GenNode 0 [prio_enc a; mpay_enc P; msty_enc K]
  | MRcv a P K => GenNode 1 [prio_enc a; mpay_enc P; msty_enc K]
  | MSel a K1 K2 => GenNode 2 [prio_enc a; msty_enc K1; msty_enc K2]
  | MBra a K1 K2 => GenNode 3 [prio_enc a; msty_enc K1; msty_enc K2]
  | MEnd a w => GenNode 4 [prio_enc a; b_enc w]
  | MRec Q => GenNode 5 [msty_enc Q]
  | MVar => GenNode 6 []
  end
with mpay_enc (P : mpay) : gen_tree Z :=
  match P with
  | MPUnit => GenNode 7 []
  | MPChan p Q h d => GenNode 8 [b_enc p; msty_enc Q; prio_enc h; GenLeaf d]
  end.

Fixpoint msty_dec (t : gen_tree Z) : msty :=
  match t with
  | GenNode 0 [a; P; K] => MSnd (prio_dec a) (mpay_dec P) (msty_dec K)
  | GenNode 1 [a; P; K] => MRcv (prio_dec a) (mpay_dec P) (msty_dec K)
  | GenNode 2 [a; K1; K2] => MSel (prio_dec a) (msty_dec K1) (msty_dec K2)
  | GenNode 3 [a; K1; K2] => MBra (prio_dec a) (msty_dec K1) (msty_dec K2)
  | GenNode 4 [a; w] => MEnd (prio_dec a) (b_dec w)
  | GenNode 5 [Q] => MRec (msty_dec Q)
  | _ => MVar
  end
with mpay_dec (t : gen_tree Z) : mpay :=
  match t with
  | GenNode 8 [p; Q; h; GenLeaf d] => MPChan (b_dec p) (msty_dec Q) (prio_dec h) d
  | _ => MPUnit
  end.

Lemma msty_dec_enc : (∀ Q, msty_dec (msty_enc Q) = Q) ∧ (∀ P, mpay_dec (mpay_enc P) = P).
Proof.
  apply msty_mpay_mut; intros; simpl; rewrite ?prio_dec_enc; try congruence.
  - by destruct w.
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

(** Every priority mapped by f (used for ρ[σ/ιs] and for valuations). *)
Fixpoint mmap (f : prio → prio) (Q : msty) : msty :=
  match Q with
  | MSnd a P K => MSnd (f a) (mmapp f P) (mmap f K)
  | MRcv a P K => MRcv (f a) (mmapp f P) (mmap f K)
  | MSel a K1 K2 => MSel (f a) (mmap f K1) (mmap f K2)
  | MBra a K1 K2 => MBra (f a) (mmap f K1) (mmap f K2)
  | MEnd a w => MEnd (f a) w
  | MRec Q => MRec (mmap f Q)
  | MVar => MVar
  end
with mmapp (f : prio → prio) (P : mpay) : mpay :=
  match P with
  | MPUnit => MPUnit
  | MPChan p Q h d => MPChan p (mmap f Q) (f h) d
  end.

(** β replaced by X. The body of [MRec] holds no [MRec] and its
    payloads no β ([rbody]), so the replacement neither stops early nor
    enters a payload. *)
Fixpoint msubV (X : msty) (Q : msty) : msty :=
  match Q with
  | MSnd a P K => MSnd a P (msubV X K)
  | MRcv a P K => MRcv a P (msubV X K)
  | MSel a K1 K2 => MSel a (msubV X K1) (msubV X K2)
  | MBra a K1 K2 => MBra a (msubV X K1) (msubV X K2)
  | MEnd a w => MEnd a w
  | MRec Q => MRec Q
  | MVar => X
  end.

(** One unfolding of µβ.∀^Q ι.S₀ at the head h of the sequence. *)
Definition munf (S0 : msty) (h : prio) : msty := msubV (MRec S0) (mmap (pinI h) S0).

(** inst: the head of a channel type and the sequence after it. *)
Definition mhd (Q : msty) (h : prio) (d : Z) : msty * prio :=
  match Q with MRec S0 => (munf S0 h, padd h d) | _ => (Q, h) end.

(** Closed session types: no β. *)
Fixpoint rclosed (Q : msty) : Prop :=
  match Q with
  | MSnd _ P K | MRcv _ P K => rpay P ∧ rclosed K
  | MSel _ K1 K2 | MBra _ K1 K2 => rclosed K1 ∧ rclosed K2
  | MEnd _ _ => True
  | MRec _ | MVar => False
  end
with rpay (P : mpay) : Prop :=
  match P with
  | MPUnit => True
  | MPChan _ Q _ _ => rclosed Q
  end.

(** The body of a recursive type: no [MRec] anywhere, payloads closed. *)
Fixpoint rbody (Q : msty) : Prop :=
  match Q with
  | MSnd _ P K | MRcv _ P K => rpay P ∧ rbody K
  | MSel _ K1 K2 | MBra _ K1 K2 => rbody K1 ∧ rbody K2
  | MEnd _ _ | MVar => True
  | MRec _ => False
  end.

(** An action at the head. *)
Definition mact (Q : msty) : Prop :=
  match Q with MRec _ | MVar => False | _ => True end.

(** A closed, well-formed channel type: β only in recursive bodies,
    bodies of [rbody] shape with an action at the head. *)
Fixpoint mwf (Q : msty) : Prop :=
  match Q with
  | MSnd _ P K | MRcv _ P K => mwfp P ∧ mwf K
  | MSel _ K1 K2 | MBra _ K1 K2 => mwf K1 ∧ mwf K2
  | MEnd _ _ => True
  | MRec S0 => rbody S0 ∧ mact S0
  | MVar => False
  end
with mwfp (P : mpay) : Prop :=
  match P with MPUnit => True | MPChan _ Q _ _ => mwf Q end.

(** ** Erasure into the session types of the core *)

Definition U : ty := TBox 0 0 (BCs [] (λ _, False)) (TLolli None None TUnit TUnit).

Definition polS (pol : bool) (s : sty) : sty := if pol then dual s else s.

Definition pm (P : mpay) : nat := match P with MPUnit => 0 | MPChan _ _ _ _ => 1 end.

Fixpoint ers (Q : msty) : sty :=
  match Q with
  | MSnd _ P K => SSeq (SSnd (pm P) (ersp P)) (ers K)
  | MRcv _ P K => SSeq (SRcv (pm P) (ersp P)) (ers K)
  | MSel _ K1 K2 => SPlus (ers K1) (ers K2)
  | MBra _ K1 K2 => SWith (ers K1) (ers K2)
  | MEnd _ _ => SEnd
  | MRec S0 => SMu (ers S0)
  | MVar => SVar 0
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

(** Substitution leaves an erased closed payload alone. *)
Lemma ers_rclosed σ :
  (∀ Q, rclosed Q → sinst σ (ers Q) = ers Q ∧ sinst σ (dual (ers Q)) = dual (ers Q)) ∧
  (∀ P, rpay P → sinst_ty σ (ersp P) = ersp P).
Proof.
  apply msty_mpay_mut; simpl; intros; try done;
    repeat match goal with H : _ ∧ _ |- _ => destruct H end;
    repeat match goal with H : ?A → _, H' : ?A |- _ => specialize (H H') end;
    repeat match goal with H : _ ∧ _ |- _ => destruct H end;
    try (split; simpl; congruence).
  match goal with |- context [polS ?b _] => destruct b end; simpl; congruence.
Qed.

(** The erasure of an unfolding is the unrolling of the erasure. *)
Lemma ers_subV X Q :
  rbody Q → sinst (ers X .: SVar) (ers Q) = ers (msubV X Q).
Proof.
  induction Q as [a P K IH|a P K IH|a K1 IH1 K2 IH2|a K1 IH1 K2 IH2|a w|Q IH|];
    simpl; try done; intros Hb;
    repeat match goal with H : _ ∧ _ |- _ => destruct H end.
  - rewrite IH by done. by rewrite (proj2 (ers_rclosed _) P).
  - rewrite IH by done. by rewrite (proj2 (ers_rclosed _) P).
  - by rewrite IH1, IH2.
  - by rewrite IH1, IH2.
Qed.

Lemma rbody_mmap f :
  (∀ Q, (rbody Q → rbody (mmap f Q)) ∧ (rclosed Q → rclosed (mmap f Q))) ∧
  (∀ P, rpay P → rpay (mmapp f P)).
Proof. apply msty_mpay_mut; simpl; intros; tauto. Qed.

Lemma ers_munf S0 h : rbody S0 → unroll (ers S0) = ers (munf S0 h).
Proof.
  intros Hb. unfold munf, unroll. rewrite <-ers_subV by (by apply rbody_mmap).
  simpl. by rewrite (proj1 (ers_mmap _)).
Qed.

(** A recursive body with an action at its head erases to a
    contractive µ, so inst is E-Conv by [seq_mu]. *)
Lemma ers_contractive S0 : mact S0 → contractive (SMu (ers S0)).
Proof.
  intros Ha. unfold contractive, unfoldS.
  destruct S0 as [a P K|a P K|a K1 K2|a K1 K2|a w| |]; simpl in Ha; try done; simpl;
    try (destruct (sfuel (ers K)); simpl; done).
Qed.

Lemma ers_mhd Q h d :
  mwf Q → seq (ers Q) (ers (mhd Q h d).1).
Proof.
  intros Hw. destruct Q as [| | | | |S0|]; simpl; try apply seq_refl.
  destruct Hw as [Hb Ha]. rewrite <-(ers_munf S0 h Hb). by apply seq_mu, ers_contractive.
Qed.

(** ** The head action of a channel type

    The dual end ([pol = true]) reads every action of S dually. *)

Inductive mact_v :=
  | ASnd (a : prio) (P : mpay) (K : msty)
  | ARcv (a : prio) (P : mpay) (K : msty)
  | ASel (a : prio) (K1 K2 : msty)
  | ABra (a : prio) (K1 K2 : msty)
  | AEnd (a : prio)
  | ANone.

Definition mview (pol : bool) (Q : msty) : mact_v :=
  match Q with
  | MSnd a P K => if pol then ARcv a P K else ASnd a P K
  | MRcv a P K => if pol then ASnd a P K else ARcv a P K
  | MSel a K1 K2 => if pol then ABra a K1 K2 else ASel a K1 K2
  | MBra a K1 K2 => if pol then ASel a K1 K2 else ABra a K1 K2
  | MEnd a _ => AEnd a
  | _ => ANone
  end.

(** The priority of the next action. *)
Definition hprio (Q : msty) : prio :=
  match Q with
  | MSnd a _ _ | MRcv a _ _ | MSel a _ _ | MBra a _ _ | MEnd a _ => a
  | _ => PTop
  end.

Definition chead (Q : msty) (h : prio) (d : Z) : prio := hprio (mhd Q h d).1.

(** ** Functional types *)

Inductive mty :=
  | MUnit
  | MChan (pol : bool) (Q : msty) (h : prio) (d : Z)
  | MArr (T : mty) (lo ef : list prio) (V : mty)
  | MPoly (nv : nat) (cs : list (prio * prio)) (T : mty) (ef : list prio) (V : mty).

(** T[σ/ιs]. A priority abstraction is closed and stays as it is. *)
Fixpoint msub (σ : list prio) (T : mty) : mty :=
  match T with
  | MUnit => MUnit
  | MChan p Q h d => MChan p (mmap (psub σ) Q) (psub σ h) d
  | MArr T lo ef V => MArr (msub σ T) (psub σ <$> lo) (psub σ <$> ef) (msub σ V)
  | MPoly nv cs T ef V => MPoly nv cs T ef V
  end.

Definition payty (P : mpay) : mty :=
  match P with MPUnit => MUnit | MPChan p Q h d => MChan p Q h d end.

(** |T| as the list whose minimum it is, empty for ⊤ (Fig. 4). *)
Definition tprios (T : mty) : list prio :=
  match T with
  | MChan _ Q h d => [chead Q h d]
  | MArr _ lo _ _ => lo
  | _ => []
  end.

(** |T| = ⊤: the types that split copies (S-Top, Fig. 12, p. 24). *)
Definition mun (T : mty) : Prop :=
  match T with MUnit | MPoly _ _ _ _ _ => True | _ => False end.
