(** * The priority world of Mordido and Pérez, version 3

    Version 3 (docs/extensions/adequacy/mordido-perez.md, section 15)
    is version 2 with n-ary choices and with channels created after a
    segment call. The text below describes version 2 where version 3
    agrees with it.

    docs/extensions/adequacy/mordido-perez.md, section 12. Priorities
    become points relative to an anchor, as in version 1. An anchor
    stands for a valuation of the priority variables and the session
    type variables of the enclosing abstraction, and its slots are

    - B[RAnc σs τs], the anchor of the instance σs, τs read in B's
      valuation, at which a priority abstraction is forced;
    - B[RCh Q h d], the channel of type Q with priority sequence
      h + k·d, at its current instant;
    - B[RLo ls], the lower point of a closure whose lower bound is the
      minimum of the items ls;
    - B[RHi σs], the upper point of a latent effect max σs.

    A point denotes ([den]) a valuation, a channel, a lower or upper
    level, or junk, given a denotation of its root. A channel denotes
    its session type with the head of its sequence, and its head form
    [hdt] gives the successor, the branch roots and the payload slot.
    Two points are equivalent when every walk from them reaches points
    of equal rank ([oeq]), so the equivalences of context-free session
    types (T-Eq) identify points. The rank is the priority of the head.
    A continuation that does not rise denotes junk ranked above every
    channel. An upper point with ⊤ lies above every other point: it is
    the coarse ceiling of K8 and stands for the latent effect ⊤ of a
    call over an unbounded segment (p. 21). *)

From stdpp Require Import base gmap countable numbers.
From LRGV Require Export examples.cfst.CfstTools mp.MP3Types.

Set Default Proof Using "All".

(** ** Items *)

Inductive ritem :=
  | RAnc (σ : list prio) (τ : list msty)
  | RCh (Q : msty) (h : prio) (d : Z)
  | RLo (l : list lbi)
  | RHi (l : list prio)
  | RLow.                                 (* the start of the low chain *)

Global Instance ritem_eq_dec : EqDecision ritem.
Proof. solve_decision. Defined.

Global Instance ritem_countable : Countable ritem.
Proof.
  apply (inj_countable'
    (λ r, match r with
          | RAnc σ τ => inl (inl (σ, τ)) | RCh Q h d => inl (inr (Q, h, d))
          | RLo l => inr (inl (inl l)) | RHi l => inr (inl (inr l)) | RLow => inr (inr ())
          end : (list prio * list msty + msty * prio * Z) + ((list lbi + list prio) + unit))
    (λ s, match s with
          | inl (inl (σ, τ)) => RAnc σ τ | inl (inr (Q, h, d)) => RCh Q h d
          | inr (inl (inl l)) => RLo l | inr (inl (inr l)) => RHi l | inr (inr _) => RLow
          end)).
  by intros [].
Qed.

Definition proot : point := Pt (NConst 0) 0.
Definition rpt (B : point) (r : ritem) : point := pt_slot B (encode_nat r).

(** ** Ranks

    ⊥ and integers with a level and a subrank, junk and ⊤ above them,
    the ceiling above those, and the junk of the ceiling on top. At one
    priority a lower point of min ls has level 0 and subrank −|ls|, a
    channel level 1 and the depth of its choice as subrank (section
    15), and an upper point level 2 and subrank |σs|. So a channel at
    an inner node of an n-ary choice lies above the outer node and
    below every upper point of the same priority. The lower point of a
    closure that holds nothing lies above the ceiling, so an argument
    of any effect may precede it. *)

(** Version 3 adds the low chain KL with its lower points KLL and its
    upper point KLH below ⊥, and above the junk of the ceiling the
    upper point KV of the high chain, the lower point KW of a closure
    that holds nothing, and junk KX on top (section 15). *)
Inductive rk := KLL (j : Z) | KL (j : Z) | KLH (j : Z) | KB (s j : Z) | KZ (z s j : Z) | KT (j : Z) | KH | KU (j : Z)
              | KV | KW | KX (j : Z).

Definition rkey (a : rk) : Z * Z * Z * Z :=
  match a with
  | KLL j => (0, 0, 0, j) | KL j => (1, 0, 0, j) | KLH j => (2, 0, 0, j)
  | KB s j => (3, 0, s, j) | KZ z s j => (4, z, s, j) | KT j => (5, 0, 0, j) | KH => (6, 0, 0, 0)
  | KU j => (7, 0, 0, j) | KV => (8, 0, 0, 0) | KW => (9, 0, 0, 0) | KX j => (10, 0, 0, j)
  end%Z.

Definition lex4 (a b : Z * Z * Z * Z) : Prop :=
  match a, b with
  | (a1, a2, a3, a4), (b1, b2, b3, b4) =>
      (a1 < b1 ∨ (a1 = b1 ∧ (a2 < b2 ∨ (a2 = b2 ∧ (a3 < b3 ∨ (a3 = b3 ∧ a4 < b4))))))%Z
  end.

Definition rlt (a b : rk) : Prop := lex4 (rkey a) (rkey b).
Arguments lex4 !a !b /.
Arguments rlt a b /.

Lemma rlt_irrefl a : ¬ rlt a a.
Proof. unfold rlt, lex4. destruct (rkey a) as [[[]]]. lia. Qed.

Lemma rlt_trans a b c : rlt a b → rlt b c → rlt a c.
Proof. unfold rlt, lex4. destruct (rkey a) as [[[]]], (rkey b) as [[[]]], (rkey c) as [[[]]]. lia. Qed.

Global Instance rlt_dec a b : Decision (rlt a b).
Proof. unfold rlt, lex4. destruct (rkey a) as [[[]]], (rkey b) as [[[]]]. apply _. Defined.

(** ** Denotations *)

Inductive dn :=
  | DAnc (v : val) (ts : list msty)
  | DCh (Q : msty) (h : prio) (d : Z)
  | DLo (x : ext) (n : nat)
  | DHi (x : ext) (n : nat)
  | DJ (j : Z)
  | DU (j : Z)
  | DLC (j : Z)                           (* the low chain *)
  | DX (j : Z).                           (* junk on top *)

Definition xrk (x : ext) (s j : Z) (t : rk) : rk :=
  match x with XBB => KLH j | XB => KB s j | XZ z => KZ z s j | XT => t | XTT => KV end.

(** The depth of a head, the subrank of a channel. *)
Definition hdep (o : option prio) : Z := match o with Some a => Z.of_nat (pdep a) | None => 0 end.

Definition cdep (v : val) (ts : list msty) (Q : msty) (h : prio) (d : Z) : Z :=
  hdep (vprio (hdt (pclose v h) d (mclose v ts Q)).1).

Definition hlen (l : list prio) : nat := if bool_decide (PTop ∈ l) then 0 else length l.

Definition rank (d : dn) : rk :=
  match d with
  | DAnc _ _ => KT 0
  | DCh Q h dd => xrk (hext (vprio (hdt h dd Q).1)) 1 (hdep (vprio (hdt h dd Q).1)) (KT 1)
  | DLo x n =>
      match x with
      | XBB => KLL (- Z.of_nat n) | XTT => match n with 0 => KW | _ => KU (- Z.of_nat n) end
      | _ => xrk x 0 (- Z.of_nat n) (match n with 0 => KW | _ => KT (- Z.of_nat n) end)
      end
  | DHi x n => xrk x 2 (Z.of_nat n) KH
  | DJ j => KT j
  | DU j => KU j
  | DLC j => KL j
  | DX j => KX j
  end.

(** The junk just above a rank. *)
Definition jnk (a : rk) : dn :=
  match a with
  | KT j => DJ (j + 1) | KH => DU 0 | KU j => DU (j + 1)
  | KV | KW => DX 0 | KX j => DX (j + 1) | _ => DJ 0
  end.

Lemma rlt_jnk a : rlt a (rank (jnk a)).
Proof. destruct a; simpl; lia. Qed.

(** The move to d′ from d, junk when the rank would not rise. The junk
    of a channel stays below the ceiling. *)
Definition guard (d d' : dn) : dn :=
  if decide (rlt (rank d) (rank d')) then d' else jnk (rank d).

Definition dnext (d : dn) : dn :=
  match d with
  | DCh Q h dd =>
      match hdt h dd Q with
      | (Some (VSnd _ _ K), h') | (Some (VRcv _ _ K), h') => DCh K h' dd
      | _ => DJ 0
      end
  | DLC j => DLC (j + 1)
  | _ => DJ 0
  end.

Definition dsh (d : dn) : dn := guard d (dnext d).

Definition dbr0 (d : dn) (b : bool) : dn :=
  match d with
  | DCh Q h dd =>
      match hdt h dd Q with
      | (Some (VSel _ K1 K2), h') | (Some (VBra _ K1 K2), h') => DCh (if b then K2 else K1) h' dd
      | _ => DJ 0
      end
  | DLC j => DLC (j + 1)
  | _ => DJ 0
  end.

Definition dbr (d : dn) (b : bool) : dn := guard d (dbr0 d b).

Definition evalZ (v : val) (ρ : prio) : Z :=
  match evalp v ρ with XZ z => z | _ => 0%Z end.

Definition xminlb (v : val) (ts : list msty) (l : list lbi) : ext :=
  foldr (λ i a, xmin (evlb v ts i) a) XTT l.

Definition dsl (d : dn) (i : nat) : dn :=
  match d with
  | DAnc v ts =>
      match decode_nat i with
      | Some (RAnc σ τ) => DAnc (evalZ v <$> σ) (mclose v ts <$> τ)
      | Some (RCh Q h dd) => DCh (mclose v ts Q) (pclose v h) dd
      | Some (RLo l) => DLo (xminlb v ts l) (length l)
      | Some (RHi l) => DHi (xmaxl v l) (hlen l)
      | Some RLow => DLC 0
      | None => DJ 0
      end
  | DCh Q h dd =>
      match i, hdt h dd Q with
      | 0, (Some (VSnd _ (MPChan _ Qp hp dp) _), _) | 0, (Some (VRcv _ (MPChan _ Qp hp dp) _), _) =>
          DCh Qp hp dp
      | _, _ => DJ 0
      end
  | DLC j => DLC (j + 1)
  | DU j => DU (j + 1)
  | _ => DJ 0
  end.

Lemma guard_rise d d' : rlt (rank d) (rank (guard d d')).
Proof. unfold guard. case_decide; [done|]. apply rlt_jnk. Qed.

Fixpoint dshN (n : nat) (d : dn) : dn :=
  match n with 0 => d | S n => dsh (dshN n d) end.

Lemma dshN_add n m d : dshN n (dshN m d) = dshN (n + m) d.
Proof. induction n; simpl; congruence. Qed.

(** The denotation of a name, given the denotation f of its root. *)
Fixpoint denN (f : pname → dn) (p : pname) : dn :=
  match p with
  | NConst _ | NVar _ => f p
  | NSlot q b i => dsl (dshN b (denN f q)) i
  | NBr q b i => dbr (dshN b (denN f q)) i
  end.

Definition den (f : pname → dn) (x : point) : dn := dshN (pt_off x) (denN f (pt_name x)).

Lemma den_shift f x : den f (pt_shift 1 x) = dsh (den f x).
Proof. destruct x as [p k]. unfold den, pt_shift. simpl. by rewrite Nat.add_1_r. Qed.

Lemma den_shiftN f n x : den f (pt_shift n x) = dshN n (den f x).
Proof. destruct x as [p k]. unfold den, pt_shift. simpl. by rewrite dshN_add, Nat.add_comm. Qed.

Lemma den_slot f x i : den f (pt_slot x i) = dsl (den f x) i.
Proof. done. Qed.

Lemma den_br f x i : den f (pt_br x i) = dbr (den f x) i.
Proof. done. Qed.

(** Points that share a root denote alike under denotations that agree
    on the root. *)
Lemma denN_root f g p : f (pn_root p) = g (pn_root p) → denN f p = denN g p.
Proof. induction p as [a|a|q IH b i|q IH b i]; simpl; try done; intros H; by rewrite IH. Qed.

Lemma den_root f g x : f (pt_root x) = g (pt_root x) → den f x = den g x.
Proof. intros H. unfold den. by rewrite (denN_root f g). Qed.

(** ** Walks and observational equivalence *)

Fixpoint mwalk (x : point) (u : list wstep) : point :=
  match u with
  | [] => x
  | WS :: u => mwalk (pt_shift 1 x) u
  | WB b :: u => mwalk (pt_br x b) u
  | WL i :: u => mwalk (pt_slot x i) u
  end.

Lemma mwalk_app x u u' : mwalk x (u ++ u') = mwalk (mwalk x u) u'.
Proof. revert x. induction u as [|[] u IH]; intros x; simpl; auto. Qed.

Fixpoint dwalk (d : dn) (u : list wstep) : dn :=
  match u with
  | [] => d
  | WS :: u => dwalk (dsh d) u
  | WB b :: u => dwalk (dbr d b) u
  | WL i :: u => dwalk (dsl d i) u
  end.

Lemma den_mwalk f x u : den f (mwalk x u) = dwalk (den f x) u.
Proof.
  revert x. induction u as [|[|b|i] u IH]; intros x; simpl; [done| | |];
    rewrite IH; [by rewrite den_shift|by rewrite den_br|by rewrite den_slot].
Qed.

Definition oeq (d d' : dn) : Prop := ∀ u, rank (dwalk d u) = rank (dwalk d' u).

Lemma oeq_refl d : oeq d d.
Proof. by intros u. Qed.
Lemma oeq_sym d d' : oeq d d' → oeq d' d.
Proof. intros H u. by rewrite H. Qed.
Lemma oeq_trans d d' d'' : oeq d d' → oeq d' d'' → oeq d d''.
Proof. intros H1 H2 u. by rewrite H1, H2. Qed.
Lemma oeq_rank d d' : oeq d d' → rank d = rank d'.
Proof. intros H. apply (H []). Qed.
Lemma oeq_dsh d d' : oeq d d' → oeq (dsh d) (dsh d').
Proof. intros H u. apply (H (WS :: u)). Qed.
Lemma oeq_dbr d d' b : oeq d d' → oeq (dbr d b) (dbr d' b).
Proof. intros H u. apply (H (WB b :: u)). Qed.
Lemma oeq_dsl d d' i : oeq d d' → oeq (dsl d i) (dsl d' i).
Proof. intros H u. apply (H (WL i :: u)). Qed.
Lemma oeq_dshN n d d' : oeq d d' → oeq (dshN n d) (dshN n d').
Proof. induction n; simpl; [done|]. intros H. by apply oeq_dsh, IHn. Qed.

(** Two channels with one head and one sequence are equivalent. *)
Lemma oeq_hdt Q Q' h h' d :
  hdt h d Q = hdt h' d Q' → oeq (DCh Q h d) (DCh Q' h' d).
Proof.
  intros E u. destruct u as [|[|b|i] u]; simpl.
  - by rewrite E.
  - unfold dsh, guard. simpl. rewrite E. done.
  - unfold dbr, guard. simpl. rewrite E. done.
  - simpl. rewrite E. done.
Qed.

(** ** Strictness through a denotation and an equivalence *)

Lemma wgen_strict_oeq N E L (dnt : point → dn) :
  (∀ p, p ∈ N → ∃ a, p = NConst a) →
  (∀ x y, E x y → eq_or_supp N x y) →
  (∀ x y, L x y → po_or_supp N x y) →
  (∀ x, dnt (pt_shift 1 x) = dsh (dnt x)) →
  (∀ x i, dnt (pt_slot x i) = dsl (dnt x) i) →
  (∀ x i, dnt (pt_br x i) = dbr (dnt x) i) →
  (∀ x y, E x y → oeq (dnt x) (dnt y)) →
  (∀ x y, L x y → rlt (rank (dnt x)) (rank (dnt y))) →
  strict (wgen N E L).
Proof.
  intros HN HE HL Hs Hl Hb Hc HLr. split; [by apply wgen_wf|].
  assert (∀ x y, geq E x y → oeq (dnt x) (dnt y)) as Heq.
  { induction 1; try (by apply Hc); [apply oeq_refl|by apply oeq_sym|by eapply oeq_trans| | |].
    - rewrite !Hs. by apply oeq_dsh.
    - rewrite !Hl. by apply oeq_dsl.
    - rewrite !Hb. by apply oeq_dbr. }
  assert (∀ x y, glt E L x y → rlt (rank (dnt x)) (rank (dnt y))) as Hlt.
  { induction 1 as [x y H|x|x i|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
    - by apply HLr.
    - rewrite Hs. apply guard_rise.
    - rewrite Hb. apply guard_rise.
    - apply Heq, oeq_rank in Hx, Hy. by rewrite Hx, <-Hy.
    - by eapply rlt_trans. }
  intros x H. apply Hlt in H. exact (rlt_irrefl _ H).
Qed.

(** ** The world *)

Definition f0 (p : pname) : dn := match p with NConst 0 => DAnc [] [] | _ => DJ 0 end.

Definition rooted0 (x : point) : Prop := pt_root x = NConst 0.

Definition Wmp : world :=
  wgen {[NConst 0]}
    (λ x y, rooted0 x ∧ rooted0 y ∧ oeq (den f0 x) (den f0 y))
    (λ x y, rooted0 x ∧ rooted0 y ∧ rlt (rank (den f0 x)) (rank (den f0 y))).

Lemma Wmp_strict : strict Wmp.
Proof.
  apply (wgen_strict_oeq _ _ _ (den f0)).
  - intros p ->%elem_of_singleton. by exists 0.
  - intros x y (Hx & Hy & _). right. unfold rooted0 in *. rewrite Hx, Hy. set_solver.
  - intros x y (Hx & Hy & _). right. unfold rooted0 in *. rewrite Hx, Hy. set_solver.
  - apply den_shift.
  - apply den_slot.
  - apply den_br.
  - by intros x y (_ & _ & H).
  - by intros x y (_ & _ & H).
Qed.

Lemma Wmp_wf : world_wf Wmp.
Proof. apply Wmp_strict. Qed.

(** ** Instantiating a root

    A point rooted at the variable a, instantiated by σ, denotes under f
    what it denotes when its root denotes what σ a denotes. *)

Lemma den_pn_inst f g σ a p :
  pn_root p = NVar a → g (NVar a) = den f (σ a) → den f (pn_inst σ p) = denN g p.
Proof.
  intros Hp Hg. induction p as [c|c|q IH b i|q IH b i]; simpl in Hp; try discriminate.
  - injection Hp as ->. simpl. by rewrite Hg.
  - change (pn_inst σ (NSlot q b i)) with (pt_slot (pt_shift b (pn_inst σ q)) i).
    rewrite den_slot, den_shiftN, IH by done. done.
  - change (pn_inst σ (NBr q b i)) with (pt_br (pt_shift b (pn_inst σ q)) i).
    rewrite den_br, den_shiftN, IH by done. done.
Qed.

Lemma den_inst f g σ a x :
  pt_root x = NVar a → g (NVar a) = den f (σ a) → den f (pt_inst σ x) = den g x.
Proof.
  intros Hx Hg. destruct x as [p o]. unfold pt_inst, pt_root in *. simpl in *.
  rewrite den_shiftN, (den_pn_inst f g σ a) by done. done.
Qed.

(** ** Anchors *)

Definition models (Θ : pctx) (v : val) (ts : list msty) : Prop := pc_ok Θ v ts.

Definition ianc (B : point) (v : val) (ts : list msty) (p : pname) : dn :=
  if decide (p = pt_name B) then DAnc v ts else DJ 0.

Definition isroot (B : point) : Prop := pt_off B = 0 ∧ pn_root (pt_name B) = pt_name B.

Lemma pn_root_cases p : ∃ a, pn_root p = NConst a ∨ pn_root p = NVar a.
Proof. induction p as [a|a|q IH b i|q IH b i]; simpl; eauto. Qed.

Lemma den_ianc B v ts : isroot B → den (ianc B v ts) B = DAnc v ts.
Proof.
  intros [Ho Hr]. destruct B as [p o]. simpl in *. subst o. unfold den. simpl.
  destruct (pn_root_cases p) as [a [Ha|Ha]]; rewrite Ha in Hr; subst p; simpl;
    unfold ianc; simpl; by rewrite decide_True.
Qed.

(** Every fact between points of the root r that holds at every
    valuation of Θ. *)
Definition crel_fact (Θ : pctx) (r : pname) (g : fact) : Prop :=
  match g with
  | FEq x y => pt_root x = r ∧ pt_root y = r ∧
               ∀ v ts, models Θ v ts → oeq (den (ianc (Pt r 0) v ts) x) (den (ianc (Pt r 0) v ts) y)
  | FLt x y => pt_root x = r ∧ pt_root y = r ∧
               ∀ v ts, models Θ v ts → rlt (rank (den (ianc (Pt r 0) v ts) x)) (rank (den (ianc (Pt r 0) v ts) y))
  end.

Definition Crel (Θ : pctx) : bcs := BCs [] (crel_fact Θ (NVar 0)).

(** The constraint of an abstraction over a segment, any valuation. *)
Definition Θany (k : nat) : pctx := PCtx 0 k (λ _ _, True).

(** The coarse ceiling and the floor of the walks from κ, with the
    upper and the lower point of the anchor b. *)
Definition pex_fact (κ b : nat) (g : fact) : Prop :=
  (∃ u, g = FLt (mwalk (pvar κ) u) (rpt (pvar b) (RHi [PTop]))) ∨
  (∃ u, g = FLt (rpt (pvar b) (RLo [LP PBot])) (mwalk (pvar κ) u)).

Definition Cseg (k : nat) : bcs := BCs [] (λ g, pex_fact 0 1 g ∨ crel_fact (Θany k) (NVar 1) g).
Definition Cex (B : point) : bcs := BCs [B] (pex_fact 0 1).

(** ** Translation of types *)

Definition hiz (B : point) (ef : list prio) : option point :=
  match ef with [] => None | _ => Some (rpt B (RHi ef)) end.

Definition ptsb (B : point) : nat → point := λ _, B.

Fixpoint tr (B : point) (pts : nat → point) (T : mty) : ty :=
  match T with
  | MUnit => U
  | MCh p Q (PR h d) => TSess (polS p (ers Q)) (rpt B (RCh Q h d))
  | MCh p Q (PX n w) => TSess (polS p (ers Q)) (mwalk (pts n) w)
  | MCh p Q (PL w) => TSess (polS p (ers Q)) (mwalk (rpt B RLow) w)
  | MCh p Q (PH w) => TSess (polS p (ers Q)) (mwalk (pt_shift 1 (rpt B (RHi [PTop]))) w)
  | MEx p Q => TEx (Some (rpt B (RLo [LP PBot]))) 1 (Cex B) (TSess (polS p (ers Q)) (pvar 0))
  | MArr T lo ef V => TLolli (hiz B ef) (Some (rpt B (RLo lo))) (tr B pts T) (tr B pts V)
  | MPoly Θ T ef V =>
      TBox 1 (pc_nt Θ) (Crel Θ)
        (TLolli None None TUnit
           (TLolli (hiz (pvar 0) ef) None (tr (pvar 0) (ptsb (pvar 0)) T) (tr (pvar 0) (ptsb (pvar 0)) V)))
  | MSeg p k Qa Qr =>
      TBox 2 k (Cseg k)
        (TLolli None None TUnit
           (TLolli (Some (rpt (pvar 1) (RHi [PTop]))) None (TSess (polS p (ers Qa)) (pvar 0))
              (TEx (Some (rpt (pvar 1) (RLo [LP PBot]))) 1 (Cex (pvar 1)) (TSess (polS p (ers Qr)) (pvar 0)))))
  end.

Lemma pt_inst_rpt σ B r : pt_inst σ (rpt B r) = rpt (pt_inst σ B) r.
Proof. apply pt_inst_slot. Qed.

Lemma pt_inst_mwalk σ x u : pt_inst σ (mwalk x u) = mwalk (pt_inst σ x) u.
Proof.
  revert x. induction u as [|[|b|i] u IH]; intros x; simpl; [done| | |]; rewrite IH;
    [by rewrite pt_inst_shift|by rewrite pt_inst_br|by rewrite pt_inst_slot].
Qed.

Lemma hiz_pinst σ B ef : pt_inst σ <$> hiz B ef = hiz (pt_inst σ B) ef.
Proof. destruct ef; simpl; [done|]. by rewrite pt_inst_rpt. Qed.

Lemma pup1_0 σ : pt_inst (pup 1 σ) (pvar 0) = pvar 0.
Proof. rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True by lia. Qed.

Lemma tr_ext B pts pts' T : (∀ n, pts n = pts' n) → tr B pts T = tr B pts' T.
Proof.
  intros H. induction T as [|p Q [h d|n w|w|w]| p Q |T IH1 lo ef V IH2|Θ T IH1 ef V IH2|p k Qa Qr];
    simpl; try done; [by rewrite H|by rewrite IH1, IH2].
Qed.

Lemma pup_lt m σ a : a < m → pt_inst (pup m σ) (pvar a) = pvar a.
Proof. intros Ha. rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True. Qed.

Lemma tr_pinst σ B pts T : pinst_ty σ (tr B pts T) = tr (pt_inst σ B) (pt_inst σ ∘ pts) T.
Proof.
  revert σ B pts. induction T as [|p Q [h d|n w|w|w]| p Q |T IH1 lo ef V IH2|Θ T IH1 ef V IH2|p k Qa Qr];
    intros σ B pts; simpl.
  - done.
  - by rewrite pt_inst_rpt.
  - by rewrite pt_inst_mwalk.
  - by rewrite pt_inst_mwalk, pt_inst_rpt.
  - by rewrite pt_inst_mwalk, pt_inst_shift, pt_inst_rpt.
  - by rewrite pt_inst_rpt, pup1_0.
  - by rewrite IH1, IH2, hiz_pinst, pt_inst_rpt.
  - rewrite IH1, IH2, hiz_pinst, pup1_0. unfold bcs_inst, Crel. simpl.
    rewrite !(tr_ext (pvar 0) (pt_inst (pup 1 σ) ∘ ptsb (pvar 0)) (ptsb (pvar 0))); try done;
      intros n; apply pup1_0.
  - unfold bcs_inst, Cseg, Cex. simpl. rewrite !pt_inst_rpt, !(pup_lt 2) by lia.
    by rewrite !pup1_0.
Qed.

Lemma tr_un B B' pts pts' T : mun T → tr B pts T = tr B' pts' T.
Proof. destruct T; simpl; done. Qed.

Lemma tr_unlimited B pts T : mun T → unlimited (tr B pts T).
Proof. destruct T; simpl; done. Qed.

(** ** Good anchors

    [good Ψ Θ B]: B is a root, and Γ ⊢ ≡ and Γ ⊢ ≺ hold between two
    points of B's root whenever they hold at every valuation of Θ. *)

Record good (Ψ : hyps) (Θ : pctx) (B : point) : Prop := {
  gd_isroot : isroot B;
  gd_inh : ∃ v ts, models Θ v ts;
  gd_eq x y : pt_root x = pt_name B → pt_root y = pt_name B →
    (∀ v ts, models Θ v ts → oeq (den (ianc B v ts) x) (den (ianc B v ts) y)) → seqs Wmp Ψ x y;
  gd_lt x y : pt_root x = pt_name B → pt_root y = pt_name B →
    (∀ v ts, models Θ v ts → rlt (rank (den (ianc B v ts) x)) (rank (den (ianc B v ts) y))) → slt Wmp Ψ x y;
  gd_kn x : pt_root x = pt_name B → skn Wmp Ψ x
}.

Definition pc0 : pctx := PCtx 0 0 (λ v ts, v = [] ∧ ts = []).

Lemma good_root Ψ : good Ψ pc0 proot.
Proof.
  assert (∀ x, rooted0 x → den (ianc proot [] []) x = den f0 x) as E.
  { intros x Hx. apply den_root. unfold rooted0 in Hx. rewrite Hx. unfold ianc.
    case_decide as Hd; [done|by exfalso]. }
  split.
  - done.
  - by exists [], [].
  - intros x y Hx Hy H. apply se_w, geq_base. split_and!; [done|done|].
    rewrite <-!E by done. by apply H.
  - intros x y Hx Hy H. apply sl_w, glt_base. split_and!; [done|done|].
    rewrite <-!E by done. by apply H.
  - intros x Hx. left. unfold pt_known. simpl. rewrite Hx. set_solver.
Qed.

Lemma pn_vb_var p a k : pn_root p = NVar a → a < k → pn_vb k p.
Proof. induction p as [c|c|q IH b i|q IH b i]; simpl; [done|intros [=->]; done|exact IH|exact IH]. Qed.

Lemma good_hyp Ψ Θ C m a :
  (∃ v ts, models Θ v ts) → (C, ids m) ∈ Ψ → a < m →
  (∀ g, crel_fact Θ (NVar a) g → bc_facts C g) → bc_env C = [] →
  good Ψ Θ (pvar a).
Proof.
  intros Hinh HΨ Ha HC Henv. destruct C as [env P]. simpl in *. subst env.
  assert (∀ x, pt_root x = NVar a → pt_inst (plist (ids m)) x = x) as Hid
    by (intros x Hx; apply pt_inst_ids; by eapply pn_vb_var).
  assert (length (ids m) = m) as Hl by (unfold ids; by rewrite length_fmap, length_seq).
  assert (∀ x, pt_root x = NVar a → pn_vb (length (ids m)) (pt_name x)) as Hvb
    by (intros x Hx; rewrite Hl; by eapply pn_vb_var).
  split.
  - done.
  - done.
  - intros x y Hx Hy E. eapply (se_hyp0 _ _ _ (ids m) x y); [exact HΨ| |split; by apply Hvb|by apply Hid|by apply Hid].
    apply HC. split_and!; [done|done|]. intros v ts Hv. exact (E v ts Hv).
  - intros x y Hx Hy E. eapply (sl_hyp0 _ _ _ (ids m) x y); [exact HΨ| |split; by apply Hvb|by apply Hid|by apply Hid].
    apply HC. split_and!; [done|done|]. intros v ts Hv. exact (E v ts Hv).
  - intros x Hx. right. exists (BCs [] P), (ids m), (pvar a). split_and!; [done| |done].
    unfold ids. apply list_elem_of_fmap. exists a. split; [done|]. apply elem_of_seq. lia.
Qed.

Lemma good_box Ψ Θ : (∃ v ts, models Θ v ts) → (Crel Θ, ids 1) ∈ Ψ → good Ψ Θ (pvar 0).
Proof. intros Hi H. apply (good_hyp Ψ Θ (Crel Θ) 1 0 Hi H); [lia|done|done]. Qed.

Lemma good_seg Ψ k : (Cseg k, ids 2) ∈ Ψ → good Ψ (Θany k) (pvar 1).
Proof.
  intros H. apply (good_hyp Ψ (Θany k) (Cseg k) 2 1); [by exists [], []|done|lia| |done].
  intros g Hg. by right.
Qed.
