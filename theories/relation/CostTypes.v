(** * Cost types (lock-freedom plan §19.3)

    The fuel layer (lockfree/LFFuel.v) observes points, counters,
    tickets and the world data keyed by points. A cost type records
    exactly that about a value. A closure type [CArr c t h σ1 σ2] bounds
    the channel actions of the body before it returns ([c]), the tickets
    it needs ([t], a ticket transformer) and the floor of the counters
    it captures ([h]). An end type [CEnd P] gives the protocol of
    payload cost types and budget bounds along the end's positions, and
    a point type [CPt ρ] the protocols at a point and its successors. A
    cost type with a credit, [CTa τ a], says how far the counters of
    the ends inside lie above their floors.

    The types are coinductive, because protocols are infinite. The fuel
    relation recurses on values, never on cost types. Nothing here reads
    a session type or a term. The world record (relation/Worlds.v) keeps
    a payload cost type per carrier point ([w_pc]), so this file comes
    before it, and [pfits_at] is stated over the three world functions
    it reads. *)

From stdpp Require Import base numbers.
From LRGV Require Import lang.Syntax.

(** ** Counters *)

(** A counter, a cost or a credit. [None] is ∞. *)
Abbreviation fuel := (option nat).

(** The order on counters, with ∞ on top. *)
Definition fle (a b : fuel) : Prop :=
  match a, b with
  | _, None => True
  | None, Some _ => False
  | Some m, Some n => m ≤ n
  end.

(** One unit less. ∞ stays ∞. *)
Definition ftick (f : fuel) : fuel := (λ m, m - 1) <$> f.

(** Sum, ∞ absorbs. *)
Definition fadd (a b : fuel) : fuel :=
  match a, b with
  | Some m, Some n => Some (m + n)
  | _, _ => None
  end.

(** a − c, used where [fle c a]. ∞ − c = ∞. *)
Definition fsub (a c : fuel) : fuel :=
  match a, c with
  | None, _ => None
  | Some m, Some n => Some (m - n)
  | Some _, None => Some 0
  end.

Lemma fle_refl f : fle f f.
Proof. destruct f; simpl; lia. Qed.

Lemma fle_tick f g : fle f g → fle (ftick f) g.
Proof. destruct f, g; simpl; lia. Qed.

Lemma fle_trans a b c : fle a b → fle b c → fle a c.
Proof. destruct a, b, c; simpl; lia. Qed.

(** ** Ticket transformers (scratch file Tix.v of §19)

    t = (s, b) stands for r ↦ 2^s·r + b; s = None is ∞ with ∞·0 = 0.
    A closure with transformer t runs at every ticket count tk ≥ t(r)
    and returns holding at least r tickets. *)
Definition tix := (fuel * nat)%type.

Definition tapp (t : tix) (r : nat) : fuel :=
  match t with
  | (Some s, b) => Some (2 ^ s * r + b)
  | (None, b) => if Nat.eqb r 0 then Some b else None
  end.

(** tk meets the need of t at r. *)
Definition meets (t : tix) (r tk : nat) : Prop :=
  match tapp t r with Some m => m ≤ tk | None => False end.

(** The identity, r ↦ r. *)
Definition tid : tix := (Some 0, 0).

(** t ≤ t′: whatever meets t′ meets t. *)
Definition tle (t t' : tix) : Prop := ∀ r tk, meets t' r tk → meets t r tk.

(** Spawn: the child gets ⌈tk/2⌉ and needs bc, the parent gets ⌊tk/2⌋
    and needs t at r. *)
Definition tspawn (bc : nat) (t : tix) : tix :=
  match t with
  | (Some s, b) => (Some (S s), Nat.max (2 * b) (2 * bc - 1))
  | (None, b) => (None, Nat.max (2 * b) (2 * bc - 1))
  end.

Lemma spawn_split bc t r tk :
  meets (tspawn bc t) r tk → bc ≤ Nat.div2 (S tk) ∧ meets t r (Nat.div2 tk).
Proof.
  rewrite !Nat.div2_div.
  destruct t as [[s|] b]; cbv beta iota zeta delta [meets tspawn tapp].
  - intros H. assert (2 ^ S s = 2 * 2 ^ s) as E by (rewrite Nat.pow_succ_r'; lia). rewrite E in H. split.
    + apply Nat.div_le_lower_bound; lia.
    + apply Nat.div_le_lower_bound; [lia|]. nia.
  - destruct (Nat.eqb r 0) eqn:E; [|done]. intros H. split;
      apply Nat.div_le_lower_bound; lia.
Qed.

(** Link: one ticket, then t at r. *)
Definition tlink (t : tix) : tix := (fst t, snd t + 1).

Lemma link_split t r tk : meets (tlink t) r tk → 1 ≤ tk ∧ meets t r (tk - 1).
Proof.
  destruct t as [[s|] b]; unfold meets, tlink, tapp; simpl.
  - lia.
  - destruct (Nat.eqb r 0); lia.
Qed.

(** Sequencing: first t1 then t2, (t1 ∘ t2) r = t1 (t2 r). *)
Definition tseq (t1 t2 : tix) : tix :=
  match t1, t2 with
  | (Some s1, b1), (Some s2, b2) => (Some (s1 + s2), 2 ^ s1 * b2 + b1)
  | (Some s1, b1), (None, b2) => (None, 2 ^ s1 * b2 + b1)
  | (None, b1), (Some _, 0) => (None, b1)
  | (None, b1), (None, 0) => (None, b1)
  | (None, b1), (_, S _) => (None, b1 + 1)
  end.

(** Sequencing is sound where it is defined usefully. *)
Lemma seq_sound t1 t2 r tk :
  snd t2 = 0 ∨ fst t1 ≠ None →
  meets (tseq t1 t2) r tk → ∃ r', meets t1 r' tk ∧ meets t2 r r'.
Proof.
  destruct t1 as [[s1|] b1], t2 as [[s2|] b2]; unfold meets, tseq, tapp; simpl; intros Hc H.
  - exists (2 ^ s2 * r + b2). split; [|lia].
    rewrite Nat.pow_add_r in H. nia.
  - destruct (Nat.eqb r 0) eqn:E; [|done]. exists b2. split; lia.
  - destruct Hc as [->|Hc]; [|done].
    destruct (Nat.eqb r 0) eqn:E; [|done]. apply Nat.eqb_eq in E as ->.
    exists 0. simpl. split; [done|lia].
  - destruct Hc as [->|Hc]; [|done].
    destruct (Nat.eqb r 0) eqn:E; [|done]. apply Nat.eqb_eq in E as ->.
    exists 0. simpl. split; [done|lia].
Qed.

(** A box that links once per round and calls itself in tail position
    has no transformer with a finite need at r = 0 (C3). *)
Lemma link_loop_no_tix (t : tix) :
  (∀ tk, meets t 0 tk → meets (tlink t) 0 tk) → ∀ tk, ¬ meets t 0 tk.
Proof.
  intros H tk Hm. revert Hm. induction tk as [tk IH] using lt_wf_ind. intros Hm.
  pose proof (link_split t 0 tk (H tk Hm)) as [H1 H2].
  apply (IH (tk - 1)); [lia|done].
Qed.

(** ** Cost types *)

CoInductive cty :=
  | CAny                                     (* any value, the result of a thread *)
  | CVal                                     (* the unit *)
  | CPt (ρ : cprof)                          (* a point value whose point fits ρ *)
  | CEnd (P : cpro)                          (* an end whose positions fit P *)
  | CArr (c : fuel) (t : tix) (h : nat) (σ1 σ2 : cta)
  | CBox (c : fuel) (t : tix) (σ : cta)
  | CProd (σ1 σ2 : cta)
  | CSum (σ1 σ2 : cta)
with cta :=
  | CTa (τ : cty) (a : fuel)                 (* τ^a, a is the credit *)
with cpro :=                                 (* a protocol node at the current position *)
  | PNode (n : nat) (b : cbody)
  | PTop
with cbody :=
  | PSnd (σ : cta) (P : cpro)
  | PRcv (σ : cta) (P : cpro)
  | PSel (P1 P2 : cpro)
  | PBra (P1 P2 : cpro)
  | PCls
with cprof :=                                (* protocols at x and x̄, profiles at x[i] and x + 1 *)
  | Prof (P Q : cpro) (fld : nat → cprof) (suc : cprof)
  | PrTop.

(** The cost type of a thread: anything, at credit ∞. *)
Definition cany : cta := CTa CAny None.

(** The credit and the type. *)
Definition cta_ty (σ : cta) : cty := match σ with CTa τ _ => τ end.
Definition cta_cr (σ : cta) : fuel := match σ with CTa _ a => a end.

(** Credit a added to σ, for the components of a pair. *)
Definition cadd (a : fuel) (σ : cta) : cta :=
  match σ with CTa τ a' => CTa τ (fadd a a') end.

(** ** Subtyping

    On arrows and boxes the cost c and the transformer t are covariant,
    the floor h is covariant, the argument contravariant and the result
    covariant. On credits, σ^a ⊑ σ'^a' asks the current lower bound not
    to rise: h' + a' ≤ h + a at a closure, a' ≤ a elsewhere. Protocols:
    a node's budget bound may fall, a send payload is contravariant, a
    receive payload covariant. *)
Definition credit_ok (τ : cty) (a : fuel) (τ' : cty) (a' : fuel) : Prop :=
  match τ', τ with
  | CAny, _ => True
  | CArr _ _ h' _ _, CArr _ _ h _ _ => fle (fadd (Some h') a') (fadd (Some h) a)
  | _, _ => fle a' a
  end.

CoInductive cst_ty : cty → cty → Prop :=
  | CsAny τ : cst_ty τ CAny
  | CsVal : cst_ty CVal CVal
  | CsPt ρ ρ' : cst_prof ρ ρ' → cst_ty (CPt ρ) (CPt ρ')
  | CsEnd P P' : cst_pro P P' → cst_ty (CEnd P) (CEnd P')
  | CsArr c t h σ1 σ2 c' t' h' σ1' σ2' :
      fle c c' → tle t t' → h ≤ h' → cst σ1' σ1 → cst σ2 σ2' →
      cst_ty (CArr c t h σ1 σ2) (CArr c' t' h' σ1' σ2')
  | CsBox c t σ c' t' σ' :
      fle c c' → tle t t' → cst σ σ' → cst_ty (CBox c t σ) (CBox c' t' σ')
  | CsProd σ1 σ2 σ1' σ2' : cst σ1 σ1' → cst σ2 σ2' → cst_ty (CProd σ1 σ2) (CProd σ1' σ2')
  | CsSum σ1 σ2 σ1' σ2' : cst σ1 σ1' → cst σ2 σ2' → cst_ty (CSum σ1 σ2) (CSum σ1' σ2')
with cst : cta → cta → Prop :=
  | CsTa τ a τ' a' : cst_ty τ τ' → credit_ok τ a τ' a' → cst (CTa τ a) (CTa τ' a')
with cst_pro : cpro → cpro → Prop :=
  | CsPTop P : cst_pro P PTop
  | CsPNode n b n' b' : n' ≤ n → cst_body b b' → cst_pro (PNode n b) (PNode n' b')
with cst_body : cbody → cbody → Prop :=
  | CsBSnd σ P σ' P' : cst σ' σ → cst_pro P P' → cst_body (PSnd σ P) (PSnd σ' P')
  | CsBRcv σ P σ' P' : cst σ σ' → cst_pro P P' → cst_body (PRcv σ P) (PRcv σ' P')
  | CsBSel P1 P2 P1' P2' : cst_pro P1 P1' → cst_pro P2 P2' → cst_body (PSel P1 P2) (PSel P1' P2')
  | CsBBra P1 P2 P1' P2' : cst_pro P1 P1' → cst_pro P2 P2' → cst_body (PBra P1 P2) (PBra P1' P2')
  | CsBCls : cst_body PCls PCls
with cst_prof : cprof → cprof → Prop :=
  | CsRTop ρ : cst_prof ρ PrTop
  | CsRProf P Q f s P' Q' f' s' :
      cst_pro P P' → cst_pro Q Q' → (∀ i, cst_prof (f i) (f' i)) → cst_prof s s' →
      cst_prof (Prof P Q f s) (Prof P' Q' f' s').

Notation "σ ⊑c σ'" := (cst σ σ') (at level 70).

(** Everything is below the thread type. *)
Lemma cst_any σ : σ ⊑c cany.
Proof. destruct σ as [τ a]. constructor; [constructor|done]. Qed.

(** ** Aging (Γ − c of §19.4)

    An entry without ends is unchanged. An entry with possible ends
    needs credit at least c and loses c of it. At c = ∞ it needs credit
    ∞. [cfree] is finite evidence that a type holds no end. *)
Inductive cfree : cty → Prop :=
  | CfVal : cfree CVal
  | CfPt ρ : cfree (CPt ρ)
  | CfBox c t σ : cfree (CBox c t σ)
  | CfProd τ1 a1 τ2 a2 : cfree τ1 → cfree τ2 → cfree (CProd (CTa τ1 a1) (CTa τ2 a2))
  | CfSum τ1 a1 τ2 a2 : cfree τ1 → cfree τ2 → cfree (CSum (CTa τ1 a1) (CTa τ2 a2)).

Inductive cage (c : fuel) : cta → cta → Prop :=
  | AgeFree τ a : cfree τ → cage c (CTa τ a) (CTa τ a)
  | AgeCredit τ a : fle c a → cage c (CTa τ a) (CTa τ (fsub a c)).

(** ** Fitting a protocol at a point

    [pfits_at kn bud pc x P]: at every depth, each node of P sits at a
    point the world knows ([kn]), its budget bound lies below the
    budget at that point ([bud]), the partner's budget is finite, and a
    payload fits the payload cost type at the carrier point ([pc]): the
    sender's payload lies below it, the receiver reads it at the
    sender's point. lockfree/LFFuel.v instantiates the three functions
    with those of a world ([pfits], [pfitpt]). *)
Section fits.
  Context (kn : point → Prop) (bud : point → fuel) (pc : point → cta).

  CoInductive pfits_at : point → cpro → Prop :=
    | PfTop x : pfits_at x PTop
    | PfNode x n b :
        kn x → fle (Some n) (bud x) → bud (pt_dual x) ≠ None → pfits_body x b →
        pfits_at x (PNode n b)
  with pfits_body : point → cbody → Prop :=
    | PfSnd x σ P : σ ⊑c pc x → pfits_at (pt_shift 1 x) P → pfits_body x (PSnd σ P)
    | PfRcv x σ P : pc (pt_dual x) ⊑c σ → pfits_at (pt_shift 1 x) P → pfits_body x (PRcv σ P)
    | PfSel x P1 P2 :
        pfits_at (sel_pt x false) P1 → pfits_at (sel_pt x true) P2 → pfits_body x (PSel P1 P2)
    | PfBra x P1 P2 :
        pfits_at (bra_pt x false) P1 → pfits_at (bra_pt x true) P2 → pfits_body x (PBra P1 P2)
    | PfCls x : pfits_body x PCls.

  CoInductive pfitpt_at : point → cprof → Prop :=
    | PfPrTop x : pfitpt_at x PrTop
    | PfProf x P Q f s :
        pfits_at x P → pfits_at (pt_dual x) Q →
        (∀ i, pfitpt_at (pt_payload x i) (f i)) → pfitpt_at (pt_shift 1 x) s →
        pfitpt_at x (Prof P Q f s).
End fits.
