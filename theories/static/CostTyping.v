(** * The cost judgment (lock-freedom plan §19.4, stage H2)

    Θ; Γ ⊢_W e : σ ▷ c ; t ([ctyped W Θ Γ e σ c t]). The judgment sits
    over the terms of lang/Syntax.v beside the typing judgment of
    static/Typing.v and reads no session type. Θ gives the ends of the
    channel constants of e their cost types, Γ is a de Bruijn list of
    optional cost types, c bounds the channel actions of e before it
    returns and t is its ticket transformer (relation/CostTypes.v).

    Every rule is local. Its premises speak about the direct subterms,
    the context and the cost types. A rule that sequences two subterms
    ages the context of the second by the cost of the first ([cage_env])
    and the result of the first by the cost of the second. λ captures
    its context at a floor h and a credit a ([ccap]), application
    charges the arrow's cost, a hand-over keeps one unit to spare
    (C-Send, C-Spawn), a link spends a ticket and a spawn splits them.
    The rules replace the checks of lockfree/Fragment.v except Rank
    and the guard (plan §19.5). Where the rules differ from the text of
    §19.4, plan §19.12 says how and why. *)

From stdpp Require Import base numbers gmap.
From LRGV Require Import lang.Syntax relation.Worlds.
From LRGV Require Export relation.CostTypes.

Set Default Proof Using "All".

(** ** Costs and transformers *)

(** The larger of two costs, ∞ absorbs. *)
Definition fmax (a b : fuel) : fuel :=
  match a, b with
  | Some m, Some n => Some (Nat.max m n)
  | _, _ => None
  end.

(** ⊕, the pointwise bound of two transformers. *)
Definition tmax (t1 t2 : tix) : tix := (fmax t1.1 t2.1, Nat.max t1.2 t2.2).

(** t1 ∘ t2 is sound ([seq_sound]) when t2 needs nothing at 0 or t1
    has a finite slope. *)
Definition tok (t1 t2 : tix) : Prop := snd t2 = 0 ∨ fst t1 ≠ None.

(** A check for t ≤ t′ on the two parameters. *)
Definition tleb (t t' : tix) : bool :=
  match t, t' with
  | (Some s, b), (Some s', b') => Nat.leb s s' && Nat.leb b b'
  | (Some _, b), (None, b') => Nat.leb b b'
  | (None, b), (None, b') => Nat.leb b b'
  | (None, _), (Some _, _) => false
  end.

Lemma tle_refl t : tle t t.
Proof. by intros r tk H. Qed.

Lemma tle_check t t' : tleb t t' = true → tle t t'.
Proof.
  destruct t as [[s|] b], t' as [[s'|] b']; simpl; intros H r tk; unfold meets, tapp.
  - apply andb_true_iff in H as [H1 H2]. apply Nat.leb_le in H1, H2.
    pose proof (Nat.pow_le_mono_r 2 s s' ltac:(lia) H1). nia.
  - apply Nat.leb_le in H. destruct (Nat.eqb r 0) eqn:E; [|done].
    apply Nat.eqb_eq in E as ->. lia.
  - done.
  - apply Nat.leb_le in H. destruct (Nat.eqb r 0); lia.
Qed.

(** ** Protocols and profiles, read at the root *)

(** The budget bound and the action of a node. *)
Definition pnode (P : cpro) : option (nat * cbody) :=
  match P with PNode n b => Some (n, b) | PTop => None end.

(** The protocols at x and x̄ of a profile, for new. *)
Definition pprof (ρ : cprof) : option (cpro * cpro) :=
  match ρ with Prof P Q _ _ => Some (P, Q) | PrTop => None end.

(** The profiles at x[i] and at x + 1. *)
Definition pfld (ρ : cprof) (i : nat) : cprof :=
  match ρ with Prof _ _ f _ => f i | PrTop => PrTop end.
Definition psuc (ρ : cprof) : cprof :=
  match ρ with Prof _ _ _ s => s | PrTop => PrTop end.

(** [pfitpt] of lockfree/LFFuel.v, stated here over the world's three
    functions so that this file does not import the fuel layer. *)
Definition cpfitpt (W : world) : point → cprof → Prop :=
  pfitpt_at (pt_known W) (w_bud W) (w_pc W).

(** ** Subtyping is reflexive *)

Lemma credit_ok_refl τ a : credit_ok τ a τ a.
Proof. destruct τ; simpl; try apply fle_refl; done. Qed.

CoFixpoint cst_ty_refl (τ : cty) : cst_ty τ τ :=
  match τ with
  | CAny => CsAny CAny
  | CVal => CsVal
  | CPt ρ => CsPt ρ ρ (cst_prof_refl ρ)
  | CEnd P => CsEnd P P (cst_pro_refl P)
  | CArr c t h σ1 σ2 =>
      CsArr c t h σ1 σ2 c t h σ1 σ2 (fle_refl c) (tle_refl t) (le_n h) (cst_refl σ1) (cst_refl σ2)
  | CBox c t σ => CsBox c t σ c t σ (fle_refl c) (tle_refl t) (cst_refl σ)
  | CProd σ1 σ2 => CsProd σ1 σ2 σ1 σ2 (cst_refl σ1) (cst_refl σ2)
  | CSum σ1 σ2 => CsSum σ1 σ2 σ1 σ2 (cst_refl σ1) (cst_refl σ2)
  end
with cst_refl (σ : cta) : σ ⊑c σ :=
  match σ with CTa τ a => CsTa τ a τ a (cst_ty_refl τ) (credit_ok_refl τ a) end
with cst_pro_refl (P : cpro) : cst_pro P P :=
  match P with
  | PTop => CsPTop PTop
  | PNode n b => CsPNode n b n b (le_n n) (cst_body_refl b)
  end
with cst_body_refl (b : cbody) : cst_body b b :=
  match b with
  | PSnd σ P => CsBSnd σ P σ P (cst_refl σ) (cst_pro_refl P)
  | PRcv σ P => CsBRcv σ P σ P (cst_refl σ) (cst_pro_refl P)
  | PSel P1 P2 => CsBSel P1 P2 P1 P2 (cst_pro_refl P1) (cst_pro_refl P2)
  | PBra P1 P2 => CsBBra P1 P2 P1 P2 (cst_pro_refl P1) (cst_pro_refl P2)
  | PCls => CsBCls
  end
with cst_prof_refl (ρ : cprof) : cst_prof ρ ρ :=
  match ρ with
  | PrTop => CsRTop PrTop
  | Prof P Q f s =>
      CsRProf P Q f s P Q f s (cst_pro_refl P) (cst_pro_refl Q) (λ i, cst_prof_refl (f i))
        (cst_prof_refl s)
  end.

(** ** Contexts *)

Abbreviation cenv := (list (option cta)).
Abbreviation cthe := (gmap cend cta).

(** An entry whose type holds no end is unlimited. *)
Definition cunl_entry (o : option cta) : Prop :=
  match o with None => True | Some σ => cfree (cta_ty σ) end.

Fixpoint cunlenv (Γ : cenv) : Prop :=
  match Γ with [] => True | o :: Γ => cunl_entry o ∧ cunlenv Γ end.

(** x : σ and nothing else but unlimited entries. *)
Definition conly (Γ : cenv) (x : nat) (σ : cta) : Prop :=
  Γ !! x = Some (Some σ) ∧ cunlenv (<[x := None]> Γ).

(** Γ = Γ1 ⊎ Γ2, an unlimited entry may go to both sides. *)
Inductive csplit : cenv → cenv → cenv → Prop :=
  | SpNil : csplit [] [] []
  | SpNone Γ Γ1 Γ2 : csplit Γ Γ1 Γ2 → csplit (None :: Γ) (None :: Γ1) (None :: Γ2)
  | SpL σ Γ Γ1 Γ2 : csplit Γ Γ1 Γ2 → csplit (Some σ :: Γ) (Some σ :: Γ1) (None :: Γ2)
  | SpR σ Γ Γ1 Γ2 : csplit Γ Γ1 Γ2 → csplit (Some σ :: Γ) (None :: Γ1) (Some σ :: Γ2)
  | SpUnl σ Γ Γ1 Γ2 :
      cfree (cta_ty σ) → csplit Γ Γ1 Γ2 → csplit (Some σ :: Γ) (Some σ :: Γ1) (Some σ :: Γ2).

(** Θ = Θ1 ⊎ Θ2. Ends are never unlimited. *)
Definition thsplit (Θ Θ1 Θ2 : cthe) : Prop := Θ1 ##ₘ Θ2 ∧ Θ = Θ1 ∪ Θ2.

Lemma thsplit_empty : thsplit ∅ ∅ ∅.
Proof. split; [apply map_disjoint_empty_l|by rewrite map_empty_union]. Qed.

(** Weakening drops unlimited entries. *)
Inductive cwk : cenv → cenv → Prop :=
  | WkNil : cwk [] []
  | WkCons o Γ' Γ : cwk Γ' Γ → cwk (o :: Γ') (o :: Γ)
  | WkDrop σ Γ' Γ : cfree (cta_ty σ) → cwk Γ' Γ → cwk (None :: Γ') (Some σ :: Γ).

(** ** Aging (Γ − c)

    [cage] of relation/CostTypes.v, plus one condition. A value at
    [CAny] carries no counter bound ([Vfuel] at [CAny] is [True]), so
    its credit says nothing, and an entry that may hold one ages only
    by 0. [cheld] is the finite evidence that the top of a type is not
    [CAny]. *)
Inductive cheld : cty → Prop :=
  | HdVal : cheld CVal
  | HdPt ρ : cheld (CPt ρ)
  | HdEnd P : cheld (CEnd P)
  | HdArr c t h σ1 σ2 : cheld (CArr c t h σ1 σ2)
  | HdBox c t σ : cheld (CBox c t σ)
  | HdProd τ1 a1 τ2 a2 : cheld τ1 → cheld τ2 → cheld (CProd (CTa τ1 a1) (CTa τ2 a2))
  | HdSum τ1 a1 τ2 a2 : cheld τ1 → cheld τ2 → cheld (CSum (CTa τ1 a1) (CTa τ2 a2)).

Definition cagex (c : fuel) (σ σ' : cta) : Prop := cage c σ σ' ∧ (c = Some 0 ∨ cheld (cta_ty σ)).

Inductive cage_env (c : fuel) : cenv → cenv → Prop :=
  | AeNil : cage_env c [] []
  | AeNone Γ Γ' : cage_env c Γ Γ' → cage_env c (None :: Γ) (None :: Γ')
  | AeSome σ σ' Γ Γ' : cagex c σ σ' → cage_env c Γ Γ' → cage_env c (Some σ :: Γ) (Some σ' :: Γ').

Definition cage_th (c : fuel) (Θ Θ' : cthe) : Prop :=
  ∀ o, match Θ !! o, Θ' !! o with
       | None, None => True
       | Some σ, Some σ' => cagex c σ σ'
       | _, _ => False
       end.

Lemma cage_th_empty c : cage_th c ∅ ∅.
Proof. intros o. by rewrite lookup_empty. Qed.

(** ** Capture (C-Abs)

    [ccap h a σ σ']: the entry σ has current lower bound at least h + a,
    the least lower bound of its ends, and σ' restates it with lower
    bound exactly h. An end gets credit h, a closure with floor h0 ≤ h
    gets credit h − h0, a pair restates its components. An unlimited
    entry stays. This is the side condition "h ≤ low of every entry,
    a = min low − h" of §19.4 together with (·)^h, as one relation. *)
Inductive ccap (h : nat) (a : fuel) : cta → cta → Prop :=
  | CpFree τ a0 : cfree τ → ccap h a (CTa τ a0) (CTa τ a0)
  | CpEnd P a0 : fle (fadd (Some h) a) a0 → ccap h a (CTa (CEnd P) a0) (CTa (CEnd P) (Some h))
  | CpArr c t h0 σ1 σ2 a0 :
      h0 ≤ h → fle (fadd (Some h) a) (fadd (Some h0) a0) →
      ccap h a (CTa (CArr c t h0 σ1 σ2) a0) (CTa (CArr c t h0 σ1 σ2) (Some (h - h0)))
  | CpProd σ1 σ2 σ1' σ2' a0 :
      ccap h a (cadd a0 σ1) σ1' → ccap h a (cadd a0 σ2) σ2' →
      ccap h a (CTa (CProd σ1 σ2) a0) (CTa (CProd σ1' σ2') (Some 0))
  | CpSum σ1 σ2 σ1' σ2' a0 :
      ccap h a (cadd a0 σ1) σ1' → ccap h a (cadd a0 σ2) σ2' →
      ccap h a (CTa (CSum σ1 σ2) a0) (CTa (CSum σ1' σ2') (Some 0)).

Inductive ccap_env (h : nat) (a : fuel) : cenv → cenv → Prop :=
  | CeNil : ccap_env h a [] []
  | CeNone Γ Γ' : ccap_env h a Γ Γ' → ccap_env h a (None :: Γ) (None :: Γ')
  | CeSome σ σ' Γ Γ' : ccap h a σ σ' → ccap_env h a Γ Γ' → ccap_env h a (Some σ :: Γ) (Some σ' :: Γ').

Definition ccap_th (h : nat) (a : fuel) (Θ Θ' : cthe) : Prop :=
  ∀ o, match Θ !! o, Θ' !! o with
       | None, None => True
       | Some σ, Some σ' => ccap h a σ σ'
       | _, _ => False
       end.

Lemma ccap_th_empty h a : ccap_th h a ∅ ∅.
Proof. intros o. by rewrite lookup_empty. Qed.

(** ** Cost signatures of the primitive constants (C-Konst)

    Each constant is a value at an arrow type with an empty map. The
    fuel layer reads no table (plan §19.11, 3). Stage H4 proves for each
    constructor that the constant is in [Vfuel] at its signature. *)
Inductive konst_cost : konst → cty → Prop :=
  | KcForce c t σ a :
      konst_cost KForce (CArr c t 0 (CTa (CBox c t σ) a) σ)
  | KcNew ρ a P Q n b n' b' :
      pprof ρ = Some (P, Q) → pnode P = Some (n, b) → pnode Q = Some (n', b') →
      konst_cost KNew (CArr (Some 0) tid 0 (CTa (CPt ρ) a)
        (CTa (CProd (CTa (CEnd P) (Some n)) (CTa (CEnd Q) (Some n'))) (Some 0)))
  | KcPay i ρ a :
      konst_cost (KPay i) (CArr (Some 0) tid 0 (CTa (CPt ρ) a) (CTa (CPt (pfld ρ i)) None))
  | KcSucc ρ a :
      konst_cost KSucc (CArr (Some 0) tid 0 (CTa (CPt ρ) a) (CTa (CPt (psuc ρ)) None))
  | KcSend σp σp' a a0 P n σ P' n' b' :
      pnode P = Some (n, PSnd σ P') → pnode P' = Some (n', b') →
      cagex (Some 1) (cadd a0 σp) σp' → σp' ⊑c σ →
      konst_cost KSend (CArr (Some 1) tid 0 (CTa (CProd σp (CTa (CEnd P) a)) a0) (CTa (CEnd P') (Some n')))
  | KcRecv a P n σ P' n' b' :
      pnode P = Some (n, PRcv σ P') → pnode P' = Some (n', b') →
      konst_cost KRecv (CArr (Some 1) tid 0 (CTa (CEnd P) a)
        (CTa (CProd σ (CTa (CEnd P') (Some n'))) (Some 0)))
  | KcClos a P n :
      pnode P = Some (n, PCls) →
      konst_cost KClos (CArr (Some 1) tid 0 (CTa (CEnd P) a) (CTa CVal None))
  | KcSel (s : bool) a P n P1 P2 n' b' :
      pnode P = Some (n, PSel P1 P2) → pnode (if s then P2 else P1) = Some (n', b') →
      konst_cost (ksel s) (CArr (Some 1) tid 0 (CTa (CEnd P) a)
        (CTa (CEnd (if s then P2 else P1)) (Some n')))
  | KcBra a P n P1 P2 n1 b1 n2 b2 :
      pnode P = Some (n, PBra P1 P2) → pnode P1 = Some (n1, b1) → pnode P2 = Some (n2, b2) →
      konst_cost KBra (CArr (Some 1) tid 0 (CTa (CEnd P) a)
        (CTa (CSum (CTa (CEnd P1) (Some n1)) (CTa (CEnd P2) (Some n2))) (Some 0)))
  | KcLink P1 a1 P2 a2 a0 :
      konst_cost KLink (CArr (Some 0) (tlink tid) 0
        (CTa (CProd (CTa (CEnd P1) a1) (CTa (CEnd P2) a2)) a0) (CTa CVal None))
  | KcSpawn c' t' h a1 σ' a :
      fle (Some 1) a →
      konst_cost KSpawn (CArr (Some 0) (tspawn (snd t') tid) 0
        (CTa (CArr c' t' h (CTa CVal a1) σ') a) (CTa CVal None)).

(** ** The judgment *)

Inductive ctyped (W : world) : cthe → cenv → expr → cta → fuel → tix → Prop :=
  | C_Unit Γ :
      cunlenv Γ →
      ctyped W ∅ Γ EUnit (CTa CVal None) (Some 0) tid
  | C_Pt Γ x ρ :
      cunlenv Γ → pt_known W x → cpfitpt W x ρ →
      ctyped W ∅ Γ (EPt x) (CTa (CPt ρ) None) (Some 0) tid
  | C_Var Γ x σ :
      conly Γ x σ →
      ctyped W ∅ Γ (Var x) σ (Some 0) tid
  | C_Ch Γ c b σ :
      cunlenv Γ →
      ctyped W {[(c, b) := σ]} Γ (Chan c b) σ (Some 0) tid
  | C_Abs Θ Θh Γ Γh e c t h a σ1 σ2 :
      ccap_th h a Θ Θh → ccap_env h a Γ Γh →
      ctyped W Θh (Some σ1 :: Γh) e σ2 c t →
      ctyped W Θ Γ (Lam e) (CTa (CArr c t h σ1 σ2) a) (Some 0) tid
  | C_App Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e1 e2 c t h σ1 σ2 a1 c1 t1 c2 t2 :
      thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
      ctyped W Θ1 Γ1 e1 (CTa (CArr c t h σ1 σ2) a1) c1 t1 →
      cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' →
      ctyped W Θ2' Γ2' e2 σ1 c2 t2 →
      fle c2 a1 → tok t2 t → tok t1 (tseq t2 t) →
      ctyped W Θ Γ (App e1 e2) σ2 (fadd c1 (fadd c2 c)) (tseq t1 (tseq t2 t))
  | C_Pair Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e1 e2 σ1 σ1' σ2 c1 t1 c2 t2 :
      thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
      ctyped W Θ1 Γ1 e1 σ1 c1 t1 →
      cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' →
      ctyped W Θ2' Γ2' e2 σ2 c2 t2 →
      cagex c2 σ1 σ1' → tok t1 t2 →
      ctyped W Θ Γ (Pair e1 e2) (CTa (CProd σ1' σ2) (Some 0)) (fadd c1 c2) (tseq t1 t2)
  | C_LetU Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e1 e2 a σ c1 t1 c2 t2 :
      thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
      ctyped W Θ1 Γ1 e1 (CTa CVal a) c1 t1 →
      cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' →
      ctyped W Θ2' Γ2' e2 σ c2 t2 →
      tok t1 t2 →
      ctyped W Θ Γ (LetU e1 e2) σ (fadd c1 c2) (tseq t1 t2)
  | C_LetP Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e1 e2 σa σb a σ c1 t1 c2 t2 :
      thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
      ctyped W Θ1 Γ1 e1 (CTa (CProd σa σb) a) c1 t1 →
      cage_th c1 Θ2 Θ2' → cage_env c1 Γ2 Γ2' →
      ctyped W Θ2' (Some (cadd a σb) :: Some (cadd a σa) :: Γ2') e2 σ c2 t2 →
      tok t1 t2 →
      ctyped W Θ Γ (LetP e1 e2) σ (fadd c1 c2) (tseq t1 t2)
  | C_Inj1 Θ Γ e σ1 σ2 c t :
      ctyped W Θ Γ e σ1 c t →
      ctyped W Θ Γ (Inj1 e) (CTa (CSum σ1 σ2) (Some 0)) c t
  | C_Inj2 Θ Γ e σ1 σ2 c t :
      ctyped W Θ Γ e σ2 c t →
      ctyped W Θ Γ (Inj2 e) (CTa (CSum σ1 σ2) (Some 0)) c t
  | C_Case Θ Θ1 Θ2 Θ2' Γ Γ1 Γ2 Γ2' e e1 e2 σa σb a σ c0 t0 c1 t1 c2 t2 :
      thsplit Θ Θ1 Θ2 → csplit Γ Γ1 Γ2 →
      ctyped W Θ1 Γ1 e (CTa (CSum σa σb) a) c0 t0 →
      cage_th c0 Θ2 Θ2' → cage_env c0 Γ2 Γ2' →
      ctyped W Θ2' (Some (cadd a σa) :: Γ2') e1 σ c1 t1 →
      ctyped W Θ2' (Some (cadd a σb) :: Γ2') e2 σ c2 t2 →
      tok t0 (tmax t1 t2) →
      ctyped W Θ Γ (Case e e1 e2) σ (fadd c0 (fmax c1 c2)) (tseq t0 (tmax t1 t2))
  | C_Box Γ e c t σ :
      cunlenv Γ →
      ctyped W ∅ (Some (CTa (CBox c t σ) None) :: Γ) e σ c t →
      ctyped W ∅ Γ (EBox e) (CTa (CBox c t σ) None) (Some 0) tid
  | C_Force Θ Γ e c t σ a c0 t0 :
      ctyped W Θ Γ e (CTa (CBox c t σ) a) c0 t0 →
      tok t0 t →
      ctyped W Θ Γ (App EForce e) σ (fadd c0 c) (tseq t0 t)
  | C_New Θ Γ e ρ a c0 t0 P Q n b n' b' :
      ctyped W Θ Γ e (CTa (CPt ρ) a) c0 t0 →
      pprof ρ = Some (P, Q) → pnode P = Some (n, b) → pnode Q = Some (n', b') →
      ctyped W Θ Γ (App ENew e)
        (CTa (CProd (CTa (CEnd P) (Some n)) (CTa (CEnd Q) (Some n'))) (Some 0)) c0 t0
  | C_Pay Θ Γ e i ρ a c0 t0 :
      ctyped W Θ Γ e (CTa (CPt ρ) a) c0 t0 →
      ctyped W Θ Γ (App (Konst (KPay i)) e) (CTa (CPt (pfld ρ i)) None) c0 t0
  | C_Succ Θ Γ e ρ a c0 t0 :
      ctyped W Θ Γ e (CTa (CPt ρ) a) c0 t0 →
      ctyped W Θ Γ (App (Konst KSucc) e) (CTa (CPt (psuc ρ)) None) c0 t0
  | C_Send Θ Γ e σp σp' a a0 P n σ P' n' b' c0 t0 :
      ctyped W Θ Γ e (CTa (CProd σp (CTa (CEnd P) a)) a0) c0 t0 →
      pnode P = Some (n, PSnd σ P') → pnode P' = Some (n', b') →
      cagex (Some 1) (cadd a0 σp) σp' → σp' ⊑c σ →
      ctyped W Θ Γ (App ESend e) (CTa (CEnd P') (Some n')) (fadd c0 (Some 1)) t0
  | C_Recv Θ Γ e a P n σ P' n' b' c0 t0 :
      ctyped W Θ Γ e (CTa (CEnd P) a) c0 t0 →
      pnode P = Some (n, PRcv σ P') → pnode P' = Some (n', b') →
      ctyped W Θ Γ (App ERecv e) (CTa (CProd σ (CTa (CEnd P') (Some n'))) (Some 0))
        (fadd c0 (Some 1)) t0
  | C_Close Θ Γ e a P n c0 t0 :
      ctyped W Θ Γ e (CTa (CEnd P) a) c0 t0 →
      pnode P = Some (n, PCls) →
      ctyped W Θ Γ (App EClos e) (CTa CVal None) (fadd c0 (Some 1)) t0
  | C_Sel (s : bool) Θ Γ e a P n P1 P2 n' b' c0 t0 :
      ctyped W Θ Γ e (CTa (CEnd P) a) c0 t0 →
      pnode P = Some (n, PSel P1 P2) → pnode (if s then P2 else P1) = Some (n', b') →
      ctyped W Θ Γ (App (Konst (ksel s)) e) (CTa (CEnd (if s then P2 else P1)) (Some n'))
        (fadd c0 (Some 1)) t0
  | C_Bra Θ Γ e a P n P1 P2 n1 b1 n2 b2 c0 t0 :
      ctyped W Θ Γ e (CTa (CEnd P) a) c0 t0 →
      pnode P = Some (n, PBra P1 P2) → pnode P1 = Some (n1, b1) → pnode P2 = Some (n2, b2) →
      ctyped W Θ Γ (App EBra e)
        (CTa (CSum (CTa (CEnd P1) (Some n1)) (CTa (CEnd P2) (Some n2))) (Some 0)) (fadd c0 (Some 1)) t0
  | C_Link Θ Γ e P1 a1 P2 a2 a0 c0 t0 :
      ctyped W Θ Γ e (CTa (CProd (CTa (CEnd P1) a1) (CTa (CEnd P2) a2)) a0) c0 t0 →
      tok t0 (tlink tid) →
      ctyped W Θ Γ (App ELink e) (CTa CVal None) c0 (tseq t0 (tlink tid))
  | C_Spawn Θ Γ e c' t' h a1 σ' a c0 t0 :
      ctyped W Θ Γ e (CTa (CArr c' t' h (CTa CVal a1) σ') a) c0 t0 →
      fle (Some 1) a → tok t0 (tspawn (snd t') tid) →
      ctyped W Θ Γ (App ESpawn e) (CTa CVal None) c0 (tseq t0 (tspawn (snd t') tid))
  | C_Konst Γ k τ :
      cunlenv Γ → konst_cost k τ →
      ctyped W ∅ Γ (Konst k) (CTa τ None) (Some 0) tid
  | C_Sub Θ Γ e σ σ' c c' t t' :
      ctyped W Θ Γ e σ c t → σ ⊑c σ' → fle c c' → tle t t' →
      ctyped W Θ Γ e σ' c' t'
  | C_Weak Θ Γ' Γ e σ c t :
      cwk Γ' Γ → ctyped W Θ Γ' e σ c t →
      ctyped W Θ Γ e σ c t
  | C_Contract Θ Γ σ e σ' c t :
      cfree (cta_ty σ) →
      ctyped W Θ (Some σ :: Some σ :: Γ) e σ' c t →
      ctyped W Θ (Some σ :: Γ) (rename pred e) σ' c t.

(** ** Structural lemmas *)

(** Subsumption on the cost and the transformer alone. *)
Lemma ctyped_mono W Θ Γ e σ c c' t t' :
  ctyped W Θ Γ e σ c t → fle c c' → tle t t' → ctyped W Θ Γ e σ c' t'.
Proof. intros H Hc Ht. eapply C_Sub; [exact H|apply cst_refl|done|done]. Qed.

(** An unlimited context weakens to the empty one. *)
Lemma cwk_refl Γ : cwk Γ Γ.
Proof. induction Γ; constructor; done. Qed.

(** Aging by 0 changes nothing. *)
Lemma cagex_zero σ : cagex (Some 0) σ σ.
Proof.
  destruct σ as [τ a]. split; [|by left].
  assert (cage (Some 0) (CTa τ a) (CTa τ (fsub a (Some 0)))) as Hc.
  { constructor. destruct a; simpl; lia. }
  destruct a; simpl in Hc; [rewrite Nat.sub_0_r in Hc|]; exact Hc.
Qed.

Lemma cage_env_zero Γ : cage_env (Some 0) Γ Γ.
Proof. induction Γ as [|[σ|] Γ IH]; constructor; [apply cagex_zero| |]; done. Qed.

(** ** Tactics for derivations

    [ct H] builds a derivation goal-directed. A goal whose cost type has
    no existential variable is checked: λ and boxes by their rules,
    every other term by C-Sub over an inferred derivation. The hint H
    handles the goals that need information the term does not carry,
    the floor and credit of a λ in inference mode. *)

Fixpoint fvb (i : nat) (e : expr) : bool :=
  match e with
  | Var x => Nat.eqb x i
  | EUnit | Konst _ | Chan _ _ | EPt _ => false
  | Lam e | EBox e => fvb (S i) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => fvb i e1 || fvb i e2
  | LetP e1 e2 => fvb i e1 || fvb (S (S i)) e2
  | Inj1 e | Inj2 e => fvb i e
  | Case e e1 e2 => fvb i e || fvb (S i) e1 || fvb (S i) e2
  end.

Ltac cfree_tac := cbn [cta_ty cadd]; solve [repeat constructor].

Ltac fle_tac := first [apply fle_refl | cbn [fle fadd fsub fmax cta_cr cadd]; first [exact I | lia]].

Ltac tle_tac := first [apply tle_refl | apply tle_check; vm_compute; reflexivity].

Ltac tok_tac := unfold tok; first [left; vm_compute; reflexivity | right; vm_compute; discriminate].

Ltac cunl_tac := cbn [cunlenv cunl_entry cta_ty]; solve [repeat split; repeat constructor].

Ltac conly_tac := split; [reflexivity|cbn [insert list_insert]; cunl_tac].

Ltac csplit_go i e1 e2 :=
  lazymatch goal with
  | |- csplit [] _ _ => apply SpNil
  | |- csplit (None :: _) _ _ => apply SpNone; csplit_go (S i) e1 e2
  | |- csplit (Some ?σ :: _) _ _ =>
      let b1 := eval vm_compute in (fvb i e1) in
      let b2 := eval vm_compute in (fvb i e2) in
      lazymatch b1 with
      | true =>
          lazymatch b2 with
          | true => apply SpUnl; [cfree_tac|csplit_go (S i) e1 e2]
          | false => apply SpL; csplit_go (S i) e1 e2
          end
      | false =>
          lazymatch b2 with
          | true => apply SpR; csplit_go (S i) e1 e2
          | false => first [apply SpUnl; [solve [cfree_tac]|] | apply SpL]; csplit_go (S i) e1 e2
          end
      end
  end.

Ltac csplit_tac e1 e2 := csplit_go 0 e1 e2.

Ltac cheld_tac := cbn [cta_ty cadd]; solve [repeat constructor].

Ltac cagex_tac :=
  split; [first [apply AgeFree; solve [cfree_tac] | apply AgeCredit; fle_tac]
         |first [left; reflexivity | right; cheld_tac]].

Ltac age_tac :=
  lazymatch goal with
  | |- cage_th _ ∅ _ => apply cage_th_empty
  | |- cage_env _ [] _ => apply AeNil
  | |- cage_env _ (None :: _) _ => apply AeNone; age_tac
  | |- cage_env _ (Some _ :: _) _ => apply AeSome; [cagex_tac|age_tac]
  end.

Ltac ccap1_tac :=
  lazymatch goal with
  | |- ccap _ _ (CTa ?τ _) _ =>
      first [apply CpFree; solve [cfree_tac]
            | apply CpEnd; fle_tac
            | apply CpArr; [lia|fle_tac]
            | apply CpProd; cbn [cadd fadd]; ccap1_tac
            | apply CpSum; cbn [cadd fadd]; ccap1_tac]
  end.

Ltac ccap_tac :=
  lazymatch goal with
  | |- ccap_th _ _ ∅ _ => apply ccap_th_empty
  | |- ccap_env _ _ [] _ => apply CeNil
  | |- ccap_env _ _ (None :: _) _ => apply CeNone; ccap_tac
  | |- ccap_env _ _ (Some _ :: _) _ => apply CeSome; [ccap1_tac|ccap_tac]
  end.

Ltac pnode_tac := reflexivity.

(** Subtyping between concrete cost types: refl where it applies,
    otherwise structure by structure with the credits by arithmetic. *)
Ltac cst_tac :=
  first
    [ apply cst_refl
    | apply cst_any
    | lazymatch goal with
      | |- cst (CTa _ _) (CTa _ _) => apply CsTa; [cst_ty_tac|cbn [credit_ok fadd fle]; first [exact I|lia]]
      end ]
with cst_ty_tac :=
  first
    [ apply cst_ty_refl
    | apply CsAny
    | apply CsProd; cst_tac
    | apply CsSum; cst_tac
    | apply CsEnd; first [apply cst_pro_refl | apply CsPTop]
    | apply CsArr; [fle_tac|tle_tac|lia|cst_tac|cst_tac]
    | apply CsBox; [fle_tac|tle_tac|cst_tac] ].

Ltac ct_simpl :=
  lazymatch goal with
  | |- ctyped ?W ?Θ ?Γ ?e ?σ ?c ?t =>
      let Γ' := eval simpl in Γ in change (ctyped W Θ Γ' e σ c t)
  end.

Ltac has_evar_ty σ := has_evar σ.

(** One step in inference mode. *)
Ltac ct_infer H :=
  ct_simpl;
  lazymatch goal with
  | |- ctyped _ _ _ ?e _ _ _ =>
  first [ H ltac:(ct H) |
  lazymatch e with
  | EUnit => apply C_Unit; cunl_tac
  | Var _ => apply C_Var; conly_tac
  | EPt _ => apply C_Pt; [cunl_tac|eassumption|eassumption]
  | App (Konst KSend) _ => eapply C_Send; [ct H|pnode_tac|pnode_tac|cagex_tac|cst_tac]
  | App (Konst KRecv) _ => eapply C_Recv; [ct H|pnode_tac|pnode_tac]
  | App (Konst KClos) _ => eapply C_Close; [ct H|pnode_tac]
  | App (Konst KBra) _ => eapply C_Bra; [ct H|pnode_tac|pnode_tac|pnode_tac]
  | App (Konst KSel1) _ => eapply (C_Sel false); [ct H|pnode_tac|pnode_tac]
  | App (Konst KSel2) _ => eapply (C_Sel true); [ct H|pnode_tac|pnode_tac]
  | App (Konst KLink) _ => eapply C_Link; [ct H|tok_tac]
  | App (Konst KSpawn) _ => eapply C_Spawn; [ct H|fle_tac|tok_tac]
  | App (Konst KNew) _ => eapply C_New; [ct H|pnode_tac|pnode_tac|pnode_tac]
  | App (Konst (KPay _)) _ => eapply C_Pay; ct H
  | App (Konst KSucc) _ => eapply C_Succ; ct H
  | App (Konst KForce) _ => eapply C_Force; [ct H|tok_tac]
  | App ?e1 ?e2 =>
      eapply C_App; [apply thsplit_empty|csplit_tac e1 e2|ct H|age_tac|age_tac|ct H
                    |fle_tac|tok_tac|tok_tac]
  | Pair ?e1 ?e2 =>
      eapply C_Pair; [apply thsplit_empty|csplit_tac e1 e2|ct H|age_tac|age_tac|ct H
                     |cagex_tac|tok_tac]
  | LetU ?e1 ?e2 =>
      eapply C_LetU; [apply thsplit_empty|csplit_tac e1 e2|ct H|age_tac|age_tac|ct H|tok_tac]
  | LetP ?e1 ?e2 =>
      eapply C_LetP; [apply thsplit_empty|csplit_tac e1 (Lam (Lam e2))|ct H|age_tac|age_tac|ct H|tok_tac]
  | Case ?e0 ?e1 ?e2 =>
      eapply C_Case; [apply thsplit_empty|csplit_tac e0 (LetU (Lam e1) (Lam e2))|ct H|age_tac|age_tac|ct H|ct H
                     |tok_tac]
  end ]
  end
(** A goal, checked when its type is known. *)
with ct H :=
  ct_simpl;
  lazymatch goal with
  | |- ctyped ?W ?Θ ?Γ ?e ?σ ?c ?t =>
      tryif has_evar σ then ct_infer H else
      first [ H ltac:(ct H) |
      lazymatch e with
      | Lam _ =>
          eapply (C_Sub W Θ Γ e σ σ); [eapply C_Abs; [ccap_tac|ccap_tac|ct H]|apply cst_refl
                                      |fle_tac|tle_tac]
      | EBox _ =>
          eapply (C_Sub W Θ Γ e σ σ); [eapply C_Box; [cunl_tac|ct H]|apply cst_refl|fle_tac|tle_tac]
      | _ => eapply (C_Sub W Θ Γ e _ σ); [ct_infer H|cst_tac|fle_tac|tle_tac]
      end ]
  end.

(** The default hint: none. *)
Ltac nohint k := fail.

(** A λ in inference mode at floor h and credit a, with argument σ1. *)
Ltac ct_abs h a σ1 k :=
  eapply (C_Abs _ _ _ _ _ _ _ _ h a σ1); [ccap_tac|ccap_tac|k].

(** The least current lower bound of the entries of a context, for the
    floor of a spawned λ. Entries other than ends and closures count as
    unlimited; [ccap] checks the choice. *)
Definition omin (a b : fuel) : fuel :=
  match a, b with
  | Some m, Some n => Some (Nat.min m n)
  | Some m, None => Some m
  | None, b => b
  end.

Ltac entry_low σ :=
  lazymatch σ with
  | CTa (CEnd _) ?a => a
  | CTa (CArr _ _ ?h0 _ _) ?a => let l := eval cbn in (fadd (Some h0) a) in l
  | CTa _ _ => constr:(@None nat)
  end.

Ltac env_low Γ :=
  lazymatch Γ with
  | [] => constr:(@None nat)
  | None :: ?Γ' => env_low Γ'
  | Some ?σ :: ?Γ' =>
      let l := env_low Γ' in
      let m := entry_low σ in
      let r := eval cbn in (omin m l) in r
  end.

(** A spawned thunk λu. e captures its context at the largest floor
    that leaves it one unit of credit, which C-Spawn asks. *)
Ltac spawn_hint k :=
  lazymatch goal with
  | |- ctyped _ _ ?Γ (Lam _) (CTa (CArr _ _ _ (CTa CVal _) _) _) _ _ =>
      let l := env_low Γ in
      lazymatch l with
      | Some ?n => let h := eval cbn in (n - 1) in ct_abs h (Some 1) (CTa CVal None) k
      | None => ct_abs 0 (@None nat) (CTa CVal None) k
      end
  end.

Ltac ct0 := ct spawn_hint.

(** Normalise the term of the goal (the encoded lets rename). *)
Ltac ct_prep :=
  lazymatch goal with
  | |- ctyped ?W ?Θ ?Γ ?e ?σ ?c ?t => let e' := eval cbn in e in change (ctyped W Θ Γ e' σ c t)
  end.
