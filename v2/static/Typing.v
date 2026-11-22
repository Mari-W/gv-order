(** * The one typing judgment (stage S2, proposal §2.17, decision Q11)

    Θ ; Γ ; Δ ⊢^F_{W,N} e : T ▷ c        [typed W N Θ Γ Δ F e T c]

    One judgment for session types and costs. The readiness and future
    premises are those of the old static typing (theories/static/Typing.v),
    the cost premises those of the old cost judgment
    (theories/static/CostTyping.v). N bounds the tickets of the two ends
    of every channel, tk(o) + tk(ō) ≤ N. An end of type (S@x)^a_m has m
    tickets and credit a ≤ m, an action returns its end at credit m, and
    E-Link asks a1 + m2 > N and a2 + m1 > N ([lgt]). A new channel, at a
    fresh root or at a field, starts its ends at any tickets m1 and m2
    with m1 + m2 ≤ N ([tsum_ok]). Deadlock-freedom typing is
    the instance N = ∞ ([conservative] in static/Conservativity.v).

    No program mentions a point. Plain [new] creates at a fresh root ρ
    with a constraint C under (wf-new) and returns the pair under ∃ρ. C
    (E-New), or at a field x·κ of any point x (E-New-Field). A field
    creation picks no constraint, because the facts about x·κ were fixed
    with the root of x, so its existential would bind nothing and assume
    only what Γ entails. Every
    primitive has its own rule (E-Send, …, E-Force). A constant k passed as
    a function is its eta-expansion λy. k y, which types by E-Abs over the
    rule of k (static/Constants.v).

    A session type enters a derivation only contractive ([scontr],
    types/Contractive.v). E-New asks it of its protocol, E-Abs of the
    argument, E-Inj of the sum, E-Box of the result, P-Term of its ends,
    and E-Sub asks the target contractive when the source is. Over
    contractive contexts every derived type is contractive
    ([typed_scontr]), and a derivation instantiated at contractive
    instances is a derivation ([typed_sinst], static/Sinst.v).

    Arrows are generalized (entry 12 of docs/redesign/pending.md). The
    upper point is a point, none, or ⊤, and E-App asks ⊤ ≺ F only of the
    empty future ([ub_below_u]). The lower point is a point, none, or ⊥,
    and E-Abs asks nothing of ⊥, which [hbot] then reports, so such a
    closure is never a payload. spawn (λe) types by E-Abs at (⊤, ⊥)
    followed by E-Spawn ([e_spawn_lam], static/Weakening.v).

    [dftyped] is the deadlock-freedom projection, Θ ; Γ ; Δ ⊢^F_W e : T,
    defined as the instance N = ∞ with the annotations of N = ∞. Its
    rules [d_*] (static/Conservativity.v) are those of the merged
    judgment without the cost premises and without aging and capture.
    No rule matches the shape of a redex. let x = e1 in e2 is
    the derived form [ELet] of lang/Syntax.v, and E-Let and D-Let are
    admissible ([e_let] and [d_let] in static/Weakening.v). [ptyped] is process typing with P-Term and P-Connect
    in the hidden form. The world of a process judgment lives on the
    constants of its interface, and P-Connect compares the two interface
    orders. [fptyped] keeps the whole world of every derivation. It is
    the target of the soundness of hiding (static/Hiding.v), and every
    derivation sits over a well-founded world ([ptyped_wf],
    [fptyped_wf]). *)

From GV Require Export static.Consts.

Inductive typed (W : sworld) (N : fuel) :
    tenv → hctx → lenv → sfuture → expr → ty → fuel → Prop :=
  | e_unit Γ Δ F :
      lenv_unl Δ →
      typed W N ∅ Γ Δ F EUnit TUnit (Some 0)
  | e_var Γ Δ F x T :
      lenv_only Δ x T →
      typed W N ∅ Γ Δ F (Var x) T (Some 0)
  | e_chan Γ Δ F o S x a m :
      lenv_unl Δ →
      typed W N {[o := TE S x a m]} Γ Δ F (Chan o) (TSess S x a m) (Some 0)
  | e_abs Θ Θh Γ Δ Δh F e T U ub lb c a :
      lbx_below_h W Γ lb (tenv_heads Θ ∪ lenv_heads Δ) (lenv_bot Δ) →
      thage a Θ Θh → lage a Δ Δh → tcontr T →
      typed W N Θh Γ (Some T :: Δh) (abs_fut ub) e U c →
      typed W N Θ Γ Δ F (Lam e) (TLolli ub lb c T U a) (Some 0)
  | e_app Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c T U a1 c1 c2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below_u W Γ ub F →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1
        (TLolli ub lb c T U a1) c1 →
      thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
      typed W N Θ2' Γ Δ2' (sf_unionb F (lb_heads lb) (lb_bot lb)) e2 T c2 →
      fle c2 a1 →
      typed W N Θ Γ Δ F (App e1 e2) U (fadd c1 (fadd c2 c))
  | e_pair Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T1' T2 c1 c2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 c1 →
      thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
      typed W N Θ2' Γ Δ2' (sf_unionb F (heads T1) (hbot T1)) e2 T2 c2 →
      tage c2 T1 T1' →
      typed W N Θ Γ Δ F (Pair e1 e2) (TProd T1' T2) (fadd c1 c2)
  | e_letu Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T c1 c2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit c1 →
      thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
      typed W N Θ2' Γ Δ2' F e2 T c2 →
      typed W N Θ Γ Δ F (LetU e1 e2) T (fadd c1 c2)
  | e_letp Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T2 T c1 c2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1
        (TProd T1 T2) c1 →
      thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
      typed W N Θ2' Γ (Some T2 :: Some T1 :: Δ2') F e2 T c2 →
      typed W N Θ Γ Δ F (LetP e1 e2) T (fadd c1 c2)
  | e_inj (i : bool) Θ Γ Δ F e T U c :
      tcontr (TSum T U) →
      typed W N Θ Γ Δ F e (if i then U else T) c →
      typed W N Θ Γ Δ F (Inj i e) (TSum T U) c
  | e_case Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e e1 e2 T1 T2 T c0 c1 c2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e
        (TSum T1 T2) c0 →
      thage c0 Θ2 Θ2' → lage c0 Δ2 Δ2' →
      typed W N Θ2' Γ (Some T1 :: Δ2') F e1 T c1 →
      typed W N Θ2' Γ (Some T2 :: Δ2') F e2 T c2 →
      typed W N Θ Γ Δ F (Case e e1 e2) T (fadd c0 (fmax c1 c2))
  | e_box Γ Δ F e m k C ub c U :
      lenv_unl Δ → tcontr U →
      (∀ ss, length ss = k → sinsts N ss →
         typed W N ∅ (hc_open m C Γ)
           (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ))
           (∅, Some (FRest (rest_of ub))) e (sinst_ty (slist ss) U) c) →
      typed W N ∅ Γ Δ F (EBox e) (TBox m k C ub c U) (Some 0)
  | e_force Θ Γ Δ F e m k C ub c U xs ss c0 :
      length xs = m → hold_at W Γ C xs → length ss = k → sinsts N ss →
      ub_below_s W Γ (pt_inst (plist xs) <$> ub) F →
      typed W N Θ Γ Δ F e (TBox m k C ub c U) c0 →
      typed W N Θ Γ Δ F (EForce e) (sinst_ty (slist ss) (ty_inst xs U)) (fadd c0 c)
  | e_send Θ Γ Δ F e S0 x m T S aS mS Tp Tp' c0 :
      unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → hbot T = false →
      (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TProd Tp (TSess S0 x aS mS)) c0 →
      tage (Some 1) Tp Tp' → tsub W Γ Tp' (payload_at m T x) →
      typed W N Θ Γ Δ F (ESend e) (TSess S x⁺ mS mS) (fadd c0 (Some 1))
  | e_recv Θ Γ Δ F e S0 x m T S a mS c0 :
      unfoldS S0 = SSeq (SRcv m T) S → pscoped m T →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TSess S0 x a mS) c0 →
      typed W N Θ Γ Δ F (ERecv e) (TProd (payload_at m T x) (TSess S x⁺ mS mS)) (fadd c0 (Some 1))
  | e_close Θ Γ Δ F e S0 x a mS c0 :
      unfoldS S0 = SEnd →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TSess S0 x a mS) c0 →
      typed W N Θ Γ Δ F (EClose e) TUnit (fadd c0 (Some 1))
  | e_select (i : bool) Θ Γ Δ F e S0 x S1 S2 a mS c0 :
      unfoldS S0 = SPlus S1 S2 →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TSess S0 x a mS) c0 →
      typed W N Θ Γ Δ F (ESel i e) (TSess (if i then S2 else S1) (sel_pt x i) mS mS) (fadd c0 (Some 1))
  | e_branch Θ Γ Δ F e S0 x S1 S2 a mS c0 :
      unfoldS S0 = SWith S1 S2 →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TSess S0 x a mS) c0 →
      typed W N Θ Γ Δ F (EBra e)
        (TSum (TSess S1 (bra_pt x false) mS mS) (TSess S2 (bra_pt x true) mS mS)) (fadd c0 (Some 1))
  | e_link Θ Γ Δ F e S x a1 m1 a2 m2 c0 :
      typed W N Θ Γ Δ F e (TProd (TSess S x a1 m1) (TSess (dual S) x‾ a2 m2)) c0 →
      lgt N a1 m2 → lgt N a2 m1 →
      typed W N Θ Γ Δ F (ELink e) TUnit c0
  | e_spawn Θ Γ Δ F e ub lb c' a c0 :
      typed W N Θ Γ Δ F e (TLolli ub lb c' TUnit TUnit a) c0 →
      fle (Some 1) a →
      typed W N Θ Γ Δ F (ESpawn e) TUnit c0
  | e_new Γ Δ F C S m1 m2 :
      lenv_unl Δ → new_ok N W Γ C → tsum_ok N m1 m2 → scontr S →
      typed W N ∅ Γ Δ F ENew
        (TEx LBot 1 C (TProd (TSess S (pvar 0) m1 m1) (TSess (dual S) (pvar 0)‾ m2 m2)))
        (Some 0)
  | e_new_fld Γ Δ F x κ S m1 m2 :
      lenv_unl Δ → tsum_ok N m1 m2 → scontr S →
      typed W N ∅ Γ Δ F ENew
        (TProd (TSess S (x·κ) m1 m1) (TSess (dual S) (x·κ)‾ m2 m2)) (Some 0)
  | e_sub Θ Γ Δ F e T T' c c' :
      typed W N Θ Γ Δ F e T c → tsub W Γ T T' → fle c c' → (tcontr T → tcontr T') →
      typed W N Θ Γ Δ F e T' c'
  | e_pack Θ Γ Δ F e lb m C T xs c :
      length xs = m → hold_at W Γ C xs →
      lbx_below_h W Γ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
      ex_wf W Γ lb m C T →
      typed W N Θ Γ Δ F e (ty_inst xs T) c →
      typed W N Θ Γ Δ F e (TEx lb m C T) c
  | e_open Θ Γ Δ F e i lb m C T U c :
      Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T → cons_open W Γ m C →
      typed W N (tenv_pinst (pshift m) Θ) (hc_open m C Γ)
        (<[i := Some T]> (lenv_pinst (pshift m) Δ))
        (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) c →
      typed W N Θ Γ Δ F e U c.

(** ** The deadlock-freedom projection

    DF typing is the merged judgment at N = ∞ with the annotations of
    N = ∞, cost ∞ and tickets ∞. Its rules [d_*] are lemmas
    (static/Conservativity.v), and [conservative] shows that any
    derivation at N = ∞ gives one. *)

Definition dftyped (W : sworld) (Θ : tenv) (Γ : hctx) (Δ : lenv) (F : sfuture) (e : expr) (T : ty) : Prop :=
  typed W None (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T) None.

(** ** Process typing

    P-Term types one thread over the interface Σ and the ends Θ_B of the
    restricted channels C0, both ends of each, dual at dual points, each
    end at credit equal to its tickets, the tickets of the two ends of a
    channel summing to at most N. The interface ends sit at credit and
    tickets N/2, so a cut of P-Connect also meets the bound. P-Term asks
    its world well formed and well-founded.
    P-Connect composes two components typed at their own worlds over the
    cut Σ_C.

    [ptyped] hides. P-Term restricts the world of its thread to the
    constants of the interface Σ and of the type T ([iface]), through
    the order the world derives ([swrestrict]), so a chain through a
    private constant becomes a fact between interface points. P-Connect
    asks the join of the two interface worlds well-founded and hides the
    cut. The constants of a derivation outside its interface are
    private, and two components may pick the same one.

    [fptyped] keeps the whole world. Its P-Connect asks the restrictions
    of the two worlds to their shared constants S = A_{W1} ∩ A_{W2}
    well-founded together. Both components sit over well-founded worlds
    by induction, so the join is well-founded ([wf_join_iff],
    [fptyped_wf]) and the form of the rule that asks the join
    well-founded is admissible ([fp_connect_join]). A hidden derivation
    gives a full one with private constants renamed apart
    ([ptyped_full], static/Hiding.v), and a full one a hidden one
    ([fptyped_ptyped]). *)

Definition chans_of (Σ : senv) : gset chan := set_map ech (dom Σ).

(** Σ̄_C, the partner ends at dual types and points. *)
Definition senv_dual (Σ : senv) : senv :=
  kmap edual ((λ e : sty * point, (dual e.1, e.2‾)) <$> Σ).

Global Instance edual_inj : base.Inj eq eq edual.
Proof. intros o o'. apply edual_inj. Qed.

(** No end of Σ has its partner in Σ. P-Term asks it of the interface: a
    channel whose two ends the thread holds is restricted (decision of
    2026-11-18). *)
Definition pfree (Σ : senv) : Prop := ∀ o, o ∈ dom Σ → edual o ∉ dom Σ.

Lemma pfree_empty : pfree ∅.
Proof. intros o. rewrite dom_empty_L. set_solver. Qed.

Lemma pfree_singleton o v : pfree {[o := v]}.
Proof.
  intros o'. rewrite dom_singleton_L, !elem_of_singleton. intros Ho H.
  subst. destruct o; discriminate.
Qed.

Inductive fptyped (N : fuel) : sworld → senv → proc → ty → Prop :=
  | fp_term W Σ ΘB C0 t T c :
      tfree T →
      (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
      (∀ o e, Σ !! o = Some e → scontr e.1) →
      (∀ c, c ∈ C0 → ∃ S x m m', tsum_ok N m m' ∧ scontr S ∧
         ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ m' m')) →
      typed W N (tenv_of (fhalf N) Σ ∪ ΘB) hc_empty [] (∅, None) t T c →
      sworld_wf W ∧ wok N W →
      fptyped N W Σ (C0, {[+ t +]}) T
  | fp_connect W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
      fptyped N W1 (Σ1 ∪ ΣC) (C1, E1) T →
      fptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
      (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
      chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
      C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
      wok N (swrestrict W1 (swshared W1 W2) ⊔ swrestrict W2 (swshared W1 W2)) →
      fptyped N (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.

(** ** Notations (Appendix A) *)

Notation "Θ ; Γ ; Δ ⊢^ F '_{' W , N '}' e : T ▷ c" := (typed W N Θ Γ Δ F e T c)
  (at level 74, Γ at level 60, Δ at level 60, F at level 0, W at level 0, N at level 0,
   e at level 60, T at level 29, c at level 60,
   format "Θ  ;  Γ  ;  Δ  ⊢^ F  '_{' W , N '}'  e  :  T  ▷  c").

Notation "Θ ; Γ ; Δ ⊢^ F '_' W t : T" := (dftyped W Θ Γ Δ F t T)
  (at level 74, Γ at level 60, Δ at level 60, F at level 0, W at level 0,
   t at level 60, T at level 60,
   format "Θ  ;  Γ  ;  Δ  ⊢^ F  '_'  W  t  :  T").

(** The mode premise of a join reduces to the shared constants. *)
Lemma wok_join_iff N W1 W2 : sworld_wf W1 → sworld_wf W2 →
  wok N (W1 ⊔ W2) ↔ wok N W1 ∧ wok N W2 ∧
    wok N (swrestrict W1 (swshared W1 W2) ⊔ swrestrict W2 (swshared W1 W2)).
Proof. intros H1 H2. destruct N; [apply wf_join_iff|apply acyc_join_iff]; done. Qed.

(** Every process derivation sits over a well-formed world, acyclic at
    N = ∞ and well-founded at a finite N. *)
Lemma fptyped_wf N W Σ p T : fptyped N W Σ p T → sworld_wf W ∧ wok N W.
Proof.
  induction 1 as [|W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 _ _ _ _ _ _ _ _ _ HS]; [done|].
  split; [by apply swjoin_wf; [apply IH1|apply IH2]|].
  apply (wok_join_iff N W1 W2 (proj1 IH1) (proj1 IH2)). split_and!; [apply IH1|apply IH2|done].
Qed.

(** P-Connect asking the join well-founded and both worlds well formed
    is admissible. *)
Lemma fp_connect_join N W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  fptyped N W1 (Σ1 ∪ ΣC) (C1, E1) T →
  fptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
  (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  sworld_wf W1 → sworld_wf W2 →
  wok N (W1 ⊔ W2) →
  fptyped N (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.
Proof.
  intros H1 H2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 Hw1 Hw2 HS.
  apply fp_connect; [exact H1|exact H2|exact HD1|exact HD2|exact Hf|exact H12|exact H1C|exact H2C
    |exact HC|exact HC1|exact HC2|]. by apply (wok_join_iff N W1 W2 Hw1 Hw2).
Qed.

Lemma fptyped_tfree N W Σ p T : fptyped N W Σ p T → tfree T.
Proof. induction 1; auto. Qed.

Lemma chans_of_union (Σ1 Σ2 : senv) : chans_of (Σ1 ∪ Σ2) = chans_of Σ1 ∪ chans_of Σ2.
Proof. unfold chans_of. by rewrite dom_union_L, set_map_union_L. Qed.

Lemma elem_of_chans_of' o (Σ : senv) : o ∈ dom Σ → ech o ∈ chans_of Σ.
Proof. intros H. unfold chans_of. apply elem_of_map. by exists o. Qed.

(** A typed interface is partner-free: P-Term asks it, and P-Connect
    keeps it, because the cut leaves and chans Σ1 ## chans Σ2. *)
Lemma pfree_join (Σ1 ΣC Σ2 ΣD : senv) : pfree (Σ1 ∪ ΣC) → pfree (Σ2 ∪ ΣD) →
  chans_of Σ1 ## chans_of Σ2 → pfree (Σ1 ∪ Σ2).
Proof.
  intros H1 H2 H12 o Ho Hd. rewrite dom_union_L in Ho, Hd.
  apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_union in Hd as [Hd|Hd].
  - apply (H1 o); rewrite dom_union_L; set_solver.
  - apply (H12 (ech o)); [by apply elem_of_chans_of'|]. rewrite <-ech_edual. by apply elem_of_chans_of'.
  - apply (H12 (ech o)); [|by apply elem_of_chans_of']. rewrite <-ech_edual. by apply elem_of_chans_of'.
  - apply (H2 o); rewrite dom_union_L; set_solver.
Qed.

Lemma fptyped_pfree N W Σ p T : fptyped N W Σ p T → pfree Σ.
Proof. induction 1; [done|eauto using pfree_join]. Qed.

(** A typed process restricts no channel of its interface. *)
Lemma fptyped_chans N W Σ p T : fptyped N W Σ p T → p.1 ## chans_of Σ.
Proof.
  induction 1 as [|? ? ? ? ? ? ? ? ? ? _ IH1 _ IH2 ? ? ? ? ? ? ? ? ?];
    simpl in *; [done|..]; rewrite !chans_of_union in *; set_solver.
Qed.

(** ** Process typing with hiding

    The world of a process judgment lives on the constants of its
    interface. P-Term hides the constants of its world outside
    [iface Σ T], P-Connect compares the two interface worlds and hides
    the cut. A world restricted to S keeps every fact the world derives
    between points with roots in S, through private constants too
    ([swrestrict_iff], static/Hiding.v). *)
Inductive ptyped (N : fuel) : sworld → senv → proc → ty → Prop :=
  | p_term W Σ ΘB C0 t T c :
      tfree T →
      (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
      (∀ o e, Σ !! o = Some e → scontr e.1) →
      (∀ c, c ∈ C0 → ∃ S x m m', tsum_ok N m m' ∧ scontr S ∧
         ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ m' m')) →
      typed W N (tenv_of (fhalf N) Σ ∪ ΘB) hc_empty [] (∅, None) t T c →
      sworld_wf W ∧ wok N W →
      ptyped N (swrestrict W (iface Σ T)) Σ (C0, {[+ t +]}) T
  | p_connect W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
      ptyped N W1 (Σ1 ∪ ΣC) (C1, E1) T →
      ptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
      (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
      chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
      C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
      wok N (W1 ⊔ W2) →
      ptyped N (swrestrict (W1 ⊔ W2) (iface (Σ1 ∪ Σ2) T)) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.

Notation "Σ ⊢_ W p : T" := (ptyped None W Σ p T)
  (at level 74, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊢_ W  p  :  T").

Lemma swrestrict_swf W S : swf W → swf (swrestrict W S).
Proof. intros [ρ Hρ]. exists ρ. intros x y H. apply Hρ. exact (swrestrict_lt W S x y H). Qed.

Lemma swrestrict_sacyc W S : sacyc W → sacyc (swrestrict W S).
Proof. intros H x Hx. exact (H x (swrestrict_lt W S x x Hx)). Qed.

Lemma swrestrict_wok N W S : wok N W → wok N (swrestrict W S).
Proof. destruct N; [apply swrestrict_swf|apply swrestrict_sacyc]. Qed.

(** Every hidden derivation sits over a well-formed world on the
    constants of its interface, acyclic at N = ∞ and well-founded at a
    finite N. *)
Lemma ptyped_wf N W Σ p T : ptyped N W Σ p T → sworld_wf W ∧ wok N W.
Proof.
  destruct 1 as [W Σ ΘB C0 t T c _ _ _ _ _ _ _ [_ HW]|W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ _ _ _ _ _ _ _ _ _ _ HS];
    (split; [apply swrestrict_wf|by apply swrestrict_wok]).
Qed.

Lemma ptyped_consts N W Σ p T : ptyped N W Σ p T → sw_consts W ⊆ iface Σ T.
Proof. destruct 1; simpl; set_solver. Qed.

Lemma ptyped_tfree N W Σ p T : ptyped N W Σ p T → tfree T.
Proof. induction 1; auto. Qed.

Lemma ptyped_pfree N W Σ p T : ptyped N W Σ p T → pfree Σ.
Proof. induction 1; [done|eauto using pfree_join]. Qed.

Lemma ptyped_chans N W Σ p T : ptyped N W Σ p T → p.1 ## chans_of Σ.
Proof.
  induction 1 as [|? ? ? ? ? ? ? ? ? ? _ IH1 _ IH2 ? ? ? ? ? ? ? ? ?];
    simpl in *; [done|..]; rewrite !chans_of_union in *; set_solver.
Qed.
