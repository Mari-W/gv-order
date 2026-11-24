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
    admissible ([e_let] and [d_let] in static/Weakening.v). [ptyped] is process typing with P-Term and P-Connect.
    P-Term concludes at the world of its thread, P-Connect at the join
    of the two component worlds. Every derivation sits over a
    well-founded world ([ptyped_wf]). *)

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
      lenv_unl Δ → fle a m →
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
           (∅, Some (rest_of ub)) e (sinst_ty (slist ss) U) c) →
      typed W N ∅ Γ Δ F (EBox e) (TBox m k C ub c U) (Some 0)
  | e_force Θ Γ Δ F e m k C ub c U xs ss c0 :
      length xs = m → hold_at W Γ C xs → length ss = k → sinsts N ss →
      ub_below_s W Γ (pt_inst (plist xs) <$> ub) F →
      typed W N Θ Γ Δ F e (TBox m k C ub c U) c0 →
      typed W N Θ Γ Δ F (EForce e) (sinst_ty (slist ss) (ty_inst xs U)) (fadd c0 (fadd (Some 1) c))
  | e_send Θ Γ Δ F e S0 x m T S aS mS Tp Tp' c0 :
      unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → below_ty W Γ x (payload_at m T x) →
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
    channel summing to at most N. An interface end o sits at the credit
    and the tickets η o of the interface annotations η, its tickets at
    most N, and P-Connect asks the tickets of the two ends of each cut
    channel to sum to at most N, as E-New does. P-Term asks its world
    well formed and well-founded.
    P-Connect composes two components typed at their own worlds over the
    cut Σ_C.

    P-Term concludes at the world of its thread. P-Connect asks the
    join of the two component worlds well-founded (acyclic at N = ∞)
    and concludes at that join. The constants of a derivation outside
    its interface are private, and two components may pick the same
    one. The proof of soundness reads a derivation at its own world
    ([fundamental_proc], static/FundamentalProc.v). *)

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

(** The side conditions that P-Connect does not ask. Disjoint channels
    give disjoint maps, and the cut of a partner-free interface is
    partner-free. *)
Lemma chans_disj_map (Σ1 Σ2 : senv) : chans_of Σ1 ## chans_of Σ2 → Σ1 ##ₘ Σ2.
Proof.
  intros H. apply map_disjoint_dom. intros o H1 H2.
  apply (H (ech o)); unfold chans_of; apply elem_of_map; by exists o.
Qed.

Lemma chans_of_senv_dual (Σ : senv) : chans_of (senv_dual Σ) = chans_of Σ.
Proof.
  unfold chans_of, senv_dual. rewrite dom_kmap_L by apply _. rewrite dom_fmap_L.
  apply set_eq. intros c. rewrite elem_of_map. setoid_rewrite elem_of_map. split.
  - intros (o & -> & o' & -> & Ho). exists o'. split; [by rewrite ech_edual|done].
  - intros (o & -> & Ho). exists (edual o). split; [by rewrite ech_edual|]. exists o. split; [done|done].
Qed.

Lemma chans_disj_map_dual (Σ2 ΣC : senv) : chans_of Σ2 ## chans_of ΣC → Σ2 ##ₘ senv_dual ΣC.
Proof. intros H. apply chans_disj_map. by rewrite chans_of_senv_dual. Qed.

Lemma pfree_union_r (Σ1 ΣC : senv) : pfree (Σ1 ∪ ΣC) → pfree ΣC.
Proof. intros H o Ho Hd. apply (H o); rewrite dom_union_L; set_solver. Qed.

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

(** ** Process typing (2026-11-24, no restriction)

    P-Term concludes at the world of its thread. P-Connect checks the
    join of the two component worlds and concludes at that join. The
    check reads only the two component worlds, so the rule stays
    compositional. Two components may use one private constant for
    unrelated points. The join then has more facts, and the check
    covers them. A derivation renames its constants by any bijection
    ([ptyped_ren], static/Hiding.v), so two components can always be
    renamed apart before they connect ([ptyped_apart]). *)
Inductive ptyped (N : fuel) (η : iann) : sworld → senv → proc → ty → Prop :=
  | p_term W Σ ΘB C0 t T c :
      tfree T →
      (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
      (∀ o e, Σ !! o = Some e → scontr e.1) →
      (∀ c, c ∈ C0 → ∃ S x m m', tsum_ok N m m' ∧ scontr S ∧
         ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ m' m')) →
      (∀ o, o ∈ dom Σ → fle (η o).2 N) →
      typed W N (tenv_ofk η Σ ∪ ΘB) hc_empty [] (∅, None) t T c →
      sworld_wf W ∧ wok N W →
      ptyped N η W Σ (C0, {[+ t +]}) T
  | p_connect W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
      ptyped N η W1 (Σ1 ∪ ΣC) (C1, E1) T →
      ptyped N η W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
      chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
      C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
      (∀ o, o ∈ dom ΣC → tsum_ok N (η o).2 (η (edual o)).2) →
      wok N (W1 ⊔ W2) →
      ptyped N η (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.

(** P-Term and P-Connect with every interface end at credit and tickets
    N/2, the rules before interface annotations. *)
Lemma p_term_half N W Σ ΘB C0 t T c :
  tfree T →
  (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
  (∀ o e, Σ !! o = Some e → scontr e.1) →
  (∀ c, c ∈ C0 → ∃ S x m m', tsum_ok N m m' ∧ scontr S ∧
     ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ m' m')) →
  typed W N (tenv_of (fhalf N) Σ ∪ ΘB) hc_empty [] (∅, None) t T c →
  sworld_wf W ∧ wok N W →
  ptyped N (khalf N) W Σ (C0, {[+ t +]}) T.
Proof.
  intros. apply (p_term N (khalf N) W Σ ΘB C0 t T c); try done; [intros; apply fhalf_le|]. by rewrite tenv_ofk_half.
Qed.

Lemma p_connect_half N W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  ptyped N (khalf N) W1 (Σ1 ∪ ΣC) (C1, E1) T →
  ptyped N (khalf N) W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  wok N (W1 ⊔ W2) →
  ptyped N (khalf N) (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.
Proof. intros. apply p_connect; try done. intros. apply tsum_fhalf. Qed.

Notation "Σ ⊢_ W p : T" := (ptyped None (khalf None) W Σ p T)
  (at level 74, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊢_ W  p  :  T").

(** Every derivation sits over a well-formed world, acyclic at N = ∞
    and well-founded at a finite N. *)
Lemma ptyped_wf N η W Σ p T : ptyped N η W Σ p T → sworld_wf W ∧ wok N W.
Proof.
  induction 1 as [W Σ ΘB C0 t T c _ _ _ _ _ _ _ _ HW|W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ [Hw1 _] _ [Hw2 _] _ _ _ _ _ _ _ HS];
    [exact HW|split; [by apply swjoin_wf|exact HS]].
Qed.

Lemma ptyped_tfree N η W Σ p T : ptyped N η W Σ p T → tfree T.
Proof. induction 1; auto. Qed.

Lemma ptyped_pfree N η W Σ p T : ptyped N η W Σ p T → pfree Σ.
Proof. induction 1; [done|eauto using pfree_join]. Qed.

Lemma ptyped_chans N η W Σ p T : ptyped N η W Σ p T → p.1 ## chans_of Σ.
Proof.
  induction 1 as [|? ? ? ? ? ? ? ? ? ? _ IH1 _ IH2 ? ? ? ? ? ? ?];
    simpl in *; [done|..]; rewrite !chans_of_union in *; set_solver.
Qed.

(** ** Locality of the interface annotations

    A derivation reads η at the interface ends of its components, which
    are the ends of its interface and the ends of the channels it binds.
    Two annotations that agree there type the same processes. *)
Lemma ptyped_iann_agree N η W Σ p T : ptyped N η W Σ p T →
  ∀ η', (∀ o, o ∈ dom Σ ∨ ech o ∈ p.1 → η' o = η o) → ptyped N η' W Σ p T.
Proof.
  induction 1 as [W Σ ΘB C0 t T c HT HB HC Hp Hc HC0 Hle Ht HW
                 |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 H12 H1C H2C HC12 HC1 HC2 Hs HW];
    intros η' Hag; simpl in *.
  - apply (p_term N η' W Σ ΘB C0 t T c); try done.
    + intros o Ho. rewrite (Hag o (or_introl Ho)). by apply Hle.
    + enough (tenv_ofk η' Σ = tenv_ofk η Σ) as -> by done.
      apply map_eq. intros o. rewrite !lookup_tenv_ofk. destruct (Σ !! o) eqn:E; [|done].
      simpl. rewrite (Hag o); [done|left; by eapply elem_of_dom_2].
  - assert (∀ o, o ∈ dom ΣC → ech o ∈ C1 ∪ C2 ∪ chans_of ΣC) as HcC.
    { intros o Ho. apply elem_of_union_r. by apply elem_of_chans_of'. }
    apply p_connect; try done.
    + apply IH1. intros o [Ho|Ho]; apply Hag.
      * rewrite dom_union_L in Ho. apply elem_of_union in Ho as [Ho|Ho].
        -- left. rewrite dom_union_L. set_solver.
        -- right. by apply HcC.
      * right. set_solver.
    + apply IH2. intros o [Ho|Ho]; apply Hag.
      * rewrite dom_union_L in Ho. apply elem_of_union in Ho as [Ho|Ho].
        -- left. rewrite dom_union_L. set_solver.
        -- right. apply elem_of_union_r. rewrite <-(chans_of_senv_dual ΣC). by apply elem_of_chans_of'.
      * right. set_solver.
    + intros o Ho. rewrite (Hag o), (Hag (edual o)); [by apply Hs| |].
      * right. rewrite ech_edual. by apply HcC.
      * right. by apply HcC.
Qed.

Lemma ptyped_iann_local N η η' W Σ p T :
  (∀ o, o ∈ dom Σ ∨ ech o ∈ p.1 → η o = η' o) →
  ptyped N η W Σ p T ↔ ptyped N η' W Σ p T.
Proof.
  intros Hag. split; intros H; eapply ptyped_iann_agree; [exact H| |exact H|].
  - intros o Ho. symmetry. by apply Hag.
  - intros o Ho. by apply Hag.
Qed.

(** Two components typed under their own annotations connect under the
    annotation that is η1 on the interface ends of the first and η2
    elsewhere, when the credits of each cut channel sum to at most N. *)
Definition iann_pick (A : cend → Prop) `{∀ o, Decision (A o)} (η1 η2 : iann) : iann :=
  λ o, if decide (A o) then η1 o else η2 o.

Lemma p_connect_iann N η1 η2 W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  ptyped N η1 W1 (Σ1 ∪ ΣC) (C1, E1) T →
  ptyped N η2 W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  (∀ o, o ∈ dom ΣC → tsum_ok N (η1 o).2 (η2 (edual o)).2) →
  wok N (W1 ⊔ W2) →
  ptyped N (iann_pick (λ o, o ∈ dom (Σ1 ∪ ΣC) ∨ ech o ∈ C1) η1 η2)
    (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.
Proof.
  intros D1 D2 H12 H1C H2C HC12 HC1 HC2 Hs HW.
  pose proof (ptyped_pfree _ _ _ _ _ _ D1) as Hp1.
  assert (∀ o, o ∈ dom (Σ2 ∪ senv_dual ΣC) ∨ ech o ∈ C2 → ¬ (o ∈ dom (Σ1 ∪ ΣC) ∨ ech o ∈ C1)) as Hdis.
  { intros o Ho1 Ho2. rewrite !dom_union_L in Ho1, Ho2.
    assert (o ∈ dom (senv_dual ΣC) → edual o ∈ dom ΣC) as Hd.
    { unfold senv_dual. rewrite dom_kmap_L by apply _. rewrite dom_fmap_L. rewrite elem_of_map.
      intros (o' & -> & Ho'). by rewrite edual_edual. }
    assert (o ∈ dom (senv_dual ΣC) → ech o ∈ chans_of ΣC) as Hdc.
    { intros H. rewrite <-ech_edual. apply elem_of_chans_of', Hd, H. }
    destruct Ho1 as [Ho1|Ho1]; [apply elem_of_union in Ho1 as [Ho1|Ho1]|];
      (destruct Ho2 as [Ho2|Ho2]; [apply elem_of_union in Ho2 as [Ho2|Ho2]|]).
    - apply (H12 (ech o)); by apply elem_of_chans_of'.
    - apply (H2C (ech o)); by apply elem_of_chans_of'.
    - apply (HC1 (ech o)); [done|]. apply elem_of_union_l. by apply elem_of_chans_of'.
    - apply (H1C (ech o)); [by apply elem_of_chans_of'|by apply Hdc].
    - pose proof (Hd Ho1). apply (Hp1 (edual o)); rewrite dom_union_L; [set_solver|]. rewrite edual_edual. set_solver.
    - apply (HC1 (ech o)); [done|]. apply elem_of_union_r. by apply Hdc.
    - apply (HC2 (ech o)); [done|]. apply elem_of_union_l. by apply elem_of_chans_of'.
    - apply (HC2 (ech o)); [done|]. apply elem_of_union_r. by apply elem_of_chans_of'.
    - apply (HC12 (ech o)); done. }
  apply p_connect; try done.
  - eapply ptyped_iann_agree; [exact D1|]. intros o Ho. unfold iann_pick. by rewrite decide_True.
  - eapply ptyped_iann_agree; [exact D2|]. intros o Ho. unfold iann_pick.
    rewrite decide_False; [done|]. by apply Hdis.
  - intros o Ho. unfold iann_pick. rewrite decide_True by (left; rewrite dom_union_L; set_solver).
    rewrite decide_False; [by apply Hs|]. apply Hdis. left. rewrite dom_union_L. apply elem_of_union_r.
    unfold senv_dual. rewrite dom_kmap_L by apply _. rewrite dom_fmap_L. apply elem_of_map. by exists o.
Qed.

(** ** Credits at most tickets

    Every end of a context that types a term has a credit at most its
    tickets. An end reaches E-Chan, which asks it, or passes an aging,
    which asks it before the end loses credit. *)

Lemma cr_tk_empty : cr_tk ∅.
Proof. intros o te. by rewrite lookup_empty. Qed.

Lemma cr_tk_thage c Θ Θ' : thage c Θ Θ' → cr_tk Θ.
Proof.
  intros H o te Hte. specialize (H o). rewrite Hte in H.
  destruct (Θ' !! o); [by destruct H as (_ & _ & _ & _ & _ & ?)|done].
Qed.

Lemma cr_tk_tsplit Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → cr_tk Θ1 → cr_tk Θ2 → cr_tk Θ.
Proof.
  intros [_ ->] H1 H2 o te Hte. apply lookup_union_Some_raw in Hte as [Hte|[_ Hte]]; eauto.
Qed.

Lemma cr_tk_pinst σ Θ : cr_tk (tenv_pinst σ Θ) → cr_tk Θ.
Proof.
  intros H o te Hte. apply (H o (tentry_pinst σ te)). unfold tenv_pinst. by rewrite lookup_fmap, Hte.
Qed.

Theorem typed_cr_tk W N Θ Γ Δ F e T c : typed W N Θ Γ Δ F e T c → cr_tk Θ.
Proof.
  induction 1; try apply cr_tk_empty; try done;
    try (eapply cr_tk_tsplit; [done|done|by eapply cr_tk_thage]);
    try (by eapply cr_tk_thage); try (by eapply cr_tk_pinst).
  intros o' te Hte. apply lookup_singleton_Some in Hte as [<- <-]. simpl. done.
Qed.
