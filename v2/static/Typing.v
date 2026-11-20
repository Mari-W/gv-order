(** * The one typing judgment (stage S2, proposal §2.17, decision Q11)

    Θ ; Γ ; Δ ⊢^F_{W,N} e : T ▷ c ; ϑ        [typed W N Θ Γ Δ F e T c ϑ]

    One judgment for session types and costs. The readiness and future
    premises are those of the old static typing (theories/static/Typing.v),
    the cost premises those of the old cost judgment
    (theories/static/CostTyping.v). N is the refill, the credit of a fresh
    end and of an end after an action. Deadlock-freedom typing is the
    instance N = ∞ ([conservative] in static/Conservativity.v).

    No program mentions a point. [new_ℓ] opens a fresh generated root ρ
    of family ℓ with the laws Λ_ℓ(ρ) of W (E-New), [new_κ o] creates at
    the field x·κ of the point x of o and returns o (E-NewAt). Every
    primitive has its own rule (E-Send, …, E-Force). A constant k passed as
    a function is its eta-expansion λy. k y, which types by E-Abs over the
    rule of k (static/Constants.v).

    [dftyped] is the deadlock-freedom projection, Θ ; Γ ; Δ ⊢^F_W e : T,
    defined as the instance N = ∞ with the annotations of N = ∞. Its
    rules [d_*] (static/Conservativity.v) are those of the merged
    judgment without the cost premises and without aging and capture.
    No rule matches the shape of a redex. let x = e1 in e2 is
    the derived form [ELet] of lang/Syntax.v, and E-Let and D-Let are
    admissible ([e_let] and [d_let] in static/Weakening.v). [ptyped] is process typing with P-Term and P-Connect
    in the two-world form. P-Connect compares the two worlds only at
    their shared roots, and every derivation sits over a strict world
    ([ptyped_strict]). *)

From GV Require Export static.Contexts.

Inductive typed (W : world) (N : fuel) :
    tenv → hctx → lenv → sfuture → expr → ty → fuel → tix → Prop :=
  | e_unit Γ Δ F :
      lenv_unl Δ →
      typed W N ∅ Γ Δ F EUnit TUnit (Some 0) tid
  | e_var Γ Δ F x T :
      lenv_only Δ x T →
      typed W N ∅ Γ Δ F (Var x) T (Some 0) tid
  | e_chan Γ Δ F o S x a :
      lenv_unl Δ →
      typed W N {[o := TE S x a]} Γ Δ F (Chan o) (TSess S x a) (Some 0) tid
  | e_abs Θ Θh Γ Δ Δh F e T U ub lb c t h a φ :
      φ ∉ dom (hc_fv Γ) →
      lbx_below_h W Γ (lbound_of lb) (tenv_heads Θ ∪ lenv_heads Δ) (lenv_bot Δ) →
      thcap h a Θ Θh → lcap h a Δ Δh →
      typed W N Θh (hc_fvar φ ub Γ) (Some T :: Δh) (∅, Some (FVar φ)) e U c t →
      typed W N Θ Γ Δ F (Lam e) (TLolli ub lb c t h T U a) (Some 0) tid
  | e_app Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c t h T U a1 c1 t1 c2 t2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below_s W Γ ub F →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1
        (TLolli ub lb c t h T U a1) c1 t1 →
      thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
      typed W N Θ2' Γ Δ2' (sf_unionb F (opt_heads lb) false) e2 T c2 t2 →
      fle c2 a1 → tok t2 t → tok t1 (tseq t2 t) →
      typed W N Θ Γ Δ F (App e1 e2) U (fadd c1 (fadd c2 c)) (tseq t1 (tseq t2 t))
  | e_pair Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T1' T2 c1 t1 c2 t2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 c1 t1 →
      thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
      typed W N Θ2' Γ Δ2' (sf_unionb F (heads T1) (hbot T1)) e2 T2 c2 t2 →
      tage c2 T1 T1' → tok t1 t2 →
      typed W N Θ Γ Δ F (Pair e1 e2) (TProd T1' T2) (fadd c1 c2) (tseq t1 t2)
  | e_letu Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T c1 t1 c2 t2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit c1 t1 →
      thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
      typed W N Θ2' Γ Δ2' F e2 T c2 t2 →
      tok t1 t2 →
      typed W N Θ Γ Δ F (LetU e1 e2) T (fadd c1 c2) (tseq t1 t2)
  | e_letp Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T2 T c1 t1 c2 t2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1
        (TProd T1 T2) c1 t1 →
      thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
      typed W N Θ2' Γ (Some T2 :: Some T1 :: Δ2') F e2 T c2 t2 →
      tok t1 t2 →
      typed W N Θ Γ Δ F (LetP e1 e2) T (fadd c1 c2) (tseq t1 t2)
  | e_inj (i : bool) Θ Γ Δ F e T U c t :
      typed W N Θ Γ Δ F e (if i then U else T) c t →
      typed W N Θ Γ Δ F (Inj i e) (TSum T U) c t
  | e_case Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e e1 e2 T1 T2 T c0 t0 c1 t1 c2 t2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
      typed W N Θ1 Γ Δ1 (sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e
        (TSum T1 T2) c0 t0 →
      thage c0 Θ2 Θ2' → lage c0 Δ2 Δ2' →
      typed W N Θ2' Γ (Some T1 :: Δ2') F e1 T c1 t1 →
      typed W N Θ2' Γ (Some T2 :: Δ2') F e2 T c2 t2 →
      tok t0 (tmax t1 t2) →
      typed W N Θ Γ Δ F (Case e e1 e2) T (fadd c0 (fmax c1 c2)) (tseq t0 (tmax t1 t2))
  | e_box Γ Δ F e m k C ub c t U φ :
      lenv_unl Δ → φ ∉ dom (hc_fv (hc_open m C Γ)) →
      (∀ ss, length ss = k → sinsts N ss →
         typed W N ∅ (hc_fvar φ ub (hc_open m C Γ))
           (lenv_pinst (pshift m) (Some (TBox m k C ub c t U) :: Δ))
           (∅, Some (FVar φ)) e (sinst_ty (slist ss) U) c t) →
      typed W N ∅ Γ Δ F (EBox e) (TBox m k C ub c t U) (Some 0) tid
  | e_force Θ Γ Δ F e m k C ub c t U xs ss c0 t0 :
      length xs = m → hold_at W Γ C xs → length ss = k → sinsts N ss →
      ub_below_s W Γ (pt_inst (plist xs) <$> ub) F →
      typed W N Θ Γ Δ F e (TBox m k C ub c t U) c0 t0 →
      tok t0 t →
      typed W N Θ Γ Δ F (EForce e) (sinst_ty (slist ss) (ty_inst xs U)) (fadd c0 c) (tseq t0 t)
  | e_send Θ Γ Δ F e S0 x m T S aS Tp Tp' c0 t0 :
      unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → hbot T = false →
      (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TProd Tp (TSess S0 x aS)) c0 t0 →
      tage (Some 1) Tp Tp' → tsub Tp' (payload_at m T x) →
      typed W N Θ Γ Δ F (ESend e) (TSess S x⁺ N) (fadd c0 (Some 1)) t0
  | e_recv Θ Γ Δ F e S0 x m T S a c0 t0 :
      unfoldS S0 = SSeq (SRcv m T) S → pscoped m T →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TSess S0 x a) c0 t0 →
      typed W N Θ Γ Δ F (ERecv e) (TProd (payload_at m T x) (TSess S x⁺ N)) (fadd c0 (Some 1)) t0
  | e_close Θ Γ Δ F e S0 x a c0 t0 :
      unfoldS S0 = SEnd →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TSess S0 x a) c0 t0 →
      typed W N Θ Γ Δ F (EClose e) TUnit (fadd c0 (Some 1)) t0
  | e_select (i : bool) Θ Γ Δ F e S0 x S1 S2 a c0 t0 :
      unfoldS S0 = SPlus S1 S2 →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TSess S0 x a) c0 t0 →
      typed W N Θ Γ Δ F (ESel i e) (TSess (if i then S2 else S1) (sel_pt x i) N) (fadd c0 (Some 1)) t0
  | e_branch Θ Γ Δ F e S0 x S1 S2 a c0 t0 :
      unfoldS S0 = SWith S1 S2 →
      ub_below_s W Γ (Some x) F →
      typed W N Θ Γ Δ F e (TSess S0 x a) c0 t0 →
      typed W N Θ Γ Δ F (EBra e)
        (TSum (TSess S1 (bra_pt x false) N) (TSess S2 (bra_pt x true) N)) (fadd c0 (Some 1)) t0
  | e_link Θ Γ Δ F e S x a1 a2 c0 t0 :
      typed W N Θ Γ Δ F e (TProd (TSess S x a1) (TSess (dual S) x‾ a2)) c0 t0 →
      tok t0 (tlink tid) →
      typed W N Θ Γ Δ F (ELink e) TUnit c0 (tseq t0 (tlink tid))
  | e_spawn_lam Θ Θ' Γ Δ Δ' F e c' t' :
      thage (Some 1) Θ Θ' → lage (Some 1) Δ Δ' →
      typed W N Θ' Γ (Some TUnit :: Δ') (∅, None) e TUnit c' t' →
      typed W N Θ Γ Δ F (ESpawn (Lam e)) TUnit (Some 0) (tspawn (tapp t' 0) tid)
  | e_spawn Θ Γ Δ F e ub lb c' t' h a c0 t0 :
      typed W N Θ Γ Δ F e (TLolli ub lb c' t' h TUnit TUnit a) c0 t0 →
      fle (Some 1) a → tok t0 (tspawn (tapp t' 0) tid) →
      typed W N Θ Γ Δ F (ESpawn e) TUnit c0 (tseq t0 (tspawn (tapp t' 0) tid))
  | e_new Γ Δ F ℓ S :
      lenv_unl Δ → ℓ ∈ w_fams W →
      typed W N ∅ Γ Δ F (ENew ℓ)
        (TEx LBot 1 (bcs_of (w_laws W ℓ)) (TProd (TSess S (pvar 0) N) (TSess (dual S) (pvar 0)‾ N)))
        (Some 0) tid
  | e_new_at Θ Γ Δ F e κ S0 x a S c0 t0 :
      typed W N Θ Γ Δ F e (TSess S0 x a) c0 t0 →
      typed W N Θ Γ Δ F (ENewAt κ e)
        (TProd (TSess S0 x a) (TProd (TSess S (x·κ) N) (TSess (dual S) (x·κ)‾ N))) c0 t0
  | e_sub Θ Γ Δ F e T T' c c' t t' :
      typed W N Θ Γ Δ F e T c t → tsub T T' → fle c c' → tle t t' →
      typed W N Θ Γ Δ F e T' c' t'
  | e_pack Θ Γ Δ F e lb m C T xs c t :
      length xs = m → hold_at W Γ C xs →
      lbx_below_h W Γ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
      typed W N Θ Γ Δ F e (ty_inst xs T) c t →
      typed W N Θ Γ Δ F e (TEx lb m C T) c t
  | e_open Θ Γ Δ F e i lb m C T U c t :
      Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
      typed W N (tenv_pinst (pshift m) Θ) (hc_open m C Γ)
        (<[i := Some T]> (lenv_pinst (pshift m) Δ))
        (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) c t →
      typed W N Θ Γ Δ F e U c t.

(** ** The deadlock-freedom projection

    DF typing is the merged judgment at N = ∞ with the annotations of
    N = ∞, cost ∞ and transformer (∞, ∞). Its rules [d_*] are lemmas
    (static/Conservativity.v), and [conservative] shows that any
    derivation at N = ∞ gives one. *)

Definition dftyped (W : world) (Θ : tenv) (Γ : hctx) (Δ : lenv) (F : sfuture) (e : expr) (T : ty) : Prop :=
  typed W None (tenv_df Θ) Γ (lenv_df Δ) F e (ty_df T) None tinf.

(** ** Process typing

    P-Term types one thread over the interface Σ and the ends Θ_B of the
    restricted channels C0, both ends of each, dual at dual points, with
    credit N, and at a finite N asks some ticket count to meet the
    transformer of the thread at 0. At N = ∞ the premise holds by its
    left disjunct, so ⊢_W is unchanged. P-Term asks its world strict.
    P-Connect composes two components typed at their own worlds, whose
    families are apart, over the cut Σ_C, and asks only the restrictions
    of the two worlds to their shared roots S = A_{W1} ∩ A_{W2} strict
    together (entry 13 of docs/redesign/pending.md). Both components sit
    over strict worlds by induction, so the join is strict
    ([strict_join_iff], [ptyped_strict]) and the earlier form of the
    rule, which asked the join strict, is admissible
    ([p_connect_join]). *)

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

Inductive ptyped (N : fuel) : world → senv → proc → ty → Prop :=
  | p_term W Σ ΘB C0 t T c ϑ :
      tfree T →
      (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
      (∀ c, c ∈ C0 → ∃ S x, ΘB !! (c⁺)%cend = Some (TE S x N) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ N)) →
      typed W N (tenv_of N Σ ∪ ΘB) hc_empty [] (∅, None) t T c ϑ →
      (N = None ∨ ∃ tk, meets ϑ 0 tk) → strict W →
      ptyped N W Σ (C0, {[+ t +]}) T
  | p_connect W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
      ptyped N W1 (Σ1 ∪ ΣC) (C1, E1) T →
      ptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
      (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
      chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
      C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
      w_fams W1 ## w_fams W2 →
      strict (wrestrict W1 (wshared W1 W2) ⊔ wrestrict W2 (wshared W1 W2)) →
      ptyped N (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.

(** ** Notations (Appendix A) *)

Notation "Θ ; Γ ; Δ ⊢^ F '_{' W , N '}' e : T ▷ c ; ϑ" := (typed W N Θ Γ Δ F e T c ϑ)
  (at level 74, Γ at level 60, Δ at level 60, F at level 0, W at level 0, N at level 0,
   e at level 60, T at level 29, c at level 60, ϑ at level 60,
   format "Θ  ;  Γ  ;  Δ  ⊢^ F  '_{' W , N '}'  e  :  T  ▷  c  ;  ϑ").

Notation "Θ ; Γ ; Δ ⊢^ F '_' W t : T" := (dftyped W Θ Γ Δ F t T)
  (at level 74, Γ at level 60, Δ at level 60, F at level 0, W at level 0,
   t at level 60, T at level 60,
   format "Θ  ;  Γ  ;  Δ  ⊢^ F  '_'  W  t  :  T").

Notation "Σ ⊢_ W p : T" := (ptyped None W Σ p T)
  (at level 74, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊢_ W  p  :  T").

(** Every process derivation sits over a strict world. *)
Lemma ptyped_strict N W Σ p T : ptyped N W Σ p T → strict W.
Proof.
  induction 1 as [|W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 _ _ _ _ _ _ _ _ _ Hfam HS]; [done|].
  apply (strict_join_iff W1 W2 (proj1 IH1) (proj1 IH2) Hfam). by split_and!.
Qed.

(** The earlier P-Connect, which asked the join strict and both worlds
    well formed, is admissible. *)
Lemma p_connect_join N W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  ptyped N W1 (Σ1 ∪ ΣC) (C1, E1) T →
  ptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
  (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  world_wf W1 → world_wf W2 → w_fams W1 ## w_fams W2 →
  strict (W1 ⊔ W2) →
  ptyped N (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.
Proof.
  intros H1 H2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 Hw1 Hw2 Hfam HS.
  apply p_connect; try done. by apply (strict_join_iff W1 W2 Hw1 Hw2 Hfam).
Qed.

Lemma ptyped_tfree N W Σ p T : ptyped N W Σ p T → tfree T.
Proof. induction 1; auto. Qed.

Lemma chans_of_union (Σ1 Σ2 : senv) : chans_of (Σ1 ∪ Σ2) = chans_of Σ1 ∪ chans_of Σ2.
Proof. unfold chans_of. by rewrite dom_union_L, set_map_union_L. Qed.

Lemma elem_of_chans_of' o (Σ : senv) : o ∈ dom Σ → ech o ∈ chans_of Σ.
Proof. intros H. unfold chans_of. apply elem_of_map. by exists o. Qed.

(** A typed interface is partner-free: P-Term asks it, and P-Connect
    keeps it, because the cut leaves and chans Σ1 ## chans Σ2. *)
Lemma ptyped_pfree N W Σ p T : ptyped N W Σ p T → pfree Σ.
Proof.
  assert (∀ Σ1 ΣC Σ2 ΣD : senv, pfree (Σ1 ∪ ΣC) → pfree (Σ2 ∪ ΣD) →
            chans_of Σ1 ## chans_of Σ2 → pfree (Σ1 ∪ Σ2)) as Hc.
  { intros Σ1 ΣC Σ2 ΣD H1 H2 H12 o Ho Hd. rewrite dom_union_L in Ho, Hd.
    apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_union in Hd as [Hd|Hd].
    - apply (H1 o); rewrite dom_union_L; set_solver.
    - apply (H12 (ech o)); [by apply elem_of_chans_of'|]. rewrite <-ech_edual. by apply elem_of_chans_of'.
    - apply (H12 (ech o)); [|by apply elem_of_chans_of']. rewrite <-ech_edual. by apply elem_of_chans_of'.
    - apply (H2 o); rewrite dom_union_L; set_solver. }
  induction 1; [done|eauto..].
Qed.

(** A typed process restricts no channel of its interface. *)
Lemma ptyped_chans N W Σ p T : ptyped N W Σ p T → p.1 ## chans_of Σ.
Proof.
  induction 1 as [|? ? ? ? ? ? ? ? ? ? _ IH1 _ IH2 ? ? ? ? ? ? ? ? ?];
    simpl in *; [done|..]; rewrite !chans_of_union in *; set_solver.
Qed.
