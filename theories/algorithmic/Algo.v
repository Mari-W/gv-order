(** * The algorithmic judgment

    Two judgments over annotated terms, both with the inputs W, N, Θ,
    Γ, Δ and F of [typed].

      Θ ; Γ ; Δ ⊢^F t ⇒ T ▷ c        [syn], T and c are outputs
      Θ ; Γ ; Δ ⊢^F t ⇐ T ▷ c        [chk], T is an input, c an output

    Every rule is fixed by the form of t and, in checking, by the form
    of t alone as well: a λ, an injection, a case and a box are checked
    by their own rules, a let checks its body, and every other form is
    checked by synthesis followed by subtyping ([c_sub]). The split of a
    binary rule is the split by occurrence of algorithmic/Annot.v. No
    rule guesses a type, a split, an instance, a position or a place to
    open, and the premises are the premises of the declarative rules,
    which the oracles of algorithmic/Decide.v decide.

    E-Sub, E-Pack and E-Open are the annotation nodes [AAsc], [APack]
    and [AOpen]. E-Box checks its body once, at the fresh instance
    [box_inst] of algorithmic/Annot.v, and asks the box context
    contractive, which makes the check sound for every instance
    ([typed_sinst], static/Sinst.v). *)

From GV Require Export algorithmic.Annot.

(** The forms checked by synthesis and subtyping. *)
Definition by_sub (t : aexpr) : bool :=
  match t with
  | ALam _ | AInj _ _ | ACase _ _ _ | ABox _ | ALetU _ _ | ALetP _ _ => false
  | _ => true
  end.

(** The future of the first premise of a binary rule. *)
Definition fut1 (F : sfuture) (Θ2 : tenv) (Δ2 : lenv) : sfuture :=
  sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2).

Section algo.
  Context (W : sworld) (N : fuel).

  Inductive syn : tenv → hctx → lenv → sfuture → aexpr → ty → fuel → Prop :=
    | a_unit Γ Δ F :
        lenv_unl Δ →
        syn ∅ Γ Δ F AUnit TUnit (Some 0)
    | a_var Γ Δ F x T :
        lenv_only Δ x T →
        syn ∅ Γ Δ F (AVar x) T (Some 0)
    | a_chan Γ Δ F o S x a m :
        lenv_unl Δ → fle a m →
        syn {[o := TE S x a m]} Γ Δ F (AChan o) (TSess S x a m) (Some 0)
    | a_app Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F t1 t2 ub lb c T U a1 c1 c2 :
        tpart (erase t1) Θ = (Θ1, Θ2) → lpart (erase t1) Δ = (Δ1, Δ2) →
        syn Θ1 Γ Δ1 (fut1 F Θ2 Δ2) t1 (TLolli ub lb c T U a1) c1 →
        ub_below_u W Γ ub F →
        thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
        chk Θ2' Γ Δ2' (sf_unionb F (lb_heads lb) (lb_bot lb)) t2 T c2 →
        fle c2 a1 →
        syn Θ Γ Δ F (AApp t1 t2) U (fadd c1 (fadd c2 c))
    | a_pair Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F t1 t2 T1 T1' T2 c1 c2 :
        tpart (erase t1) Θ = (Θ1, Θ2) → lpart (erase t1) Δ = (Δ1, Δ2) →
        syn Θ1 Γ Δ1 (fut1 F Θ2 Δ2) t1 T1 c1 →
        thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
        syn Θ2' Γ Δ2' (sf_unionb F (heads T1) (hbot T1)) t2 T2 c2 →
        tage c2 T1 T1' →
        syn Θ Γ Δ F (APair t1 t2) (TProd T1' T2) (fadd c1 c2)
    | a_letu Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F t1 t2 T c1 c2 :
        tpart (erase t1) Θ = (Θ1, Θ2) → lpart (erase t1) Δ = (Δ1, Δ2) →
        chk Θ1 Γ Δ1 (fut1 F Θ2 Δ2) t1 TUnit c1 →
        thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
        syn Θ2' Γ Δ2' F t2 T c2 →
        syn Θ Γ Δ F (ALetU t1 t2) T (fadd c1 c2)
    | a_letp Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F t1 t2 T1 T2 T c1 c2 :
        tpart (erase t1) Θ = (Θ1, Θ2) → lpart (erase t1) Δ = (Δ1, Δ2) →
        syn Θ1 Γ Δ1 (fut1 F Θ2 Δ2) t1 (TProd T1 T2) c1 →
        thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
        syn Θ2' Γ (Some T2 :: Some T1 :: Δ2') F t2 T c2 →
        syn Θ Γ Δ F (ALetP t1 t2) T (fadd c1 c2)
    | a_force Θ Γ Δ F t xs ss m k C ub c U c0 :
        syn Θ Γ Δ F t (TBox m k C ub c U) c0 →
        length xs = m → hold_at W Γ C xs → length ss = k → sinsts N ss →
        ub_below_s W Γ (pt_inst (plist xs) <$> ub) F →
        syn Θ Γ Δ F (AForce xs ss t) (sinst_ty (slist ss) (ty_inst xs U)) (fadd c0 (fadd (Some 1) c))
    | a_send Θ Γ Δ F t S0 x m T S aS mS Tp Tp' c0 :
        syn Θ Γ Δ F t (TProd Tp (TSess S0 x aS mS)) c0 →
        unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → below_ty W Γ x (payload_at m T x) →
        ub_below_s W Γ (Some x) F →
        tage (Some 1) Tp Tp' → tsub W Γ Tp' (payload_at m T x) →
        syn Θ Γ Δ F (AOp PSend t) (TSess S x⁺ mS mS) (fadd c0 (Some 1))
    | a_recv Θ Γ Δ F t S0 x m T S a mS c0 :
        syn Θ Γ Δ F t (TSess S0 x a mS) c0 →
        unfoldS S0 = SSeq (SRcv m T) S → pscoped m T →
        ub_below_s W Γ (Some x) F →
        syn Θ Γ Δ F (AOp PRecv t) (TProd (payload_at m T x) (TSess S x⁺ mS mS)) (fadd c0 (Some 1))
    | a_close Θ Γ Δ F t S0 x a mS c0 :
        syn Θ Γ Δ F t (TSess S0 x a mS) c0 →
        unfoldS S0 = SEnd →
        ub_below_s W Γ (Some x) F →
        syn Θ Γ Δ F (AOp PClose t) TUnit (fadd c0 (Some 1))
    | a_select (i : bool) Θ Γ Δ F t S0 x S1 S2 a mS c0 :
        syn Θ Γ Δ F t (TSess S0 x a mS) c0 →
        unfoldS S0 = SPlus S1 S2 →
        ub_below_s W Γ (Some x) F →
        syn Θ Γ Δ F (AOp (PSel i) t) (TSess (if i then S2 else S1) (sel_pt x i) mS mS) (fadd c0 (Some 1))
    | a_branch Θ Γ Δ F t S0 x S1 S2 a mS c0 :
        syn Θ Γ Δ F t (TSess S0 x a mS) c0 →
        unfoldS S0 = SWith S1 S2 →
        ub_below_s W Γ (Some x) F →
        syn Θ Γ Δ F (AOp PBra t)
          (TSum (TSess S1 (bra_pt x false) mS mS) (TSess S2 (bra_pt x true) mS mS)) (fadd c0 (Some 1))
    | a_link Θ Γ Δ F t S x a1 m1 a2 m2 c0 :
        syn Θ Γ Δ F t (TProd (TSess S x a1 m1) (TSess (dual S) x‾ a2 m2)) c0 →
        lgt N a1 m2 → lgt N a2 m1 →
        syn Θ Γ Δ F (AOp PLink t) TUnit c0
    | a_spawn Θ Γ Δ F t ub lb c' a c0 :
        syn Θ Γ Δ F t (TLolli ub lb c' TUnit TUnit a) c0 →
        syn Θ Γ Δ F (AOp PSpawn t) TUnit c0
    | a_new Γ Δ F C S m1 m2 :
        lenv_unl Δ → new_ok N W Γ C → tsum_ok N m1 m2 → scontr S →
        syn ∅ Γ Δ F (ANew C S m1 m2)
          (TEx LBot 1 C (TProd (TSess S (pvar 0) m1 m1) (TSess (dual S) (pvar 0)‾ m2 m2))) (Some 0)
    | a_new_fld Γ Δ F x κ S m1 m2 :
        lenv_unl Δ → tsum_ok N m1 m2 → scontr S →
        syn ∅ Γ Δ F (ANewF x κ S m1 m2)
          (TProd (TSess S (x·κ) m1 m1) (TSess (dual S) (x·κ)‾ m2 m2)) (Some 0)
    | a_asc Θ Γ Δ F t T c c' :
        chk Θ Γ Δ F t T c → fle c c' →
        syn Θ Γ Δ F (AAsc T c' t) T c'
    | a_pack Θ Γ Δ F t lb m C T xs c :
        length xs = m → hold_at W Γ C xs →
        lbx_below_h W Γ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
        ex_wf W Γ lb m C T →
        chk Θ Γ Δ F t (ty_inst xs T) c →
        syn Θ Γ Δ F (APack lb m C T xs t) (TEx lb m C T) c
    | a_open Θ Γ Δ F t i lb m C T U c :
        Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T → cons_open W Γ m C →
        chk (tenv_pinst (pshift m) Θ) (hc_open m C Γ)
          (<[i := Some T]> (lenv_pinst (pshift m) Δ))
          (sf_pinst (pshift m) F) t (pinst_ty (pshift m) U) c →
        syn Θ Γ Δ F (AOpen i U t) U c

  with chk : tenv → hctx → lenv → sfuture → aexpr → ty → fuel → Prop :=
    | c_lam Θ Θh Γ Δ Δh F t T U ub lb c a c0 :
        lbx_below_h W Γ lb (tenv_heads Θ ∪ lenv_heads Δ) (lenv_bot Δ) →
        thage a Θ Θh → lage a Δ Δh → tcontr T →
        chk Θh Γ (Some T :: Δh) (abs_fut ub) t U c0 → fle c0 c →
        chk Θ Γ Δ F (ALam t) (TLolli ub lb c T U a) (Some 0)
    | c_inj (i : bool) Θ Γ Δ F t T U c :
        tcontr (TSum T U) →
        chk Θ Γ Δ F t (if i then U else T) c →
        chk Θ Γ Δ F (AInj i t) (TSum T U) c
    | c_case Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F t t1 t2 T1 T2 T c0 c1 c2 :
        tpart (erase t) Θ = (Θ1, Θ2) → lpart (erase t) Δ = (Δ1, Δ2) →
        syn Θ1 Γ Δ1 (fut1 F Θ2 Δ2) t (TSum T1 T2) c0 →
        thage c0 Θ2 Θ2' → lage c0 Δ2 Δ2' →
        chk Θ2' Γ (Some T1 :: Δ2') F t1 T c1 →
        chk Θ2' Γ (Some T2 :: Δ2') F t2 T c2 →
        chk Θ Γ Δ F (ACase t t1 t2) T (fadd c0 (fmax c1 c2))
    | c_box Γ Δ F t m k C ub c U c0 :
        lenv_unl Δ → tcontr U → lenv_contr Δ →
        chk ∅ (hc_open m C Γ)
          (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ))
          (∅, Some (rest_of ub)) t (sinst_ty (slist (box_inst (box_base k U Δ) k)) U) c0 →
        fle c0 c →
        chk ∅ Γ Δ F (ABox t) (TBox m k C ub c U) (Some 0)
    | c_letu Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F t1 t2 T c1 c2 :
        tpart (erase t1) Θ = (Θ1, Θ2) → lpart (erase t1) Δ = (Δ1, Δ2) →
        chk Θ1 Γ Δ1 (fut1 F Θ2 Δ2) t1 TUnit c1 →
        thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
        chk Θ2' Γ Δ2' F t2 T c2 →
        chk Θ Γ Δ F (ALetU t1 t2) T (fadd c1 c2)
    | c_letp Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F t1 t2 T1 T2 T c1 c2 :
        tpart (erase t1) Θ = (Θ1, Θ2) → lpart (erase t1) Δ = (Δ1, Δ2) →
        syn Θ1 Γ Δ1 (fut1 F Θ2 Δ2) t1 (TProd T1 T2) c1 →
        thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
        chk Θ2' Γ (Some T2 :: Some T1 :: Δ2') F t2 T c2 →
        chk Θ Γ Δ F (ALetP t1 t2) T (fadd c1 c2)
    | c_sub Θ Γ Δ F t T0 T c :
        by_sub t = true →
        syn Θ Γ Δ F t T0 c → tsub W Γ T0 T → (tcontr T0 → tcontr T) →
        chk Θ Γ Δ F t T c.

  Scheme syn_mut := Induction for syn Sort Prop
    with chk_mut := Induction for chk Sort Prop.
  Combined Scheme syn_chk_mut from syn_mut, chk_mut.
End algo.
