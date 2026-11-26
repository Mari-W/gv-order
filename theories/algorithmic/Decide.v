(** * The decision procedure

    [alg t] computes, for an annotated term t, a synthesis function and
    a checking function. Each runs the rules of algorithmic/Algo.v by
    recursion on t, computes the split, the aging and the expected types,
    and asks the oracles of algorithmic/Oracles.v for the premises.

    - [alg_sound]: what [alg] returns is derivable.
    - [alg_complete]: what is derivable, [alg] returns.
    - [syn_dec], [chk_dec]: the algorithmic judgments are decidable
      relative to the oracles.
    - [syn_det], [chk_det]: synthesis has at most one result, checking
      at most one cost, so the judgments are syntax-directed. *)

From GV Require Export algorithmic.Oracles algorithmic.Complete.

(** ** Aging, computed *)

Fixpoint tage_f (c : fuel) (T : ty) : option ty :=
  match T with
  | TUnit => Some TUnit
  | TBox _ _ _ _ _ _ => Some T
  | TSess Ss x a mt => if decide (fle c a ∨ idle Ss) then Some (TSess Ss x (fsub a c) mt) else None
  | TLolli ub lb c0 T1 U a => if decide (fle c a) then Some (TLolli ub lb c0 T1 U (fsub a c)) else None
  | TProd T1 T2 =>
      match tage_f c T1, tage_f c T2 with Some T1', Some T2' => Some (TProd T1' T2') | _, _ => None end
  | TSum T1 T2 =>
      match tage_f c T1, tage_f c T2 with Some T1', Some T2' => Some (TSum T1' T2') | _, _ => None end
  | TEx lb n C T1 => match tage_f c T1 with Some T1' => Some (TEx lb n C T1') | None => None end
  end.

Lemma tage_f_free c T : tfree T → tage_f c T = Some T.
Proof. induction 1; simpl; try done; by rewrite IHtfree1, IHtfree2. Qed.

Lemma tage_f_spec c T T' : tage c T T' ↔ tage_f c T = Some T'.
Proof.
  split.
  - induction 1; simpl; try (by rewrite decide_True by auto).
    + by apply tage_f_free.
    + by rewrite IHtage1, IHtage2.
    + by rewrite IHtage1, IHtage2.
    + by rewrite IHtage.
  - revert T'. induction T as [|ub lb c0 T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2|n k C ub c0 U _|Ss x a mt|lb n C T1 IH]
      using ty_rect; intros T' H; simpl in H.
    + simplify_eq. apply age_free. constructor.
    + case_decide; simplify_eq. by apply age_arr.
    + destruct (tage_f c T1) eqn:E1, (tage_f c T2) eqn:E2; simplify_eq. constructor; auto.
    + destruct (tage_f c T1) eqn:E1, (tage_f c T2) eqn:E2; simplify_eq. constructor; auto.
    + simplify_eq. apply age_free. constructor.
    + case_decide as Hd; simplify_eq. destruct Hd; [by apply age_sess|by apply age_idle].
    + destruct (tage_f c T1) eqn:E1; simplify_eq. constructor; auto.
Qed.

Definition thage_ok (c : fuel) (e : tentry) : Prop :=
  (fle c (te_cr e) ∨ idle (te_sty e)) ∧ fle (te_cr e) (te_tk e).
Definition tentry_age (c : fuel) (e : tentry) : tentry :=
  TE (te_sty e) (te_pt e) (fsub (te_cr e) c) (te_tk e).

Global Instance thage_ok_dec c e : Decision (thage_ok c e).
Proof. unfold thage_ok. apply _. Defined.

Definition thage_f (c : fuel) (Θ : tenv) : option tenv :=
  if decide (map_Forall (λ _ e, thage_ok c e) Θ) then Some (tentry_age c <$> Θ) else None.

Lemma thage_f_spec c Θ Θ' : thage c Θ Θ' ↔ thage_f c Θ = Some Θ'.
Proof.
  unfold thage_f. split.
  - intros H. rewrite decide_True.
    + f_equal. apply map_eq. intros o. rewrite lookup_fmap. specialize (H o).
      destruct (Θ !! o) as [[s x a m]|], (Θ' !! o) as [[s' x' a' m']|]; simpl in *; try done.
      destruct H as (-> & -> & -> & _ & -> & _). done.
    + intros o e He. specialize (H o). rewrite He in H. destruct (Θ' !! o); [|done].
      destruct H as (_ & _ & _ & H1 & _ & H2). by split.
  - case_decide as Hf; [|done]. intros [= <-] o. rewrite lookup_fmap.
    destruct (Θ !! o) as [e|] eqn:E; simpl; [|done].
    destruct (Hf o e E) as [H1 H2]. by split_and!.
Qed.

Fixpoint lage_f (c : fuel) (Δ : lenv) : option lenv :=
  match Δ with
  | [] => Some []
  | None :: Δ' => match lage_f c Δ' with Some Δ'' => Some (None :: Δ'') | None => None end
  | Some T :: Δ' =>
      match tage_f c T, lage_f c Δ' with Some T', Some Δ'' => Some (Some T' :: Δ'') | _, _ => None end
  end.

Lemma lage_f_spec c Δ Δ' : lage c Δ Δ' ↔ lage_f c Δ = Some Δ'.
Proof.
  split.
  - induction 1 as [|Δ Δ' _ IH|σ σ' Δ Δ' Ht _ IH]; simpl; [done|by rewrite IH|].
    apply tage_f_spec in Ht. by rewrite Ht, IH.
  - revert Δ'. induction Δ as [|[T|] Δ IH]; intros Δ' H; simpl in H.
    + simplify_eq. constructor.
    + destruct (tage_f c T) eqn:E1, (lage_f c Δ) eqn:E2; simplify_eq.
      constructor; [by apply tage_f_spec|by apply IH].
    + destruct (lage_f c Δ) eqn:E2; simplify_eq. constructor. by apply IH.
Qed.

(** ** Contexts *)

Lemma lenv_unl_cons o Δ :
  lenv_unl (o :: Δ) ↔ (o = None ∨ ∃ U, o = Some U ∧ unlimited U) ∧ lenv_unl Δ.
Proof.
  split.
  - intros H. split; [apply H, list_elem_of_here|]. intros o' Ho'. apply H, list_elem_of_further, Ho'.
  - intros [Ho H] o' Ho'. apply elem_of_cons in Ho' as [->|Ho']; [done|by apply H].
Qed.

Global Instance lenv_unl_dec Δ : Decision (lenv_unl Δ).
Proof.
  induction Δ as [|o Δ IH].
  - left. intros o Ho. by apply elem_of_nil in Ho.
  - assert (Decision (o = None ∨ ∃ U, o = Some U ∧ unlimited U)) as Do.
    { destruct o as [U|].
      - destruct (decide (unlimited U)) as [Hu|Hu].
        + left. right. by exists U.
        + right. intros [Hn|(U' & HU' & Hu')]; [discriminate|]. injection HU' as <-. done.
      - left. by left. }
    destruct Do as [Ho|Ho].
    + destruct IH as [HΔ|HΔ].
      * left. apply lenv_unl_cons. by split.
      * right. intros Hc. apply HΔ. apply lenv_unl_cons in Hc. by destruct Hc.
    + right. intros Hc. apply Ho. apply lenv_unl_cons in Hc. by destruct Hc.
Defined.

Lemma lenv_only_iff Δ x T : lenv_only Δ x T ↔ Δ !! x = Some (Some T) ∧ lenv_unl (<[x := None]> Δ).
Proof.
  split.
  - intros [Hx Hy]. split; [done|]. intros o Ho. apply list_elem_of_lookup in Ho as [i Hi].
    destruct (decide (i = x)) as [->|Hne].
    + rewrite list_lookup_insert_eq in Hi by (by eapply lookup_lt_Some). simplify_eq. by left.
    + rewrite list_lookup_insert_ne in Hi by done. destruct o as [σ|]; [|by left].
      right. exists σ. split; [done|]. by apply (Hy i).
  - intros [Hx H]. split; [done|]. intros y σ Hne Hy.
    assert (Some σ ∈ <[x := None]> Δ) as Hin.
    { apply list_elem_of_lookup. exists y. by rewrite list_lookup_insert_ne by done. }
    destruct (H _ Hin) as [?|(U & [= <-] & HU)]; [done|done].
Qed.

Global Instance lenv_contr_dec Δ : Decision (lenv_contr Δ).
Proof.
  set (P := λ o : option ty, match o with Some T => Is_true (tcontr T) | None => True end).
  assert (lenv_contr Δ ↔ Forall P Δ) as HP.
  { rewrite Forall_lookup. split.
    - intros H i [T|] Hi; [by apply (H i)|done].
    - intros H i T Hi. exact (H i (Some T) Hi). }
  assert (∀ o, Decision (P o)) by (intros [T|]; unfold P; apply _).
  destruct (decide (Forall P Δ)) as [Hf|Hf]; [left; by apply HP|right; intros Hc; apply Hf, HP, Hc].
Defined.

Lemma dom_singleton_inv (Θ : tenv) o e : dom Θ = {[o]} → Θ !! o = Some e → Θ = {[o := e]}.
Proof.
  intros Hd He. apply map_eq. intros o'. destruct (decide (o' = o)) as [->|Hne].
  - by rewrite lookup_singleton_eq.
  - rewrite lookup_singleton_ne by done. apply not_elem_of_dom. rewrite Hd. set_solver.
Qed.

(** ** The algorithm *)

Abbreviation SynF := (tenv → hctx → lenv → sfuture → option (ty * fuel)).
Abbreviation ChkF := (tenv → hctx → lenv → sfuture → ty → option fuel).

Section alg.
  Context `{SltOracle, HoldOracle, ConsOracle, NewOracle, BcsOracle, SequivOracle, SsubOracle}.
  Context (W : sworld) (N : fuel).

  Definition chk_of (s : SynF) : ChkF := λ Θ Γ Δ F T,
    match s Θ Γ Δ F with
    | Some (T0, c) => if decide (tsub W Γ T0 T ∧ (tcontr T0 → tcontr T)) then Some c else None
    | None => None
    end.

  Definition no_syn : SynF := λ _ _ _ _, None.

  Fixpoint alg (t : aexpr) : SynF * ChkF :=
    match t with
    | AVar x =>
        let s : SynF := λ Θ Γ Δ F,
          if decide (dom Θ = ∅) then
            match Δ !! x with
            | Some (Some T) => if decide (lenv_unl (<[x := None]> Δ)) then Some (T, Some 0) else None
            | _ => None
            end
          else None in
        (s, chk_of s)
    | AUnit =>
        let s : SynF := λ Θ Γ Δ F,
          if decide (dom Θ = ∅ ∧ lenv_unl Δ) then Some (TUnit, Some 0) else None in
        (s, chk_of s)
    | AChan o =>
        let s : SynF := λ Θ Γ Δ F,
          if decide (dom Θ = {[o]}) then
            match Θ !! o with
            | Some (TE Ss x a m) => if decide (lenv_unl Δ ∧ fle a m) then Some (TSess Ss x a m, Some 0) else None
            | None => None
            end
          else None in
        (s, chk_of s)
    | ALam t =>
        (no_syn, λ Θ Γ Δ F T,
          match T with
          | TLolli ub lb c T1 U a =>
              if decide (lbx_below_h W Γ lb (tenv_heads Θ ∪ lenv_heads Δ) (lenv_bot Δ) ∧ tcontr T1) then
                match thage_f a Θ, lage_f a Δ with
                | Some Θh, Some Δh =>
                    match (alg t).2 Θh Γ (Some T1 :: Δh) (abs_fut ub) U with
                    | Some c0 => if decide (fle c0 c) then Some (Some 0) else None
                    | None => None
                    end
                | _, _ => None
                end
              else None
          | _ => None
          end)
    | AApp t1 t2 =>
        let s : SynF := λ Θ Γ Δ F,
          let Θs := tpart (erase t1) Θ in let Δs := lpart (erase t1) Δ in
          match (alg t1).1 Θs.1 Γ Δs.1 (fut1 F Θs.2 Δs.2) with
          | Some (TLolli ub lb c T U a1, c1) =>
              if decide (ub_below_u W Γ ub F) then
                match thage_f c1 Θs.2, lage_f c1 Δs.2 with
                | Some Θ2', Some Δ2' =>
                    match (alg t2).2 Θ2' Γ Δ2' (sf_unionb F (lb_heads lb) (lb_bot lb)) T with
                    | Some c2 => if decide (fle c2 a1) then Some (U, fadd c1 (fadd c2 c)) else None
                    | None => None
                    end
                | _, _ => None
                end
              else None
          | _ => None
          end in
        (s, chk_of s)
    | APair t1 t2 =>
        let s : SynF := λ Θ Γ Δ F,
          let Θs := tpart (erase t1) Θ in let Δs := lpart (erase t1) Δ in
          match (alg t1).1 Θs.1 Γ Δs.1 (fut1 F Θs.2 Δs.2) with
          | Some (T1, c1) =>
              match thage_f c1 Θs.2, lage_f c1 Δs.2 with
              | Some Θ2', Some Δ2' =>
                  match (alg t2).1 Θ2' Γ Δ2' (sf_unionb F (heads T1) (hbot T1)) with
                  | Some (T2, c2) =>
                      match tage_f c2 T1 with Some T1' => Some (TProd T1' T2, fadd c1 c2) | None => None end
                  | None => None
                  end
              | _, _ => None
              end
          | None => None
          end in
        (s, chk_of s)
    | ALetU t1 t2 =>
        (λ Θ Γ Δ F,
          let Θs := tpart (erase t1) Θ in let Δs := lpart (erase t1) Δ in
          match (alg t1).2 Θs.1 Γ Δs.1 (fut1 F Θs.2 Δs.2) TUnit with
          | Some c1 =>
              match thage_f c1 Θs.2, lage_f c1 Δs.2 with
              | Some Θ2', Some Δ2' =>
                  match (alg t2).1 Θ2' Γ Δ2' F with Some (T, c2) => Some (T, fadd c1 c2) | None => None end
              | _, _ => None
              end
          | None => None
          end,
         λ Θ Γ Δ F T,
          let Θs := tpart (erase t1) Θ in let Δs := lpart (erase t1) Δ in
          match (alg t1).2 Θs.1 Γ Δs.1 (fut1 F Θs.2 Δs.2) TUnit with
          | Some c1 =>
              match thage_f c1 Θs.2, lage_f c1 Δs.2 with
              | Some Θ2', Some Δ2' =>
                  match (alg t2).2 Θ2' Γ Δ2' F T with Some c2 => Some (fadd c1 c2) | None => None end
              | _, _ => None
              end
          | None => None
          end)
    | ALetP t1 t2 =>
        (λ Θ Γ Δ F,
          let Θs := tpart (erase t1) Θ in let Δs := lpart (erase t1) Δ in
          match (alg t1).1 Θs.1 Γ Δs.1 (fut1 F Θs.2 Δs.2) with
          | Some (TProd T1 T2, c1) =>
              match thage_f c1 Θs.2, lage_f c1 Δs.2 with
              | Some Θ2', Some Δ2' =>
                  match (alg t2).1 Θ2' Γ (Some T2 :: Some T1 :: Δ2') F with
                  | Some (T, c2) => Some (T, fadd c1 c2)
                  | None => None
                  end
              | _, _ => None
              end
          | _ => None
          end,
         λ Θ Γ Δ F T,
          let Θs := tpart (erase t1) Θ in let Δs := lpart (erase t1) Δ in
          match (alg t1).1 Θs.1 Γ Δs.1 (fut1 F Θs.2 Δs.2) with
          | Some (TProd T1 T2, c1) =>
              match thage_f c1 Θs.2, lage_f c1 Δs.2 with
              | Some Θ2', Some Δ2' =>
                  match (alg t2).2 Θ2' Γ (Some T2 :: Some T1 :: Δ2') F T with
                  | Some c2 => Some (fadd c1 c2)
                  | None => None
                  end
              | _, _ => None
              end
          | _ => None
          end)
    | AInj i t =>
        (no_syn, λ Θ Γ Δ F T,
          match T with
          | TSum T1 U1 => if decide (tcontr (TSum T1 U1)) then (alg t).2 Θ Γ Δ F (if i then U1 else T1) else None
          | _ => None
          end)
    | ACase t t1 t2 =>
        (no_syn, λ Θ Γ Δ F T,
          let Θs := tpart (erase t) Θ in let Δs := lpart (erase t) Δ in
          match (alg t).1 Θs.1 Γ Δs.1 (fut1 F Θs.2 Δs.2) with
          | Some (TSum T1 T2, c0) =>
              match thage_f c0 Θs.2, lage_f c0 Δs.2 with
              | Some Θ2', Some Δ2' =>
                  match (alg t1).2 Θ2' Γ (Some T1 :: Δ2') F T, (alg t2).2 Θ2' Γ (Some T2 :: Δ2') F T with
                  | Some c1, Some c2 => Some (fadd c0 (fmax c1 c2))
                  | _, _ => None
                  end
              | _, _ => None
              end
          | _ => None
          end)
    | ABox t =>
        (no_syn, λ Θ Γ Δ F T,
          match T with
          | TBox m k C ub c U =>
              if decide (dom Θ = ∅ ∧ lenv_unl Δ ∧ tcontr U ∧ lenv_contr Δ) then
                match (alg t).2 ∅ (hc_open m C Γ) (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ))
                        (∅, Some (rest_of ub)) (sinst_ty (slist (box_inst (box_base k U Δ) k)) U) with
                | Some c0 => if decide (fle c0 c) then Some (Some 0) else None
                | None => None
                end
              else None
          | _ => None
          end)
    | ANew C Ss m1 m2 =>
        let s : SynF := λ Θ Γ Δ F,
          if decide (dom Θ = ∅ ∧ lenv_unl Δ ∧ new_ok N W Γ C ∧ tsum_ok N m1 m2 ∧ scontr Ss) then
            Some (TEx LBot 1 C (TProd (TSess Ss (pvar 0) m1 m1) (TSess (dual Ss) (pvar 0)‾ m2 m2)), Some 0)
          else None in
        (s, chk_of s)
    | ANewF x κ Ss m1 m2 =>
        let s : SynF := λ Θ Γ Δ F,
          if decide (dom Θ = ∅ ∧ lenv_unl Δ ∧ tsum_ok N m1 m2 ∧ scontr Ss) then
            Some (TProd (TSess Ss (x·κ) m1 m1) (TSess (dual Ss) (x·κ)‾ m2 m2), Some 0)
          else None in
        (s, chk_of s)
    | AOp k t =>
        let s : SynF := λ Θ Γ Δ F,
          match k with
          | PSend =>
              match (alg t).1 Θ Γ Δ F with
              | Some (TProd Tp (TSess S0 x aS mS), c0) =>
                  match unfoldS S0 with
                  | SSeq (SSnd m T) Ss =>
                      match tage_f (Some 1) Tp with
                      | Some Tp' =>
                          if decide (pscoped m T ∧ below_ty W Γ x (payload_at m T x) ∧
                                     ub_below_s W Γ (Some x) F ∧ tsub W Γ Tp' (payload_at m T x))
                          then Some (TSess Ss x⁺ mS mS, fadd c0 (Some 1)) else None
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | PRecv =>
              match (alg t).1 Θ Γ Δ F with
              | Some (TSess S0 x a mS, c0) =>
                  match unfoldS S0 with
                  | SSeq (SRcv m T) Ss =>
                      if decide (pscoped m T ∧ ub_below_s W Γ (Some x) F)
                      then Some (TProd (payload_at m T x) (TSess Ss x⁺ mS mS), fadd c0 (Some 1)) else None
                  | _ => None
                  end
              | _ => None
              end
          | PClose =>
              match (alg t).1 Θ Γ Δ F with
              | Some (TSess S0 x a mS, c0) =>
                  match unfoldS S0 with
                  | SEnd => if decide (ub_below_s W Γ (Some x) F) then Some (TUnit, fadd c0 (Some 1)) else None
                  | _ => None
                  end
              | _ => None
              end
          | PSel i =>
              match (alg t).1 Θ Γ Δ F with
              | Some (TSess S0 x a mS, c0) =>
                  match unfoldS S0 with
                  | SPlus S1 S2 =>
                      if decide (ub_below_s W Γ (Some x) F)
                      then Some (TSess (if i then S2 else S1) (sel_pt x i) mS mS, fadd c0 (Some 1)) else None
                  | _ => None
                  end
              | _ => None
              end
          | PBra =>
              match (alg t).1 Θ Γ Δ F with
              | Some (TSess S0 x a mS, c0) =>
                  match unfoldS S0 with
                  | SWith S1 S2 =>
                      if decide (ub_below_s W Γ (Some x) F)
                      then Some (TSum (TSess S1 (bra_pt x false) mS mS) (TSess S2 (bra_pt x true) mS mS),
                                 fadd c0 (Some 1)) else None
                  | _ => None
                  end
              | _ => None
              end
          | PLink =>
              match (alg t).1 Θ Γ Δ F with
              | Some (TProd (TSess Ss x a1 m1) (TSess S' y a2 m2), c0) =>
                  if decide (S' = dual Ss ∧ y = x‾ ∧ lgt N a1 m2 ∧ lgt N a2 m1) then Some (TUnit, c0) else None
              | _ => None
              end
          | PSpawn =>
              match (alg t).1 Θ Γ Δ F with
              | Some (TLolli ub lb c' TUnit TUnit a, c0) => Some (TUnit, c0)
              | _ => None
              end
          | PForce => None
          end in
        (s, chk_of s)
    | AForce xs ss t =>
        let s : SynF := λ Θ Γ Δ F,
          match (alg t).1 Θ Γ Δ F with
          | Some (TBox m k C ub c U, c0) =>
              if decide (length xs = m ∧ hold_at W Γ C xs ∧ length ss = k ∧ sinsts N ss ∧
                         ub_below_s W Γ (pt_inst (plist xs) <$> ub) F)
              then Some (sinst_ty (slist ss) (ty_inst xs U), fadd c0 (fadd (Some 1) c)) else None
          | _ => None
          end in
        (s, chk_of s)
    | AAsc T c' t =>
        let s : SynF := λ Θ Γ Δ F,
          match (alg t).2 Θ Γ Δ F T with
          | Some c => if decide (fle c c') then Some (T, c') else None
          | None => None
          end in
        (s, chk_of s)
    | APack lb m C T xs t =>
        let s : SynF := λ Θ Γ Δ F,
          if decide (length xs = m ∧ hold_at W Γ C xs ∧
                     lbx_below_h W Γ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) ∧ ex_wf W Γ lb m C T) then
            match (alg t).2 Θ Γ Δ F (ty_inst xs T) with Some c => Some (TEx lb m C T, c) | None => None end
          else None in
        (s, chk_of s)
    | AOpen i U t =>
        let s : SynF := λ Θ Γ Δ F,
          match Δ !! i with
          | Some (Some (TEx lb m C T)) =>
              if decide (¬ unlimited T ∧ cons_open W Γ m C) then
                match (alg t).2 (tenv_pinst (pshift m) Θ) (hc_open m C Γ)
                        (<[i := Some T]> (lenv_pinst (pshift m) Δ)) (sf_pinst (pshift m) F)
                        (pinst_ty (pshift m) U) with
                | Some c => Some (U, c)
                | None => None
                end
              else None
          | _ => None
          end in
        (s, chk_of s)
    end.

  Lemma alg_by_sub t Θ Γ Δ F T :
    by_sub t = true → (alg t).2 Θ Γ Δ F T = chk_of (alg t).1 Θ Γ Δ F T.
  Proof. destruct t; done. Qed.

  Lemma chk_of_sound t (s : SynF) :
    by_sub t = true →
    (∀ Θ Γ Δ F T c, s Θ Γ Δ F = Some (T, c) → syn W N Θ Γ Δ F t T c) →
    ∀ Θ Γ Δ F T c, chk_of s Θ Γ Δ F T = Some c → chk W N Θ Γ Δ F t T c.
  Proof.
    intros Hb Hs Θ Γ Δ F T c Hc. unfold chk_of in Hc.
    destruct (s Θ Γ Δ F) as [[T0 c0]|] eqn:E; [|done].
    case_decide as Hd; [|done]. simplify_eq. destruct Hd as [Hsub Hct].
    eapply c_sub; [done|by apply Hs|done|done].
  Qed.

  Lemma tpart_pair e Θ : tpart e Θ = ((tpart e Θ).1, (tpart e Θ).2).
  Proof. by destruct (tpart e Θ). Qed.
  Lemma lpart_pair e Δ : lpart e Δ = ((lpart e Δ).1, (lpart e Δ).2).
  Proof. by destruct (lpart e Δ). Qed.

  Local Arguments tpart : simpl never.

  Local Ltac opt_inv H :=
    repeat (cbn [alg fst snd chk_of no_syn] in H; first
      [ discriminate H
      | match type of H with
        | (match ?x with _ => _ end) = _ => destruct x eqn:?
        end ]);
    repeat match goal with Hd : decide _ = _ |- _ => clear Hd end;
    simplify_eq; destruct_and?.

  Local Ltac use_ih :=
    match goal with
    | IH : ∀ _ _ _ _ _ _, (alg ?t).1 _ _ _ _ = _ → syn _ _ _ _ _ _ ?t _ _
      |- syn _ _ _ _ _ _ ?t _ _ => eapply IH; eassumption
    | IH : ∀ _ _ _ _ _ _, (alg ?t).2 _ _ _ _ _ = _ → chk _ _ _ _ _ _ ?t _ _
      |- chk _ _ _ _ _ _ ?t _ _ => eapply IH; eassumption
    | IH : (∀ _ _ _ _ _ _, (alg ?t).1 _ _ _ _ = _ → syn _ _ _ _ _ _ ?t _ _) ∧ _
      |- syn _ _ _ _ _ _ ?t _ _ => eapply (proj1 IH); eassumption
    | IH : _ ∧ (∀ _ _ _ _ _ _, (alg ?t).2 _ _ _ _ _ = _ → chk _ _ _ _ _ _ ?t _ _)
      |- chk _ _ _ _ _ _ ?t _ _ => eapply (proj2 IH); eassumption
    end.

  Local Ltac discharge :=
    repeat first
      [ eassumption | reflexivity | use_ih
      | (rewrite tpart_pair; reflexivity) | (rewrite lpart_pair; reflexivity)
      | (apply tage_f_spec; eassumption) | (apply thage_f_spec; eassumption)
      | (apply lage_f_spec; eassumption) | (apply lenv_only_iff; split; eassumption) ].

  Local Ltac prep :=
    repeat match goal with
    | H : dom ?Θ = ∅ |- _ => apply dom_empty_inv_L in H; subst Θ
    | Hd : dom ?Θ = {[?o]}, He : ?Θ !! ?o = Some _ |- _ =>
        rewrite (dom_singleton_inv _ _ _ Hd He); clear Hd He
    end.

  Theorem alg_sound t :
    (∀ Θ Γ Δ F T c, (alg t).1 Θ Γ Δ F = Some (T, c) → syn W N Θ Γ Δ F t T c) ∧
    (∀ Θ Γ Δ F T c, (alg t).2 Θ Γ Δ F T = Some c → chk W N Θ Γ Δ F t T c).
  Proof.
    induction t as [x| |o|t IH|t1 IH1 t2 IH2|t1 IH1 t2 IH2|t1 IH1 t2 IH2|t1 IH1 t2 IH2|i t IH|t IH t1 IH1 t2 IH2
                   |t IH|C Ss m1 m2|x κ Ss m1 m2|k t IH|xs ss t IH|T c' t IH|lb m C T xs t IH|i U t IH].
    all: match goal with |- (∀ _ _ _ _ _ _, (alg ?t).1 _ _ _ _ = _ → _) ∧ _ =>
      assert (∀ Θ Γ Δ F T c, (alg t).1 Θ Γ Δ F = Some (T, c) → syn W N Θ Γ Δ F t T c) as Hsyn end;
      [intros Θ Γ Δ F T0 c0 Hs; opt_inv Hs; prep; try subst; try (econstructor; discharge; fail)|].
    all: split; [exact Hsyn|].
    all: intros Θ Γ Δ F T0 c0 Hs.
    all: first [ by eapply chk_of_sound; [reflexivity|exact Hsyn|exact Hs]
               | opt_inv Hs; prep; econstructor; discharge; fail ].
  Qed.

  Local Ltac solve_side :=
    split_and?; first [assumption | reflexivity | apply dom_empty_L | apply dom_singleton_L | done].

  Local Ltac crunch :=
    repeat (cbn [alg fst snd chk_of no_syn]; first
      [ reflexivity
      | match goal with
        | H : tpart _ _ = _ |- _ => rewrite H
        | H : lpart _ _ = _ |- _ => rewrite H
        | H : (alg _).1 _ _ _ _ = _ |- _ => rewrite H
        | H : (alg _).2 _ _ _ _ _ = _ |- _ => rewrite H
        | H : thage _ _ _ |- _ => rewrite (proj1 (thage_f_spec _ _ _) H)
        | H : lage _ _ _ |- _ => rewrite (proj1 (lage_f_spec _ _ _) H)
        | H : tage _ _ _ |- _ => rewrite (proj1 (tage_f_spec _ _ _) H)
        | H : unfoldS _ = _ |- _ => rewrite H
        | H : _ !! _ = Some _ |- _ => rewrite H
        end
      | rewrite lookup_singleton_eq
      | rewrite decide_True by solve_side ]).

  Theorem alg_complete :
    (∀ Θ Γ Δ F t T c, syn W N Θ Γ Δ F t T c → (alg t).1 Θ Γ Δ F = Some (T, c)) ∧
    (∀ Θ Γ Δ F t T c, chk W N Θ Γ Δ F t T c → (alg t).2 Θ Γ Δ F T = Some c).
  Proof.
    apply syn_chk_mut; intros.
    all: try (match goal with H : lenv_only _ _ _ |- _ => apply lenv_only_iff in H as [? ?] end).
    all: first [ rewrite alg_by_sub by assumption; unfold chk_of | idtac ].
    all: crunch.
  Qed.

  (** ** Decidability and syntax-directedness *)

  Theorem syn_det Θ Γ Δ F t T c T' c' :
    syn W N Θ Γ Δ F t T c → syn W N Θ Γ Δ F t T' c' → T = T' ∧ c = c'.
  Proof.
    intros Ha Hb. apply (proj1 alg_complete) in Ha, Hb. rewrite Ha in Hb. by simplify_eq.
  Qed.

  Theorem chk_det Θ Γ Δ F t T c c' :
    chk W N Θ Γ Δ F t T c → chk W N Θ Γ Δ F t T c' → c = c'.
  Proof.
    intros Ha Hb. apply (proj2 alg_complete) in Ha, Hb. rewrite Ha in Hb. by simplify_eq.
  Qed.

  Theorem syn_dec Θ Γ Δ F t :
    {Tc | syn W N Θ Γ Δ F t Tc.1 Tc.2} + {∀ T c, ¬ syn W N Θ Γ Δ F t T c}.
  Proof.
    destruct ((alg t).1 Θ Γ Δ F) as [[T c]|] eqn:E.
    - left. exists (T, c). by apply (proj1 (alg_sound t)).
    - right. intros T c Hs. apply (proj1 alg_complete) in Hs. congruence.
  Defined.

  Theorem chk_dec Θ Γ Δ F t T :
    {c | chk W N Θ Γ Δ F t T c} + {∀ c, ¬ chk W N Θ Γ Δ F t T c}.
  Proof.
    destruct ((alg t).2 Θ Γ Δ F T) as [c|] eqn:E.
    - left. exists c. by apply (proj2 (alg_sound t)).
    - right. intros c Hs. apply (proj2 alg_complete) in Hs. congruence.
  Defined.

  (** Typing an annotated term is decidable relative to the oracles:
      the algorithm either returns a declarative derivation of the
      erasure, or no algorithmic derivation exists. *)
  Corollary typed_annot_dec Θ Γ Δ F t :
    {Tc | typed W N Θ Γ Δ F (erase t) Tc.1 Tc.2 ∧ syn W N Θ Γ Δ F t Tc.1 Tc.2} +
    {∀ T c, ¬ syn W N Θ Γ Δ F t T c}.
  Proof.
    destruct (syn_dec Θ Γ Δ F t) as [[Tc Hs]|Hs]; [left|right; exact Hs].
    exists Tc. split; [by apply (proj1 (algo_sound W N))|exact Hs].
  Defined.
End alg.
