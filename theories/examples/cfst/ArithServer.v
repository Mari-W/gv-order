(** * The arithmetic expression server (Thiemann and Vasconcelos 2016, Listing 3, stage D)

      TermC = µX. ⊕(!∗, ⊕(X;X, X;X))
      TermD = dual TermC = µX. &(?∗, &(X;X, X;X))

    The ternary choice {Const, Add, Mult} of TermChan becomes binary
    choices, Const = select₁, Add = select₂ select₁, Mult = select₂
    select₂. Int becomes ∗. [receiveEval] serves TermD;β. On Const it
    receives the constant, on Add and Mult it recurses on both subterms.
    The paper returns n₁+n₂ or n₁∗n₂ next to the channel. The calculus
    has no integers, so receiveEval returns the channel alone, and the
    Add and Mult branches run the same code.

      receiveEval : □(∀κ ζ β. C. ∗ ⊸ ((TermD;β)@κ ⊸^ζ ∃κ′≽κ. C′. β@κ′))
      C  = {κ·w ≺ ζ, κ·w ≺ (κ·w)[i] ∣ w, i}
      C′ = {κ ≺ κ′} ∪ C[κ′/κ]

    Add and Mult run the same code, at the two points κ[B][A] and
    κ[B][B] where the inner choice continues (K11). The proof types it
    once for both.

    computeService runs receiveEval on TermD;(!∗;Close) and sends the
    result. The client is the paper's, Add (Const 5) (Mult (Const 7)
    (Const 9)) followed by a receive, as a fixed sequence of selections
    and sends. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.TreeSum.

Set Default Proof Using "All".

Definition TermC : sty :=
  SMu (SPlus (SSnd 0 TUnit) (SPlus (SSeq (SVar 0) (SVar 0)) (SSeq (SVar 0) (SVar 0)))).

Definition TermD : sty :=
  SMu (SWith (SRcv 0 TUnit) (SWith (SSeq (SVar 0) (SVar 0)) (SSeq (SVar 0) (SVar 0)))).

(** The choice between Add and Mult. *)
Definition OpC : sty := SPlus (SSeq TermC TermC) (SSeq TermC TermC).
Definition OpD : sty := SWith (SSeq TermD TermD) (SSeq TermD TermD).

Lemma dual_TermC : dual TermC = TermD.
Proof. reflexivity. Qed.

Lemma unfoldS_TermC : unfoldS TermC = SPlus (SSnd 0 TUnit) OpC.
Proof. reflexivity. Qed.

Lemma unfoldS_TermD : unfoldS TermD = SWith (SRcv 0 TUnit) OpD.
Proof. reflexivity. Qed.

Lemma TermC_contractive : contractive TermC.
Proof. unfold contractive. by rewrite unfoldS_TermC. Qed.

Lemma TermD_contractive : contractive TermD.
Proof. unfold contractive. by rewrite unfoldS_TermD. Qed.

Lemma TermC_hc : hcontractive TermC.
Proof.
  apply (hc_ind (λ s, s = TermC)); [|done]. intros n s -> IH.
  specialize (IH TermC eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_TermC). cbn [view]. split; [apply hcontractive_snd|].
  destruct n as [|m]; [done|]. rewrite ahc_S. unfold hc_step, OpC.
  rewrite (hd_of _ _ (unfoldS_plus _ _)). cbn [view].
  pose proof (ahc_mono (S m) m TermC ltac:(lia) IH) as IH'. split; by apply ahc_seq.
Qed.

Lemma TermD_hc : hcontractive TermD.
Proof.
  apply (hc_ind (λ s, s = TermD)); [|done]. intros n s -> IH.
  specialize (IH TermD eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_TermD). cbn [view]. split; [apply hcontractive_rcv|].
  destruct n as [|m]; [done|]. rewrite ahc_S. unfold hc_step, OpD.
  rewrite (hd_of _ _ (unfoldS_with _ _)). cbn [view].
  pose proof (ahc_mono (S m) m TermD ltac:(lia) IH) as IH'. split; by apply ahc_seq.
Qed.

(** The heads of TermC;s and TermD;s. *)
Lemma TermC_seq s : seq (SSeq TermC s) (SPlus (SSeq (SSnd 0 TUnit) s) (SSeq OpC s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply TermC_contractive|by rewrite unfoldS_TermC].
  by rewrite unfoldS_TermC, unfoldS_plus.
Qed.

Lemma TermD_seq s : seq (SSeq TermD s) (SWith (SSeq (SRcv 0 TUnit) s) (SSeq OpD s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply TermD_contractive|by rewrite unfoldS_TermD].
  by rewrite unfoldS_TermD, unfoldS_with.
Qed.

(** Add and Mult distributed over the continuation and reassociated. *)
Lemma opC_seq s : hcontractive s →
  seq (SSeq OpC s) (SPlus (SSeq TermC (SSeq TermC s)) (SSeq TermC (SSeq TermC s))).
Proof.
  intros Hs. eapply seq_trans; [apply seq_choice_dist_plus|].
  apply seq_plus_cong; apply seq_assoc; auto using TermC_hc.
Qed.

Lemma opD_seq s : hcontractive s →
  seq (SSeq OpD s) (SWith (SSeq TermD (SSeq TermD s)) (SSeq TermD (SSeq TermD s))).
Proof.
  intros Hs. eapply seq_trans; [apply seq_choice_dist_with|].
  apply seq_with_cong; apply seq_assoc; auto using TermD_hc.
Qed.

(** The point κ[B][i] of a point variable κ = a, where the choice
    between Add and Mult continues. *)
Abbreviation pop a i := (Pt (NPayload (NPayload (NVar a) 0 1) 0 (bidx i)) 0).

(** ** receiveEval *)

Definition reval_body : ty :=
  TLolli (Some (pv 1 0)) None (TSess (SSeq TermD (SVar 0)) (pv 0 0)) send_after.

Definition reval_ty : ty := TBox 2 1 send_C (TLolli None None TUnit reval_body).

(** Add and Mult: two recursive calls, the second inside an open and
    re-pack, as in drain. *)
Definition reval_op : expr :=
  App (Lam (App (Lam (Var 0)) (App (App EForce (Var 4)) (Var 0))))
      (App (App EForce (Var 3)) (Var 0)).

Definition reval : expr :=
  EBox (Lam (Case (App EBra (Var 0))
    (LetP (App ERecv (Var 0)) (LetU (Var 1) (Var 0)))
    (Case (App EBra (Var 0)) reval_op reval_op))).

Lemma reval_ty_pscoped : pscoped 0 reval_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma reval_inst x z s :
  sinst_ty (slist [s]) (ty_inst [x; z] reval_body) =
  TLolli (Some z) None (TSess (SSeq TermD s) x)
    (TEx (LPt x) 1 (BCs [x; z] after_P) (TSess s (pv 0 0))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma reval_typed W F : world_wf W → typed W ∅ [] ∅ [] F reval reval_ty.
Proof.
  intros HW. unfold reval, reval_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  intros ss Hss Hhc. destruct ss as [|s [|]]; try discriminate Hss.
  rewrite Forall_singleton in Hhc. fold reval_ty.
  change (lenv_pinst (pshift 2) [Some reval_ty]) with [Some (pinst_ty (pshift 2) reval_ty)].
  rewrite (pinst_closed _ reval_ty) by apply reval_ty_pscoped.
  cbn. fold TermD. change (bcs_inst (pshift 2) send_C) with send_C.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 0))
              (TSess (SWith (SSeq (SRcv 0 TUnit) s) (SSeq OpD s)) (pv 0 0))).
    + eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TermD_seq].
    + apply KTBra; [hypbc true ([] : list (option bool)) false false|hypbc true ([] : list (option bool)) true false].
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hypw ([] : list (option bool)).
  - (* Const: receive, then pack at κ[A]+1 *)
    cbn. apply (t_pack W _ _ _ _ _ _ (LPt (pv 0 0)) 1 after_C (TSess s (pv 0 0)) [psl 0 false 1]).
    + done.
    + apply Forall_singleton. apply (skn_in W _ send_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done].
    + unfold after_C. apply bcs_hold_env. intros f [(c & c' & ->) | (w & c & c' & [-> | (i & ->)])] _;
        cbn [fact_map fact_holds]; rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst.
      * destruct c'; (eapply sl_trans; [hypbc c ([] : list (option bool)) false true|]);
          [apply (slt_po W _ (psl 0 false 0) HW)|apply (sl_dpo W _ (psl 0 false 0))].
      * hypwc c (Some false :: None :: w).
      * hypbc c (Some false :: None :: w) i c'.
    + split; [|done]. intros y Hy. mem_cases Hy. right.
      eapply sl_trans; [hypb ([] : list (option bool)) false|apply (sl_dpo W _ (psl 0 false 0))].
    + cbn. tstep.
      { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (psl 0 false 0)) (TSess (SSeq (SRcv 0 TUnit) s) (psl 0 false 0))).
        - tstep.
        - apply KTRecv.
        - kscope.
        - apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 1 0). split; [done|]. right. hypw [Some false]. }
      cbn. tstep; [tstep|]. tstep.
  - (* Add or Mult: the same code at κ[B][A] and κ[B][B] *)
    cbn.
    match goal with |- typed ?W' ?Φ ?Ψ _ ?Δ ?F (Case _ ?e1 ?e2) ?T =>
      assert (∀ i, typed W' Φ Ψ ∅ (Some (TSess (SSeq TermD (SSeq TermD s)) (pop 0 i))
                                     :: lp (Lam (Pair e1 e2)) 0 Δ) F e1 T) as Hop end.
    2:{ eapply (tv_case W HW _ _ _ _ _ _ _ (TSess (SSeq TermD (SSeq TermD s)) (pop 0 false))
                  (TSess (SSeq TermD (SSeq TermD s)) (pop 0 true))); [reflexivity| |apply Hop|apply Hop].
        eapply (tv_appk W HW _ _ _ _ KBra _ (Some (psl 0 true 0))
                  (TSess (SWith (SSeq TermD (SSeq TermD s)) (SSeq TermD (SSeq TermD s))) (psl 0 true 0))).
        - eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply opD_seq].
        - apply KTBra; [hypbc true [Some true] false false|hypbc true [Some true] true false].
        - done.
        - apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 1 0). split; [done|]. right. hypw [Some true]. }
    intros i. unfold reval_op. cbn.
    set (R1 := TEx (LPt (pop 0 i)) 1 (BCs [pop 0 i; pv 1 0] after_P) (TSess (SSeq TermD s) (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 1 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pop 0 i)) 1 (BCs [pop 0 i; pv 1 0] after_P)
                  (TSess (SSeq TermD s) (pv 0 0)) _
                  (<[2:=Some (pv 2 0)]> (<[1:=Some (pv 2 0)]> (<[0:=None]> ∅)))
                  [(send_C, [pv 1 0; pv 2 0]); (BCs [pop 1 i; pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq TermD s) (pv 0 0)); None; None; None; Some reval_ty]
                  (∅, Some (FVar 2))
                  (TEx (LPt (pv 1 0)) 1 (BCs [pv 1 0; pv 2 0] after_P) (TSess s (pv 0 0))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (R2 := TEx (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P) (TSess s (pv 0 0))).
      assert (∀ Ψ, (BCs [pop 1 i; pv 2 0] after_P, [pv 0 0]) ∈ Ψ → (send_C, [pv 1 0; pv 2 0]) ∈ Ψ →
                   Forall (skn W Ψ) [pv 0 0; pv 2 0]) as Hkn.
      { intros Ψ H1 H2. apply Forall_cons. split; [|apply Forall_singleton].
        - apply (skn_in W Ψ (BCs [pop 1 i; pv 2 0] after_P) [pv 0 0] (pv 0 0)); [exact H1|by left|done].
        - apply (skn_in W Ψ send_C [pv 1 0; pv 2 0] (pv 2 0)); [exact H2|by right; left|done]. }
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None R2); [reflexivity| | |].
      * eapply (tv_lam W HW _ _ _ _ _ R2 _ (Some (pv 2 0)) None 3); [set_solver|cbn; set_solver|].
        cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P)
                  (TSess s (pv 0 0)) _
                  (<[3:=Some (pv 3 0)]> (<[2:=Some (pv 3 0)]> (<[1:=Some (pv 3 0)]> (<[0:=None]> ∅))))
                  [(send_C, [pv 2 0; pv 3 0]); (BCs [pop 2 i; pv 3 0] after_P, [pv 1 0]);
                   (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]
                  [Some (TSess s (pv 0 0)); None; None; None; None; Some reval_ty]
                  (∅, Some (FVar 3))
                  (TEx (LPt (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0))));
          [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
        assert (∀ c c', slt W [(send_C, [pv 2 0; pv 3 0]); (BCs [pop 2 i; pv 3 0] after_P, [pv 1 0]);
                       (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])] (pt_polar c (pv 2 0)) (pt_polar c' (pv 0 0))) as Hch.
        { intros c c'. apply (sl_trans _ _ _ (psl 2 true 0)).
          { eapply (sl_hyp0 _ _ send_P _ (pt_polar c (pv 0 0)) (wstep (pv 0 0) (Some true)));
              [inlist|exists [], c, true; right; by exists true|destruct c; fscw|by destruct c|reflexivity]. }
          apply (sl_trans _ _ _ (pop 2 i)).
          { eapply (sl_hyp0 _ _ send_P _ (pwalk (pv 0 0) [Some true]) (wstep (pwalk (pv 0 0) [Some true]) (Some i)));
              [inlist|exists [Some true], true, true; right; by exists i|fscw|reflexivity|reflexivity]. }
          eapply sl_trans.
          - eapply (sl_hyp W _ [pop 2 i; pv 3 0] after_P [pv 1 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|left; by exists true, true|fsc|reflexivity].
          - eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 1 0) (pt_polar c' (pv 0 0))));
              [inlist|left; by exists true, c'|destruct c'; fsc|by destruct c']. }
        apply (t_pack W _ _ _ _ _ _ (LPt (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0)) [pv 0 0]).
        -- done.
        -- apply Forall_singleton.
           apply (skn_in W _ (BCs [pv 1 0; pv 3 0] after_P) [pv 0 0] (pv 0 0)); [inlist|by left|done].
        -- apply bcs_hold_env. intros f [(c & c' & ->) | (w & c & c' & [-> | (j & ->)])] _;
             cbn [fact_map fact_holds]; rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst; [apply Hch| |].
           ++ hypawc [pv 1 0; pv 3 0] [pv 0 0] c w.
           ++ hypabc [pv 1 0; pv 3 0] [pv 0 0] c w j c'.
        -- split; [|done]. intros y Hy. mem_cases Hy. right. apply (Hch true false).
        -- cbn. tstep.
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq TermD s) (pv 0 0)) R2);
          [reflexivity| | |].
        -- unfold R2. rewrite <-(reval_inst (pv 0 0) (pv 2 0) s).
           apply (typed_force W _ _ _ _ _ _ 2 1 send_C None reval_body [pv 0 0; pv 2 0] [s]);
             [done|done| | |done| |apply ubs_none|tstep].
           ++ apply bcs_hold_intro. intros g (w & c & c' & [-> | (j & ->)]) _;
                cbn [fact_map fact_holds]; rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst.
              ** hypawc [pop 1 i; pv 2 0] [pv 0 0] c w.
              ** hypabc [pop 1 i; pv 2 0] [pv 0 0] c w j c'.
           ++ apply Hkn; inlist.
           ++ by apply Forall_singleton.
        -- tstep.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy|].
           exists (pv 2 0). split; [done|]. apply sle_refl, HW.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. apply sle_refl, HW.
    + eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None
                (TSess (SSeq TermD (SSeq TermD s)) (pop 0 i)) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(reval_inst (pop 0 i) (pv 1 0) (SSeq TermD s)).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None reval_body [pop 0 i; pv 1 0] [SSeq TermD s]);
          [done|done| | |done| |apply ubs_none|tstep].
        -- apply bcs_hold_self; [by left|vb_list|]. intros g (w & c & c' & [-> | (j & ->)]) _;
             exists (Some true :: Some i :: w), c, c'; [left|right; exists j]; fmwp.
        -- apply (skn_ids2 W _ send_C); [by left|done|done].
        -- apply Forall_singleton, hcontractive_seq; [apply TermD_hc|done].
      * tstep.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

(** ** The closed program go

      go = let (re, re′) = ⟨receiveEval, receiveEval⟩ in
           let (c, s) = new ∗ in
           spawn (λu. let () = u in close (send ⟨∗, open (force re′ s)⟩));
           let (_, c′) = recv (send ⟨∗, select₁ (send ⟨∗, select₁ (select₂ (select₂
                           (send ⟨∗, select₁ (select₁ (select₂ c))⟩)))⟩)⟩) in
           close c′

    The spawned thread is computeService. The client sends Add (Const 5)
    (Mult (Const 7) (Const 9)) with ∗ for the constants and receives the
    result. The ends have type TermC;(?∗;Close) and TermD;(!∗;Close) at
    the point α of c, and the client acts at the points [asp k] of its
    walk from α. As in TreeSum.v the top-level point z is the ceiling of
    receiveEval, and c is created with the facts of C at α and z
    ([tca_C] of TreeCopy.v). With end points [asp k] is dual after the
    client's first choice, and computeService holds the other end at
    ᾱ. *)

(** The client's walk: Op, Add, Const, send 5, Op, Mult, Const, send 7,
    Const, send 9, recv. *)
Definition as_cw : list (option bool) :=
  [Some true; Some false; Some false; None; Some true; Some true; Some false; None;
   Some false; None; None].
Definition asp (k : nat) : point :=
  pt_polar (negb (wpol (take k as_cw))) (pwalk (pc 0 0) (take k as_cw)).

Definition as_srv : expr :=
  LetU (Var 0) (App (Lam (App EClos (App ESend (Pair EUnit (Var 0)))))
                    (App (App EForce (Var 3)) (Var 1))).

Definition as_cli : expr :=
  LetP (App ERecv (App ESend (Pair EUnit (App ESel1 (App ESend (Pair EUnit
          (App ESel1 (App ESel2 (App ESel2 (App ESend (Pair EUnit
            (App ESel1 (App ESel1 (App ESel2 (Var 1)))))))))))))))
    (LetU (Var 1) (App EClos (Var 0))).

Definition as_go : expr :=
  LetP (Pair reval reval) (let_new_pair_at (EPt (pconst 0)) (LetU (App ESpawn (Lam as_srv)) as_cli)).

(** The client's continuation, the reply. *)
Definition as_Q : sty := SSeq (SRcv 0 TUnit) SEnd.

(** After the [new] a is 0 and z is 1. *)
Lemma as_typed : styped ∅ tca_Ψ [] (∅, None) as_go TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold as_go, let_new_pair_at, tca_Ψ.
  assert (hcontractive as_Q) as HQ by (apply hcontractive_seq; [apply hcontractive_rcv|apply hcontractive_end]).
  assert (hcontractive (SSeq TermC as_Q)) as HQ' by (apply hcontractive_seq; [apply TermC_hc|exact HQ]).
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply reval_typed, HW|exact HWs|apply reval_typed, HW]. }
  cbn. new_top HWs (SSeq TermC as_Q) (pconst 0).
  fresh_clean.
  set (Ψ := [(top_C0, [pconst 1]); (BCs [pconst 1] send_P, [pconst 0])]).
  assert (∀ w c, slt W Ψ (pt_polar c (pwalk (pc 0 0) w)) (pc 1 0)) as Haz.
  { intros w c. eapply (sl_hyp W Ψ [pconst 1] send_P [pconst 0] (FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 1 0)));
      [inlist|exists w, c, true; by left|fscp|fmwp]. }
  assert (∀ w i c c', slt W Ψ (pt_polar c (pwalk (pc 0 0) w)) (pt_polar c' (wstep (pwalk (pc 0 0) w) (Some i)))) as Haa.
  { intros w i c c'. eapply (sl_hyp W Ψ [pconst 1] send_P [pconst 0]
                          (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i)))));
      [inlist|exists w, c, c'; right; by exists i|fscp|fmwp]. }
  cbn. tstep.
  { (* computeService *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold as_srv. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pt_dual (pc 0 0))) 1 (BCs [pt_dual (pc 0 0); pc 1 0] after_P) (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pc 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pt_dual (pc 0 0))) 1 (BCs [pt_dual (pc 0 0); pc 1 0] after_P)
                  (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0)) _
                  (<[1:=Some (pc 1 0)]> (<[0:=Some (pc 1 0)]> ∅))
                  [(top_C0, [pconst 1]); (BCs [pconst 1] send_P, [pconst 0]); (BCs [pt_dual (pc 0 0); pc 1 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0)); None; None; None; None; None;
                   Some reval_ty; Some reval_ty]
                  (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      assert (∀ w, slt W [(top_C0, [pconst 1]); (BCs [pconst 1] send_P, [pconst 0]); (BCs [pt_dual (pc 0 0); pc 1 0] after_P, [pv 0 0])]
                     (pwalk (pv 0 0) w) (pc 1 0)) as Hz'.
      { intros w. hypaw [pt_dual (pc 0 0); pc 1 0] [pv 0 0] w. }
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 1)) (TSess SEnd (pv 0 1)));
        [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|]].
      + eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
                  (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0)))).
        * tstep; [|tstep]. tstep.
        * apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)). cbn. set_solver.
        * kscope.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 1 0). split; [done|]. right. apply (Hz' []).
      + exists (pc 1 0). split; [done|]. right. apply (Hz' [None]).
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 1 0)) None
                (TSess (SSeq TermD (SSeq (SSnd 0 TUnit) SEnd)) (pt_dual (pc 0 0))) RD); [reflexivity| | |].
      + unfold RD. rewrite <-(reval_inst (pt_dual (pc 0 0)) (pc 1 0) (SSeq (SSnd 0 TUnit) SEnd)).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None reval_body [pt_dual (pc 0 0); pc 1 0] [SSeq (SSnd 0 TUnit) SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & c & c' & [-> | (i & ->)]) _; cbn [fact_map fact_holds];
            pnorm; [eapply Haz|eapply Haa].
        * constructor; [eapply skn_inst; [by right; left|by left|done]|].
          constructor; [eapply skn_inst; [by left|by left|done]|constructor].
        * apply Forall_singleton, hcontractive_seq; [apply hcontractive_snd|apply hcontractive_end].
      + tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 1 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 0). split; [done|]. apply sle_refl, HW. }
  (* the client *)
  unfold as_cli. cbn. tstep.
  - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (asp 10)) (TSess as_Q (asp 10)));
      [|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* asp 9: Const 9 *)
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (asp 9))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) as_Q) (asp 9))));
      [|apply (KTSend _ _ _ 0 TUnit as_Q (asp 9)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (asp 8))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) as_Q) (SSeq OpC as_Q)) (asp 8)));
      [|apply KTSel1, (Haa (take 8 as_cw) false (negb (wpol (take 8 as_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* asp 8: TermC;Q after the send of 7 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TermC as_Q) (asp 8))).
    { apply teq_steq. split; [done|apply TermC_seq]. }
    (* asp 7: Const 7 *)
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (asp 7))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TermC as_Q)) (asp 7))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq TermC as_Q) (asp 7)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (asp 6))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) (SSeq TermC as_Q)) (SSeq OpC (SSeq TermC as_Q))) (asp 6)));
      [|apply KTSel1, (Haa (take 6 as_cw) false (negb (wpol (take 6 as_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* asp 6: TermC;(TermC;Q) after Mult *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TermC (SSeq TermC as_Q)) (asp 6))).
    { apply teq_steq. split; [done|apply TermC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (asp 5))
              (TSess (SPlus (SSeq TermC (SSeq TermC as_Q)) (SSeq TermC (SSeq TermC as_Q))) (asp 5)));
      [|apply KTSel2, (Haa (take 5 as_cw) true (negb (wpol (take 5 as_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq OpC as_Q) (asp 5))).
    { apply teq_steq. split; [done|by apply opC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (asp 4))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) as_Q) (SSeq OpC as_Q)) (asp 4)));
      [|apply KTSel2, (Haa (take 4 as_cw) true (negb (wpol (take 4 as_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* asp 4: TermC;Q after the send of 5 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TermC as_Q) (asp 4))).
    { apply teq_steq. split; [done|apply TermC_seq]. }
    (* asp 3: Const 5 *)
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (asp 3))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TermC as_Q)) (asp 3))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq TermC as_Q) (asp 3)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (asp 2))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) (SSeq TermC as_Q)) (SSeq OpC (SSeq TermC as_Q))) (asp 2)));
      [|apply KTSel1, (Haa (take 2 as_cw) false (negb (wpol (take 2 as_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* asp 2: TermC;(TermC;Q) after Add *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TermC (SSeq TermC as_Q)) (asp 2))).
    { apply teq_steq. split; [done|apply TermC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (asp 1))
              (TSess (SPlus (SSeq TermC (SSeq TermC as_Q)) (SSeq TermC (SSeq TermC as_Q))) (asp 1)));
      [|apply KTSel1, (Haa (take 1 as_cw) false (negb (wpol (take 1 as_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq OpC as_Q) (asp 1))).
    { apply teq_steq. split; [done|by apply opC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pc 0 0))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) as_Q) (SSeq OpC as_Q)) (pc 0 0)));
      [|apply KTSel2, (Haa [] true true true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TermC_seq].
  - (* the result and close *)
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (asp 11)) (TSess SEnd (asp 11)));
      [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
Qed.

Theorem as_deadlock_free : deadlock_free (∅, {[+ as_go +]}).
Proof. apply (soundness_created_s tca_Ψ _ TUnit tca_created); [constructor|apply as_typed]. Qed.
