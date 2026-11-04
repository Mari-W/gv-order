(** * A held channel sent at the first action inside a segment function

      fa : □(∀κ ι ζ a. C. ∗ ⊸ ((!(Close);XformD;a)@κ ⊗ Close@ι ⊸^ζ
                                ∃κ′≽κ+1. C′. a@κ′))
      C  = {ι ≡ κ[0]} ∪ {κ·w ≺ ζ, κ·w ≺ (κ·w)[i] ∣ w, i}
      fa ⟨c, d⟩ = treeSum (send ⟨d, c⟩)

      fa_go = let (c, s) = new in
              let (d, d′) = new at α[0] in
              spawn (λu. close d′);
              spawn (λu. close (open (fa ⟨c, d⟩)));
              let (e, s) = recv s in spawn (λu. close e);
              the client of TreeSum.v on s

    This is fa_main of mordido-perez.md (section "Gaps checked against
    the core"). The caller holds d and passes it to fa with c. The
    first action of fa sends d on c at κ. O-Send asks the payload's
    point to be the payload point κ[0] of the carrier ([payload_at]),
    and the box constraint states ι ≡ κ[0] for the point ι of d, so
    E-Conv moves d to κ[0] before the send. The caller creates d at
    the payload point α[0] of its channel c at α and forces fa at
    [α; α[0]; z], where ι ≡ κ[0] holds by reflexivity. Then fa calls
    treeSum at κ+1 with the walk facts of C from κ+1 and returns its
    result. The other end of c receives d at its own payload point
    α[0] and runs the tree client of TreeSum.v from α+1. Each end of d
    is closed in a thread of its own.

    fa takes c and d as a pair. Mordido and Pérez pass them as two
    curried arguments and check the send at the call with the concrete
    sequence of c, 5 < 12 (p. 39). The core checks it once in the body
    of fa, against the box constraint. The curried form fac at the end
    of the file types too ([fac_deadlock_free]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.TreeSum.

Set Default Proof Using "All".

(** !(∃ι₀. Close@ι₀);XformD;s *)
Definition FaS (s : sty) : sty := SSeq (SSnd 1 (TSess SEnd (pvar 0))) (SSeq XformD s).

(** C with κ = 0, ι = 1 and ζ = 2 under the box binder. *)
Definition fa_P (g : fact) : Prop :=
  walk_P (pv 0 0) (pv 2 0) g ∨ g = FEq (pv 1 0) (pt_slot (pv 0 0) 0).
Definition fa_C : bcs := BCs [] fa_P.

Definition fa_res : ty := TEx (LPt (pv 0 1)) 1 (BCs [pv 0 1; pv 2 0] after_P) (TSess (SVar 0) (pv 0 0)).

Definition fa_body : ty :=
  TLolli (Some (pv 2 0)) None (TProd (TSess (FaS (SVar 0)) (pv 0 0)) (TSess SEnd (pv 1 0))) fa_res.

Definition fa_ty : ty := TBox 3 1 fa_C (TLolli None None TUnit fa_body).

(** treeSum is the variable 5 of the body, the variable 1 outside. *)
Definition fa : expr :=
  EBox (Lam (LetP (Var 0) (App (App EForce (Var 5)) (App ESend (Pair (Var 0) (Var 1)))))).

Lemma fa_ty_pscoped : pscoped 0 fa_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma fa_inst x y z s :
  sinst_ty (slist [s]) (ty_inst [x; y; z] fa_body) =
  TLolli (Some z) None (TProd (TSess (FaS s) x) (TSess SEnd y))
    (TEx (LPt (pt_shift 1 x)) 1 (BCs [pt_shift 1 x; z] after_P) (TSess s (pv 0 0))).
Proof.
  destruct x as [p o], y as [q r], z as [t u]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma fa_typed W Ψ F : world_wf W → typed W ∅ Ψ ∅ [None; Some tsum_ty] F fa fa_ty.
Proof.
  intros HW. unfold fa, fa_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0).
  { intros o Ho. rewrite elem_of_cons, list_elem_of_singleton in Ho.
    destruct Ho as [-> | ->]; [by left|right; by eexists]. }
  { set_solver. }
  intros ss Hss Hhc. destruct ss as [|s [|]]; try discriminate Hss.
  rewrite Forall_singleton in Hhc. fold fa_ty.
  change (lenv_pinst (pshift 3) [Some fa_ty; None; Some tsum_ty])
    with [Some (pinst_ty (pshift 3) fa_ty); None; Some (pinst_ty (pshift 3) tsum_ty)].
  rewrite (pinst_closed _ fa_ty) by apply fa_ty_pscoped.
  rewrite (pinst_closed _ tsum_ty) by apply tsum_ty_pscoped.
  change (sinst_ty (slist [s]) fa_body) with
    (TLolli (Some (pv 2 0)) None (TProd (TSess (FaS s) (pv 0 0)) (TSess SEnd (pv 1 0)))
       (TEx (LPt (pv 0 1)) 1 (BCs [pv 0 1; pv 2 0] after_P) (TSess s (pv 0 0)))).
  change (bcs_inst (pshift 3) fa_C) with fa_C.
  set (Ψ' := hyps_inst (pshift 3) Ψ ++ [(fa_C, ids 3)]).
  assert ((fa_C, ids 3) ∈ Ψ') as Hg by (apply elem_of_app; right; by left).
  assert (∀ w, slt W Ψ' (pwalk (pv 0 0) w) (pv 2 0)) as Hz.
  { intros w. eapply (sl_hyp0 _ _ fa_P _ (pwalk (pv 0 0) w) (pv 2 0));
      [exact Hg|left; exists w; by left|fscw|piw|piw]. }
  assert (∀ w i, slt W Ψ' (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))) as Hb.
  { intros w i. eapply (sl_hyp0 _ _ fa_P _ (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i)));
      [exact Hg|left; exists w; right; by exists i|fscw|piw|piw]. }
  assert (seqs W Ψ' (pv 1 0) (pt_slot (pv 0 0) 0)) as He.
  { eapply (se_hyp0 _ _ fa_P _ (pv 1 0) (pt_slot (pv 0 0) 0)); [exact Hg|by right|fsc|reflexivity|reflexivity]. }
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn.
  eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq XformD s) (pv 0 1))); [reflexivity| | |].
  - (* treeSum at κ+1 *)
    rewrite <-(tsum_inst (pv 0 1) (pv 2 0) s).
    apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pv 0 1; pv 2 0] [s]);
      [done|done| | |done| |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g (w & [-> | (i & ->)]) _; cbn [fact_map fact_holds];
        rewrite ?wstep_inst, ?pwalk_inst; [apply (Hz (None :: w))|apply (Hb (None :: w) i)].
    + constructor; [apply (skn_inst W Ψ' fa_C (ids 3) (pvar 0)); [exact Hg|cbn; set_solver|done]|].
      constructor; [apply (skn_inst W Ψ' fa_C (ids 3) (pvar 2)); [exact Hg|cbn; set_solver|done]|constructor].
    + by apply Forall_singleton.
  - (* send ⟨d, c⟩ at κ, d moved from ι to κ[0] *)
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess SEnd (pt_slot (pv 0 0) 0)) (TSess (FaS s) (pv 0 0)))).
    + tstep; [tstep|].
      apply (t_conv W _ _ _ _ _ _ (TSess SEnd (pv 1 0))); [split; [exact He|apply seq_refl]|tstep].
    + apply (KTSend _ _ _ 1 (TSess SEnd (pvar 0)) (SSeq XformD s) (pv 0 0)). cbn.
      intros h Hh. mem_cases Hh. apply (Hb [] false).
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. right. apply (Hz []).
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 2 0). split; [done|]. apply sle_refl, HW.
Qed.

(** ** The closed program fa_go

    The top level binds treeSum and then fa, which captures it. After
    the first [new] α is 0 and z is 1, and c : FaS Close@α. d and d′
    are created at α[0]. *)

Definition fa_srv_call : expr :=
  LetU (Var 0) (App (Lam (App EClos (Var 0))) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2)))).

Definition fa_cli : expr :=
  LetP (App ERecv (App ESel1 (App ESel1 (App ESend (Pair EUnit
          (App ESel2 (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 0)))))))))))
    (LetU (Var 1) (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Definition fa_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
      (LetU (App ESpawn (Lam fa_srv_call))
        (LetP (App ERecv (Var 2))
          (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 2))))) fa_cli))))).

Definition fa_go : expr :=
  LetP (Pair tsum EUnit) (LetU (Var 0) (LetP (Pair fa EUnit) (LetU (Var 0) fa_main))).

(** The walk of the other end of c: recv, then the client walk of
    TreeSum.v from α+1. *)
Definition fa_cw : list (option bool) := None :: ts_cw.
Definition fap (k : nat) : point := pwalk (pv 0 0) (take k fa_cw).

Lemma fa_go_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) fa_go TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fa_go.
  assert (hcontractive ts_Q1) as HQ1 by (apply hcontractive_seq; [apply hcontractive_rcv|apply hcontractive_end]).
  assert (hcontractive ts_Q2) as HQ2 by (apply hcontractive_seq; [apply hcontractive_rcv|exact HQ1]).
  tstep.
  { tstep; [tstep|apply typed_hyps_wk; [exact HWs|apply tsum_typed, HW]]. }
  cbn. tstep; [tstep|]. cbn.
  tstep.
  { tstep; [tstep|apply fa_typed, HW]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_open W _ _ ∅ _ _ _ _ (FaS SEnd) tca_C); [apply tca_ok|..].
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  set (Ψ := [(top_C0, [pvar 1]); (BCs [pvar 1] send_P, [pvar 0])]).
  assert (∀ w, slt W Ψ (pwalk (pv 0 0) w) (pv 1 0)) as Haz.
  { intros w. eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0] (FLt (pwalk (pv 0 0) w) (pv 1 0)));
      [inlist|exists w; by left|fscw|fmw]. }
  assert (∀ w i, slt W Ψ (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))) as Haa.
  { intros w i. eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0]
                          (FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))));
      [inlist|exists w; right; by exists i|fscw|fmw]. }
  apply (t_new_at W _ _ _ _ _ _ _ SEnd (psl 0 false 0) HWs).
  { eapply skn_inst; [by right; left|by left|done]. }
  cbn. tstep.
  { (* close d′ *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (psl 0 false 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (psl 0 false 0)) (TSess SEnd (psl 0 false 0)));
      [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. right. apply (Haz [Some false]). }
  cbn. tstep.
  { (* the caller of fa *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply (Haa [] false)]. }
    unfold fa_srv_call. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pv 0 1)) 1 (BCs [pv 0 1; pv 1 0] after_P) (TSess SEnd (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pv 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. eapply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 1)) 1 (BCs [pv 0 1; pv 1 0] after_P)
                  (TSess SEnd (pv 0 0)) _
                  (<[1:=Some (pv 2 0)]> (<[0:=Some (pv 2 0)]> ∅))
                  [(top_C0, [pvar 2]); (BCs [pvar 2] send_P, [pvar 1]); (BCs [pv 1 1; pv 2 0] after_P, [pv 0 0])]
                  _ (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. right.
      eapply (sl_hyp W _ [pv 1 1; pv 2 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
        [inlist|right; exists []; by left|fsc|reflexivity].
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None
                (TProd (TSess (FaS SEnd) (pv 0 0)) (TSess SEnd (psl 0 false 0))) RD); [reflexivity| | |].
      + rewrite <-(fa_inst (pv 0 0) (psl 0 false 0) (pv 1 0) SEnd : _ = TLolli _ _ _ RD).
        apply (typed_force W _ _ _ _ _ _ 3 1 fa_C None fa_body [pv 0 0; psl 0 false 0; pv 1 0] [SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g [(w & [-> | (i & ->)]) | ->] _; cbn [fact_map fact_holds];
            rewrite ?wstep_inst, ?pwalk_inst; [apply Haz|apply Haa|apply se_refl].
        * constructor; [eapply skn_inst; [by right; left|by left|done]|].
          constructor; [eapply skn_inst; [by right; left|by left|done]|].
          constructor; [eapply skn_inst; [by left|by left|done]|constructor].
        * apply Forall_singleton, hcontractive_end.
      + tstep; tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  (* the other end of c receives d and runs the tree client *)
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 (TSess SEnd (pvar 0))) (SSeq XformC SEnd)) (pv 0 0)));
      [tstep|apply (KTRecv _ _ _ 1 (TSess SEnd (pvar 0)) (SSeq XformC SEnd) (pv 0 0))|kscope|
       apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (psl 0 false 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (psl 0 false 0)) (TSess SEnd (psl 0 false 0)));
      [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. right. apply (Haz [Some false]). }
  unfold fa_cli. cbn. tstep.
  - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (fap 8)) (TSess ts_Q2 (fap 8)));
      [|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip ts_Q2) (fap 8))).
    { apply teq_steq. split; [done|by apply skip_l]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (fap 7))
              (TSess (SPlus (SSeq SSkip ts_Q2) (SSeq XN ts_Q2)) (fap 7)));
      [|apply KTSel1, (Haa (take 7 fa_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC ts_Q2)) (fap 7))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ2]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (fap 6))
              (TSess (SPlus (SSeq SSkip (SSeq XformC ts_Q2)) (SSeq XN (SSeq XformC ts_Q2))) (fap 6)));
      [|apply KTSel1, (Haa (take 6 fa_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC ts_Q2)) (fap 6))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (fap 5))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC ts_Q2))) (fap 5))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC ts_Q2)) (fap 5)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN ts_Q1) (fap 5))).
    { apply teq_steq. split; [done|by apply xnode_snd]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (fap 4)) (TSess (SPlus (SSeq SSkip ts_Q1) (SSeq XN ts_Q1)) (fap 4)));
      [|apply KTSel2, (Haa (take 4 fa_cw) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC ts_Q1)) (fap 4))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ1]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (fap 3))
              (TSess (SPlus (SSeq SSkip (SSeq XformC ts_Q1)) (SSeq XN (SSeq XformC ts_Q1))) (fap 3)));
      [|apply KTSel1, (Haa (take 3 fa_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC ts_Q1)) (fap 3))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (fap 2))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC ts_Q1))) (fap 2))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC ts_Q1)) (fap 2)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN SEnd) (fap 2))).
    { apply teq_steq. split; [done|apply xnode_snd, hcontractive_end]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (fap 1)) (TSess (SPlus (SSeq SSkip SEnd) (SSeq XN SEnd)) (fap 1)));
      [|apply KTSel2, (Haa (take 1 fa_cw) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply XformC_seq].
  - cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (fap 9)) (TSess ts_Q1 (fap 9)));
        [tstep|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (fap 10)) (TSess SEnd (fap 10)));
      [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
Qed.

Theorem fa_deadlock_free : deadlock_free (∅, {[+ fa_go +]}).
Proof.
  apply (soundness_source 1 top_C0 _ TUnit (c0_acyclic_creation _ _ top_acyclic));
    [constructor|apply fa_go_typed].
Qed.


(** ** The curried form

      fac : □(∀κ ι ζ a. C. ∗ ⊸ ((!(Close);XformD;a)@κ ⊸
                                (Close@ι ⊸^ζ_κ ∃κ′≽κ+1. C′. a@κ′)))
      fac c d = treeSum (send ⟨d, c⟩)

    Mordido and Pérez pass c and d one at a time. Applied to c, fac
    returns a closure that holds c, so its lower point is κ. The
    application to c never blocks and has no upper point. The second
    application has the upper point ζ, and the body is the body of fa. *)

Definition fac_body : ty :=
  TLolli None None (TSess (FaS (SVar 0)) (pv 0 0))
    (TLolli (Some (pv 2 0)) (Some (pv 0 0)) (TSess SEnd (pv 1 0)) fa_res).

Definition fac_ty : ty := TBox 3 1 fa_C (TLolli None None TUnit fac_body).

(** treeSum is the variable 4 of the body, the variable 1 outside. *)
Definition fac : expr :=
  EBox (Lam (Lam (App (App EForce (Var 4)) (App ESend (Pair (Var 0) (Var 1)))))).

Lemma fac_ty_pscoped : pscoped 0 fac_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma fac_inst x y z s :
  sinst_ty (slist [s]) (ty_inst [x; y; z] fac_body) =
  TLolli None None (TSess (FaS s) x)
    (TLolli (Some z) (Some x) (TSess SEnd y)
       (TEx (LPt (pt_shift 1 x)) 1 (BCs [pt_shift 1 x; z] after_P) (TSess s (pv 0 0)))).
Proof.
  destruct x as [p o], y as [q r], z as [t u]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma fac_typed W Ψ F : world_wf W → typed W ∅ Ψ ∅ [None; Some tsum_ty] F fac fac_ty.
Proof.
  intros HW. unfold fac, fac_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0).
  { intros o Ho. rewrite elem_of_cons, list_elem_of_singleton in Ho.
    destruct Ho as [-> | ->]; [by left|right; by eexists]. }
  { set_solver. }
  intros ss Hss Hhc. destruct ss as [|s [|]]; try discriminate Hss.
  rewrite Forall_singleton in Hhc. fold fac_ty.
  change (lenv_pinst (pshift 3) [Some fac_ty; None; Some tsum_ty])
    with [Some (pinst_ty (pshift 3) fac_ty); None; Some (pinst_ty (pshift 3) tsum_ty)].
  rewrite (pinst_closed _ fac_ty) by apply fac_ty_pscoped.
  rewrite (pinst_closed _ tsum_ty) by apply tsum_ty_pscoped.
  change (sinst_ty (slist [s]) fac_body) with
    (TLolli None None (TSess (FaS s) (pv 0 0))
       (TLolli (Some (pv 2 0)) (Some (pv 0 0)) (TSess SEnd (pv 1 0))
          (TEx (LPt (pv 0 1)) 1 (BCs [pv 0 1; pv 2 0] after_P) (TSess s (pv 0 0))))).
  change (bcs_inst (pshift 3) fa_C) with fa_C.
  set (Ψ' := hyps_inst (pshift 3) Ψ ++ [(fa_C, ids 3)]).
  assert ((fa_C, ids 3) ∈ Ψ') as Hg by (apply elem_of_app; right; by left).
  assert (∀ w, slt W Ψ' (pwalk (pv 0 0) w) (pv 2 0)) as Hz.
  { intros w. eapply (sl_hyp0 _ _ fa_P _ (pwalk (pv 0 0) w) (pv 2 0));
      [exact Hg|left; exists w; by left|fscw|piw|piw]. }
  assert (∀ w i, slt W Ψ' (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))) as Hb.
  { intros w i. eapply (sl_hyp0 _ _ fa_P _ (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i)));
      [exact Hg|left; exists w; right; by exists i|fscw|piw|piw]. }
  assert (seqs W Ψ' (pv 1 0) (pt_slot (pv 0 0) 0)) as He.
  { eapply (se_hyp0 _ _ fa_P _ (pv 1 0) (pt_slot (pv 0 0) 0)); [exact Hg|by right|fsc|reflexivity|reflexivity]. }
  eapply (tv_lam W HW _ _ _ _ _ _ _ None None 1); [set_solver|cbn; set_solver|].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pv 2 0)) (Some (pv 0 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn.
  eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq XformD s) (pv 0 1))); [reflexivity| | |].
  - rewrite <-(tsum_inst (pv 0 1) (pv 2 0) s).
    apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pv 0 1; pv 2 0] [s]);
      [done|done| | |done| |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g (w & [-> | (i & ->)]) _; cbn [fact_map fact_holds];
        rewrite ?wstep_inst, ?pwalk_inst; [apply (Hz (None :: w))|apply (Hb (None :: w) i)].
    + constructor; [apply (skn_inst W Ψ' fa_C (ids 3) (pvar 0)); [exact Hg|cbn; set_solver|done]|].
      constructor; [apply (skn_inst W Ψ' fa_C (ids 3) (pvar 2)); [exact Hg|cbn; set_solver|done]|constructor].
    + by apply Forall_singleton.
  - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess SEnd (pt_slot (pv 0 0) 0)) (TSess (FaS s) (pv 0 0)))).
    + tstep; [tstep|].
      apply (t_conv W _ _ _ _ _ _ (TSess SEnd (pv 1 0))); [split; [exact He|apply seq_refl]|tstep].
    + apply (KTSend _ _ _ 1 (TSess SEnd (pvar 0)) (SSeq XformD s) (pv 0 0)). cbn.
      intros h Hh. mem_cases Hh. apply (Hb [] false).
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. right. apply (Hz []).
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 2 0). split; [done|]. apply sle_refl, HW.
Qed.

Definition fac_srv_call : expr :=
  LetU (Var 0) (App (Lam (App EClos (Var 0))) (App (App (App EForce (Var 6)) (Var 4)) (Var 2))).

Definition fac_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
      (LetU (App ESpawn (Lam fac_srv_call))
        (LetP (App ERecv (Var 2))
          (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 2))))) fa_cli))))).

Definition fac_go : expr :=
  LetP (Pair tsum EUnit) (LetU (Var 0) (LetP (Pair fac EUnit) (LetU (Var 0) fac_main))).

Lemma fac_go_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) fac_go TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fac_go.
  assert (hcontractive ts_Q1) as HQ1 by (apply hcontractive_seq; [apply hcontractive_rcv|apply hcontractive_end]).
  assert (hcontractive ts_Q2) as HQ2 by (apply hcontractive_seq; [apply hcontractive_rcv|exact HQ1]).
  tstep.
  { tstep; [tstep|apply typed_hyps_wk; [exact HWs|apply tsum_typed, HW]]. }
  cbn. tstep; [tstep|]. cbn.
  tstep.
  { tstep; [tstep|apply fac_typed, HW]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_open W _ _ ∅ _ _ _ _ (FaS SEnd) tca_C); [apply tca_ok|..].
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  set (Ψ := [(top_C0, [pvar 1]); (BCs [pvar 1] send_P, [pvar 0])]).
  assert (∀ w, slt W Ψ (pwalk (pv 0 0) w) (pv 1 0)) as Haz.
  { intros w. eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0] (FLt (pwalk (pv 0 0) w) (pv 1 0)));
      [inlist|exists w; by left|fscw|fmw]. }
  assert (∀ w i, slt W Ψ (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))) as Haa.
  { intros w i. eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0]
                          (FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))));
      [inlist|exists w; right; by exists i|fscw|fmw]. }
  apply (t_new_at W _ _ _ _ _ _ _ SEnd (psl 0 false 0) HWs).
  { eapply skn_inst; [by right; left|by left|done]. }
  cbn. tstep.
  { (* close d′ *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (psl 0 false 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (psl 0 false 0)) (TSess SEnd (psl 0 false 0)));
      [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. right. apply (Haz [Some false]). }
  cbn. tstep.
  { (* the caller of fac, curried *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply (Haa [] false)]. }
    unfold fac_srv_call. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pv 0 1)) 1 (BCs [pv 0 1; pv 1 0] after_P) (TSess SEnd (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pv 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. eapply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 1)) 1 (BCs [pv 0 1; pv 1 0] after_P)
                  (TSess SEnd (pv 0 0)) _
                  (<[1:=Some (pv 2 0)]> (<[0:=Some (pv 2 0)]> ∅))
                  [(top_C0, [pvar 2]); (BCs [pvar 2] send_P, [pvar 1]); (BCs [pv 1 1; pv 2 0] after_P, [pv 0 0])]
                  _ (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. right.
      eapply (sl_hyp W _ [pv 1 1; pv 2 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
        [inlist|right; exists []; by left|fsc|reflexivity].
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) (Some (pv 0 0)) (TSess SEnd (psl 0 false 0)) RD);
        [reflexivity| | |].
      + eapply (tv_app W HW _ _ _ _ _ _ None None (TSess (FaS SEnd) (pv 0 0))
                  (TLolli (Some (pv 1 0)) (Some (pv 0 0)) (TSess SEnd (psl 0 false 0)) RD)); [reflexivity| | |].
        * rewrite <-(fac_inst (pv 0 0) (psl 0 false 0) (pv 1 0) SEnd : _ = TLolli _ _ _ (TLolli _ _ _ RD)).
          apply (typed_force W _ _ _ _ _ _ 3 1 fa_C None fac_body [pv 0 0; psl 0 false 0; pv 1 0] [SEnd]);
            [done|done| | |done| |apply ubs_none|tstep].
          -- apply bcs_hold_intro. intros g [(w & [-> | (i & ->)]) | ->] _; cbn [fact_map fact_holds];
               rewrite ?wstep_inst, ?pwalk_inst; [apply Haz|apply Haa|apply se_refl].
          -- constructor; [eapply skn_inst; [by right; left|by left|done]|].
             constructor; [eapply skn_inst; [by right; left|by left|done]|].
             constructor; [eapply skn_inst; [by left|by left|done]|constructor].
          -- apply Forall_singleton, hcontractive_end.
        * tstep.
        * apply ubs_none.
      + tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  (* the other end of c receives d and runs the tree client *)
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 (TSess SEnd (pvar 0))) (SSeq XformC SEnd)) (pv 0 0)));
      [tstep|apply (KTRecv _ _ _ 1 (TSess SEnd (pvar 0)) (SSeq XformC SEnd) (pv 0 0))|kscope|
       apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (psl 0 false 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (psl 0 false 0)) (TSess SEnd (psl 0 false 0)));
      [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. right. apply (Haz [Some false]). }
  unfold fa_cli. cbn. tstep.
  - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (fap 8)) (TSess ts_Q2 (fap 8)));
      [|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip ts_Q2) (fap 8))).
    { apply teq_steq. split; [done|by apply skip_l]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (fap 7))
              (TSess (SPlus (SSeq SSkip ts_Q2) (SSeq XN ts_Q2)) (fap 7)));
      [|apply KTSel1, (Haa (take 7 fa_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC ts_Q2)) (fap 7))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ2]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (fap 6))
              (TSess (SPlus (SSeq SSkip (SSeq XformC ts_Q2)) (SSeq XN (SSeq XformC ts_Q2))) (fap 6)));
      [|apply KTSel1, (Haa (take 6 fa_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC ts_Q2)) (fap 6))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (fap 5))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC ts_Q2))) (fap 5))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC ts_Q2)) (fap 5)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN ts_Q1) (fap 5))).
    { apply teq_steq. split; [done|by apply xnode_snd]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (fap 4)) (TSess (SPlus (SSeq SSkip ts_Q1) (SSeq XN ts_Q1)) (fap 4)));
      [|apply KTSel2, (Haa (take 4 fa_cw) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC ts_Q1)) (fap 4))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ1]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (fap 3))
              (TSess (SPlus (SSeq SSkip (SSeq XformC ts_Q1)) (SSeq XN (SSeq XformC ts_Q1))) (fap 3)));
      [|apply KTSel1, (Haa (take 3 fa_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC ts_Q1)) (fap 3))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (fap 2))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC ts_Q1))) (fap 2))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC ts_Q1)) (fap 2)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN SEnd) (fap 2))).
    { apply teq_steq. split; [done|apply xnode_snd, hcontractive_end]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (fap 1)) (TSess (SPlus (SSeq SSkip SEnd) (SSeq XN SEnd)) (fap 1)));
      [|apply KTSel2, (Haa (take 1 fa_cw) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply XformC_seq].
  - cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (fap 9)) (TSess ts_Q1 (fap 9)));
        [tstep|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (fap 10)) (TSess SEnd (fap 10)));
      [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
Qed.

Theorem fac_deadlock_free : deadlock_free (∅, {[+ fac_go +]}).
Proof.
  apply (soundness_source 1 top_C0 _ TUnit (c0_acyclic_creation _ _ top_acyclic));
    [constructor|apply fac_go_typed].
Qed.
