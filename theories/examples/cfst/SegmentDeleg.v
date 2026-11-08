(** * Handing a channel over on the channel a segment call returns

      sd_srv = let c′ = treeSum c in
               let (d, d′) = new Close at κ′[0] in
               spawn (λu. close d′);
               close (send ⟨d, c′⟩)
      sd_cli = the client of TreeSum.v, then
               let (e, c) = recv c in spawn (λu. close e); close c

    The server gets the channel c′ at the instant κ′ after the segment
    of treeSum, creates d at the payload point κ′[0] and sends it on
    c′. The send owes κ′ ≺ κ′[0], which the existential of treeSum
    states along every walk of κ′ because a branch owes it too. The
    client receives d at its own point (α·w)[0] for the walk w of the
    tree. Each end of d goes to a thread of its own, so no thread
    orders d against c. With end points the server holds c at ᾱ, d′
    sits at (κ′[0])‾ and the send asks κ′ ≺ (κ′[0])‾, which the
    existential states at both polarities.

    The rules of Mordido and Pérez type the program with
    c′ : !⁹(Close¹²);Wait¹³ and d created after the call at 12. The
    send asks 9 < 12 (Fig. 5, p. 11). Version 2 of the translation in
    theories/mp loses sends of a channel on the channel a segment call
    returns (mordido-perez.md, §13). The core types it natively
    ([sd_typed], [sd_deadlock_free]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.TreeSum.

Set Default Proof Using "All".

Definition sdq_Q0 : sty := SSeq (SRcv 1 (TSess SEnd (pvar 0))) SEnd.
Definition sdq_QS : sty := SSeq (SSnd 1 (TSess SEnd (pvar 0))) SEnd.
Definition sdq_Q1 : sty := SSeq (SRcv 0 TUnit) sdq_Q0.
Definition sdq_Q2 : sty := SSeq (SRcv 0 TUnit) sdq_Q1.

Definition sd_after : expr :=
  let_new_pair (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
    (App EClos (App ESend (Pair (Var 1) (Var 2))))).

Definition sd_srv : expr :=
  LetU (Var 0) (App (Lam sd_after) (App (App EForce (Var 3)) (Var 1))).

Definition sd_cli : expr :=
  LetP (App ERecv (App ESel1 (App ESel1 (App ESend (Pair EUnit
          (App ESel2 (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 1)))))))))))
    (LetU (Var 1) (LetP (App ERecv (Var 0)) (LetU (Var 1)
      (LetP (App ERecv (Var 0))
        (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 2))))) (App EClos (Var 0))))))).

Definition sd_go : expr :=
  LetP (Pair tsum tsum) (let_new_pair (LetU (App ESpawn (Lam sd_srv)) sd_cli)).

Definition sdq_cw : list (option bool) := ts_cw ++ [None].
Definition sdp (k : nat) : point :=
  pt_polar (negb (wpol (take k sdq_cw))) (pwalk (pv 0 0) (take k sdq_cw)).

Lemma sd_typed : styped ∅ tca_Ψ [] (∅, None) sd_go TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold sd_go, tca_Ψ.
  assert (hcontractive sdq_Q0) as HQ0 by (apply hcontractive_seq; [apply hcontractive_rcv|apply hcontractive_end]).
  assert (hcontractive sdq_QS) as HQS by (apply hcontractive_seq; [apply hcontractive_snd|apply hcontractive_end]).
  assert (hcontractive sdq_Q1) as HQ1 by (apply hcontractive_seq; [apply hcontractive_rcv|exact HQ0]).
  assert (hcontractive sdq_Q2) as HQ2 by (apply hcontractive_seq; [apply hcontractive_rcv|exact HQ1]).
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply tsum_typed, HW|exact HWs|apply tsum_typed, HW]. }
  cbn. new_top HWs (SSeq XformC sdq_Q0) (pvar 0).
  fresh_clean.
  set (Ψ := [(top_C0, [pvar 1]); (BCs [pvar 1] send_P, [pvar 0])]).
  assert (∀ w c, slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pv 1 0)) as Haz.
  { intros w c. eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0] (FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 1 0)));
      [inlist|exists w, c, true; by left|fscp|fmwp]. }
  assert (∀ w i c c', slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i)))) as Haa.
  { intros w i c c'. eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0]
                          (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i)))));
      [inlist|exists w, c, c'; right; by exists i|fscp|fmwp]. }
  cbn. tstep.
  { (* the server *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold sd_srv. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pt_dual (pv 0 0))) 1 (BCs [pt_dual (pv 0 0); pv 1 0] after_P) (TSess sdq_QS (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pv 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pt_dual (pv 0 0))) 1 (BCs [pt_dual (pv 0 0); pv 1 0] after_P)
                  (TSess sdq_QS (pv 0 0)) _
                  (<[1:=Some (pv 2 0)]> (<[0:=Some (pv 2 0)]> ∅))
                  [(top_C0, [pvar 2]); (BCs [pvar 2] send_P, [pvar 1]); (BCs [pt_dual (pv 1 0); pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess sdq_QS (pv 0 0)); None; None; None; None; None; Some tsum_ty; Some tsum_ty]
                  (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      apply (t_new_at W _ _ _ _ _ _ _ SEnd (psl 0 false 0) HWs).
      { eapply skn_inst; [by right; right; left|by left|done]. }
      cbn.
      set (Ψ2 := [(top_C0, [pvar 2]); (BCs [pvar 2] send_P, [pvar 1]); (BCs [pt_dual (pv 1 0); pv 2 0] after_P, [pv 0 0])]).
      assert (slt W Ψ2 (pv 0 0) (pv 2 0)) as Hcz0.
      { eapply (sl_hyp W Ψ2 [pt_dual (pv 1 0); pv 2 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
          [inlist|right; exists [], true, true; by left|fsc|reflexivity]. }
      assert (slt W Ψ2 (pv 0 1) (pv 2 0)) as Hcz1.
      { eapply (sl_hyp W Ψ2 [pt_dual (pv 1 0); pv 2 0] after_P [pv 0 0] (FLt (pwalk (pv 0 0) [None]) (pv 2 0)));
          [inlist|right; exists [None], true, true; by left|fscw|fmw]. }
      assert (slt W Ψ2 (pt_dual (psl 0 false 0)) (pv 2 0)) as Hdz.
      { eapply (sl_hyp W Ψ2 [pt_dual (pv 1 0); pv 2 0] after_P [pv 0 0]
                  (FLt (pt_polar false (pwalk (pv 0 0) [Some false])) (pv 2 0)));
          [inlist|right; exists [Some false], false, true; by left|fscp|fmwp]. }
      assert (slt W Ψ2 (pv 0 0) (pt_dual (psl 0 false 0))) as Hcd.
      { eapply (sl_hyp W Ψ2 [pt_dual (pv 1 0); pv 2 0] after_P [pv 0 0]
                  (FLt (pt_polar true (pwalk (pv 0 0) [])) (pt_polar false (wstep (pwalk (pv 0 0) []) (Some false)))));
          [inlist|right; exists [], true, false; right; by exists false|fscp|fmwp]. }
      {
      tstep.
      { tstep; [|apply KTSpawn|done|apply ubs_none].
        eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 2 0)) (Some (psl 0 false 0)) 2); [set_solver| |].
        { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
        cbn. tstep; [tstep|]. cbn.
        eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pt_dual (psl 0 false 0))) (TSess SEnd (pt_dual (psl 0 false 0))));
          [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. right. exact Hdz. }
      cbn. eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 1)) (TSess SEnd (pv 0 1))); [|apply KTClos|done|].
      - tstep; [|apply (KTSend _ _ _ 1 (TSess SEnd (pvar 0)) SEnd (pv 0 0))| |].
        + tstep; tstep.
        + cbn. intros h Hh. mem_cases Hh. exact Hcd.
        + kscope.
        + apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 2 0). split; [done|]. right. exact Hcz0.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. right. exact Hcz1. }
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None (TSess (SSeq XformD sdq_QS) (pt_dual (pv 0 0))) RD);
        [reflexivity| | |].
      + unfold RD. rewrite <-(tsum_inst (pt_dual (pv 0 0)) (pv 1 0) sdq_QS).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pt_dual (pv 0 0); pv 1 0] [sdq_QS]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & c & c' & [-> | (i & ->)]) _; cbn [fact_map fact_holds];
            pnorm; [eapply Haz|eapply Haa].
        * constructor; [eapply skn_inst; [by right; left|by left|done]|].
          constructor; [eapply skn_inst; [by left|by left|done]|constructor].
        * apply Forall_singleton, HQS.
      + tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  (* the client *)
  unfold sd_cli. cbn. tstep.
  - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (sdp 7)) (TSess sdq_Q2 (sdp 7)));
      [|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sdp 7: Skip;Q2 after select₁ *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip sdq_Q2) (sdp 7))).
    { apply teq_steq. split; [done|by apply skip_l]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (sdp 6))
              (TSess (SPlus (SSeq SSkip sdq_Q2) (SSeq XN sdq_Q2)) (sdp 6)));
      [|apply KTSel1, (Haa (take 6 sdq_cw) false (negb (wpol (take 6 sdq_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sdp 6: Skip;(XformC;Q2) after select₁, the left leaf of Node 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC sdq_Q2)) (sdp 6))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ2]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (sdp 5))
              (TSess (SPlus (SSeq SSkip (SSeq XformC sdq_Q2)) (SSeq XN (SSeq XformC sdq_Q2))) (sdp 5)));
      [|apply KTSel1, (Haa (take 5 sdq_cw) false (negb (wpol (take 5 sdq_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sdp 5: XformC;(XformC;Q2) after the send of 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC sdq_Q2)) (sdp 5))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (sdp 4))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC sdq_Q2))) (sdp 4))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC sdq_Q2)) (sdp 4)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    (* sdp 4: XN;Q1 after select₂, Node 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN sdq_Q1) (sdp 4))).
    { apply teq_steq. split; [done|by apply xnode_snd]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (sdp 3)) (TSess (SPlus (SSeq SSkip sdq_Q1) (SSeq XN sdq_Q1)) (sdp 3)));
      [|apply KTSel2, (Haa (take 3 sdq_cw) true (negb (wpol (take 3 sdq_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sdp 3: Skip;(XformC;Q1) after select₁, the leaf left of 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC sdq_Q1)) (sdp 3))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ1]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (sdp 2))
              (TSess (SPlus (SSeq SSkip (SSeq XformC sdq_Q1)) (SSeq XN (SSeq XformC sdq_Q1))) (sdp 2)));
      [|apply KTSel1, (Haa (take 2 sdq_cw) false (negb (wpol (take 2 sdq_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sdp 2: XformC;(XformC;Q1) after the send of 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC sdq_Q1)) (sdp 2))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (sdp 1))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC sdq_Q1))) (sdp 1))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC sdq_Q1)) (sdp 1)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    (* sdp 1: XN;Close after select₂, Node 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN sdq_Q0) (sdp 1))).
    { apply teq_steq. split; [done|by apply xnode_snd]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 0 0)) (TSess (SPlus (SSeq SSkip sdq_Q0) (SSeq XN sdq_Q0)) (pv 0 0)));
      [|apply KTSel2, (Haa [] true true true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply XformC_seq].
  - (* the two replies and close *)
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (sdp 8)) (TSess sdq_Q1 (sdp 8)));
        [tstep|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
    cbn. tstep; [tstep|]. cbn.
    tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (sdp 9)) (TSess sdq_Q0 (sdp 9)));
        [tstep|apply (KTRecv _ _ _ 1 (TSess SEnd (pvar 0)) SEnd (sdp 9))|kscope|
         apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
    cbn. tstep.
    { tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (pt_dual (pt_payload (sdp 9) 0))) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pt_payload (sdp 9) 0)) (TSess SEnd (pt_payload (sdp 9) 0)));
        [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right.
      pose proof (Haz (take 9 sdq_cw ++ [Some false]) true) as H. rewrite pwalk_snoc in H. exact H. }
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pt_shift 1 (sdp 9))) (TSess SEnd (pt_shift 1 (sdp 9))));
      [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
Qed.


Theorem sd_deadlock_free : deadlock_free (∅, {[+ sd_go +]}).
Proof. apply (soundness_created_s tca_Ψ _ TUnit tca_created); [constructor|apply sd_typed]. Qed.
