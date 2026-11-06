(** * A channel after a segment call, ordered both ways

      si_srv = let c′ = treeSum c in
               let (d, d′) = new (?∗;Close) in
               spawn (λu. close (send ⟨∗, d′⟩));
               let c′ = send ⟨∗, c′⟩ in let (_, d) = recv d in
               close d; close c′
      si_cli = the client of TreeSum.v, then let (_, c) = recv c in close c

    The server serves the tree of TreeSum.v and gets the channel c′ at
    the instant κ′ after the segment. It then creates d and interleaves
    the two channels. It sends on c′ while it holds d, receives on d
    while it holds c′, and closes d while it holds c′. So d is ordered
    against c′ in both directions. With end points the server holds d
    at δ and the spawned partner holds d′ at δ̄. The creation constraint
    of d states κ′ ≺ δ̄, δ+1 ≺ (κ′+1)‾, δ+1 ≺ z and δ̄+1 ≺ z for the
    ceiling z of treeSum. Each fact relates δ or δ̄ to a point that is
    known when d is created. The only fact it derives between known
    points is κ′ ≺ (κ′+1)‾, which program order gives, so cc_ok holds
    locally ([sid_ok]).

    The rules of Mordido and Pérez type the program with c′ : !⁹;Wait¹³
    and d : ?¹⁰;Close¹² (T-Let, p. 25). Version 3 of the translation in
    theories/mp does not, because the rank world fixes the ranks of the
    walks of c′ by the data (mordido-perez.md, §15.3). The core types it
    natively ([si_typed], [si_deadlock_free]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.TreeSum.

Set Default Proof Using "All".

Definition si_Q0 : sty := SSeq (SRcv 0 TUnit) SEnd.
Definition si_QS : sty := SSeq (SSnd 0 TUnit) SEnd.
Definition si_Q1 : sty := SSeq (SRcv 0 TUnit) si_Q0.
Definition si_Q2 : sty := SSeq (SRcv 0 TUnit) si_Q1.

Definition si_after : expr :=
  let_new_pair (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (App ESend (Pair EUnit (Var 1)))))))
    (App (Lam (LetP (App ERecv (Var 2)) (LetU (Var 1) (LetU (App EClos (Var 0)) (App EClos (Var 2))))))
         (App ESend (Pair EUnit (Var 2))))).

Definition si_srv : expr :=
  LetU (Var 0) (App (Lam si_after) (App (App EForce (Var 3)) (Var 1))).

Definition si_cli : expr :=
  LetP (App ERecv (App ESel1 (App ESel1 (App ESend (Pair EUnit
          (App ESel2 (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 1)))))))))))
    (LetU (Var 1) (LetP (App ERecv (Var 0)) (LetU (Var 1)
      (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))))).

Definition si_go : expr :=
  LetP (Pair tsum tsum) (let_new_pair (LetU (App ESpawn (Lam si_srv)) si_cli)).

(** The client's walk, the one of TreeSum.v and one more receive. *)
Definition si_cw : list (option bool) := ts_cw ++ [None].
Definition sip (k : nat) : point :=
  pt_polar (negb (wpol (take k si_cw))) (pwalk (pv 0 0) (take k si_cw)).

(** The creation constraint of d, over δ = 0 with κ′ = 1 and z = 2
    outside. *)
Definition sid_P (g : fact) : Prop :=
  g = FLt (pv 1 0) (pt_dual (pv 0 0)) ∨ g = FLt (pv 0 1) (pt_dual (pv 1 1)) ∨ g = FLt (pv 0 1) (pv 2 0) ∨
  g = FLt (pt_dual (pv 0 1)) (pv 2 0).
Definition sid_C : bcs := BCs [pvar 0; pvar 2] sid_P.

Lemma sid_ok W Ψ : slt W Ψ (pv 0 0) (pv 2 0) → cc_ok (seqs W Ψ) (slt W Ψ) sid_C.
Proof.
  intros Hz.
  apply (cc_ok_out _ _ sid_C olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po|intros x _; apply olt_dpo| |].
  - intros a b (f & [-> | [-> | [-> | ->]]] & _ & E); injection E as -> ->; cbn; auto.
  - intros u p q v (f & [-> | [-> | [-> | ->]]] & _ & E) (f' & [-> | [-> | [-> | ->]]] & _ & E') Hu Hp Hq Hv Hpq;
      injection E as -> ->; injection E' as -> ->; cbn in Hu, Hp, Hq, Hv; try done.
    + apply glt_dpo.
    + apply (glt_up _ _ (pv 0 0) (pv 2 0)). exact Hz.
    + apply (glt_up _ _ (pv 0 0) (pv 2 0)). exact Hz.
Qed.

Lemma si_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) si_go TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold si_go.
  assert (hcontractive si_Q0) as HQ0 by (apply hcontractive_seq; [apply hcontractive_rcv|apply hcontractive_end]).
  assert (hcontractive si_QS) as HQS by (apply hcontractive_seq; [apply hcontractive_snd|apply hcontractive_end]).
  assert (hcontractive si_Q1) as HQ1 by (apply hcontractive_seq; [apply hcontractive_rcv|exact HQ0]).
  assert (hcontractive si_Q2) as HQ2 by (apply hcontractive_seq; [apply hcontractive_rcv|exact HQ1]).
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply tsum_typed, HW|exact HWs|apply tsum_typed, HW]. }
  cbn. apply (t_new_open W _ _ ∅ _ _ _ _ (SSeq XformC si_Q0) tca_C); [apply tca_ok|..].
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
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
    unfold si_srv. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pt_dual (pv 0 0))) 1 (BCs [pt_dual (pv 0 0); pv 1 0] after_P) (TSess si_QS (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pv 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pt_dual (pv 0 0))) 1 (BCs [pt_dual (pv 0 0); pv 1 0] after_P)
                  (TSess si_QS (pv 0 0)) _
                  (<[1:=Some (pv 2 0)]> (<[0:=Some (pv 2 0)]> ∅))
                  [(top_C0, [pvar 2]); (BCs [pvar 2] send_P, [pvar 1]); (BCs [pt_dual (pv 1 0); pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess si_QS (pv 0 0)); None; None; None; None; None; Some tsum_ty; Some tsum_ty]
                  (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      apply (t_new_open W _ _ ∅ _ _ _ _ si_Q0 sid_C).
      { apply sid_ok.
        eapply (sl_hyp W _ [pt_dual (pv 1 0); pv 2 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
          [inlist|right; exists [], true, true; by left|fsc|reflexivity]. }
      { constructor; [eapply skn_inst; [by right; right; left|by left|done]|].
        constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
      fresh_clean. cbn.
      set (Ψ2 := [(top_C0, [pvar 3]); (BCs [pvar 3] send_P, [pvar 2]);
                  (BCs [pt_dual (pv 2 0); pv 3 0] after_P, [pv 1 0]); (BCs [pvar 1; pvar 3] sid_P, [pvar 0])]).
      assert (slt W Ψ2 (pv 0 1) (pt_dual (pv 1 1))) as Hdc.
      { eapply (sl_hyp W Ψ2 [pvar 1; pvar 3] sid_P [pvar 0] (FLt (pv 0 1) (pt_dual (pv 1 1))));
          [inlist|by right; left|fsc|reflexivity]. }
      assert (slt W Ψ2 (pv 1 0) (pt_dual (pv 0 0))) as Hcd.
      { eapply (sl_hyp W Ψ2 [pvar 1; pvar 3] sid_P [pvar 0] (FLt (pv 1 0) (pt_dual (pv 0 0))));
          [inlist|by left|fsc|reflexivity]. }
      assert (slt W Ψ2 (pv 0 1) (pv 3 0)) as Hdz1.
      { eapply (sl_hyp W Ψ2 [pvar 1; pvar 3] sid_P [pvar 0] (FLt (pv 0 1) (pv 2 0)));
          [inlist|by right; right; left|fsc|reflexivity]. }
      assert (slt W Ψ2 (pt_dual (pv 0 1)) (pv 3 0)) as Hdbz1.
      { eapply (sl_hyp W Ψ2 [pvar 1; pvar 3] sid_P [pvar 0] (FLt (pt_dual (pv 0 1)) (pv 2 0)));
          [inlist|by right; right; right|fsc|reflexivity]. }
      assert (slt W Ψ2 (pv 0 0) (pv 3 0)) as Hdz0.
      { eapply sl_trans; [apply (slt_po W Ψ2 (pv 0 0) HW)|exact Hdz1]. }
      assert (slt W Ψ2 (pt_dual (pv 0 0)) (pv 3 0)) as Hdbz0.
      { eapply sl_trans; [apply (slt_po W Ψ2 (pt_dual (pv 0 0)) HW)|exact Hdbz1]. }
      assert (slt W Ψ2 (pv 0 0) (pt_dual (pv 1 1))) as Hdc0.
      { eapply sl_trans; [apply (slt_po W Ψ2 (pv 0 0) HW)|exact Hdc]. }
      assert (slt W Ψ2 (pv 1 1) (pv 3 0)) as Hcz1.
      { eapply (sl_hyp W Ψ2 [pt_dual (pv 2 0); pv 3 0] after_P [pv 1 0] (FLt (pwalk (pv 0 0) [None]) (pv 2 0)));
          [inlist|right; exists [None], true, true; by left|fscw|fmw]. }
      match goal with |- typed W ?Φ _ ?Θ ?Δ ?F ?e ?T => change (typed W Φ Ψ2 Θ Δ F e T) end.
      set (Φ2 := fhyps_pinst (pshift 1) (<[1:=Some (pv 2 0)]> (<[0:=Some (pv 2 0)]> ∅))).
      assert (Φ2 !! 1 = Some (Some (pv 3 0))) as HΦ1
        by (unfold Φ2, fhyps_pinst; by rewrite lookup_fmap, lookup_insert_eq).
      assert (2 ∉ dom Φ2) as HΦ2.
      { unfold Φ2, fhyps_pinst. rewrite dom_fmap_L. set_solver. }
      tstep.
      { (* the partner of d *)
        tstep; [|apply KTSpawn|done|apply ubs_none].
        eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 3 0)) (Some (pv 0 0)) 2); [exact HΦ2| |].
        { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
        cbn. tstep; [tstep|]. cbn.
        eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pt_dual (pv 0 1))) (TSess SEnd (pt_dual (pv 0 1)))); [|apply KTClos|done|].
        - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pt_dual (pv 0 0)))
                    (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) (pt_dual (pv 0 0)))));
            [|apply (KTSend _ _ _ 0 TUnit SEnd (pt_dual (pv 0 0))); cbn; set_solver|kscope|].
          + tstep; [tstep|tstep].
          + apply ubs_intro; [intros y Hy; mem_cases Hy|].
            exists (pv 3 0). split; [by rewrite lookup_insert_eq|]. right. exact Hdbz0.
        - apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 3 0). split; [by rewrite lookup_insert_eq|]. right. exact Hdbz1. }
      assert (slt W Ψ2 (pv 1 0) (pv 3 0)) as Hcz0.
      { eapply (sl_hyp W Ψ2 [pt_dual (pv 2 0); pv 3 0] after_P [pv 1 0] (FLt (pv 0 0) (pv 2 0)));
          [inlist|right; exists [], true, true; by left|fsc|reflexivity]. }
      cbn. {
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 3 0)) (Some (pt_dual (pv 0 0))) (TSess SEnd (pv 1 1)) TUnit);
        [reflexivity| | |].
      - assert (2 ∉ dom Φ2) as HΦ2' by exact HΦ2.
        eapply (tv_lam W HW _ _ _ _ _ (TSess SEnd (pv 1 1)) TUnit (Some (pv 3 0)) (Some (pt_dual (pv 0 0))) 2);
          [exact HΦ2'| |].
        { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
        cbn. tstep.
        + eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess si_Q0 (pv 0 0)));
            [tstep|apply KTRecv|kscope|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hdc0|].
          exists (pv 3 0). split; [by rewrite lookup_insert_eq|]. right. exact Hdz0.
        + cbn. tstep; [tstep|]. cbn. tstep.
          * eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 1)) (TSess SEnd (pv 0 1)));
              [tstep|apply KTClos|done|].
            apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hdc|].
            exists (pv 3 0). split; [by rewrite lookup_insert_eq|]. right. exact Hdz1.
          * eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 1)) (TSess SEnd (pv 1 1)));
              [tstep|apply KTClos|done|].
            apply ubs_intro; [intros y Hy; mem_cases Hy|].
            exists (pv 3 0). split; [by rewrite lookup_insert_eq|]. right. exact Hcz1.
      - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0)) (TProd TUnit (TSess si_QS (pv 1 0))));
          [|apply (KTSend _ _ _ 0 TUnit SEnd (pv 1 0)); cbn; set_solver|kscope|].
        + tstep; [tstep|tstep].
        + apply ubs_intro; [intros y Hy; mem_cases Hy; first [exact Hcd|set_solver]|].
          exists (pv 3 0). split; [exact HΦ1|]. right. exact Hcz0.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; set_solver|]. cbn.
        exists (pv 3 0). split; [exact HΦ1|]. apply sle_refl, HW. }
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None (TSess (SSeq XformD si_QS) (pt_dual (pv 0 0))) RD);
        [reflexivity| | |].
      + unfold RD. rewrite <-(tsum_inst (pt_dual (pv 0 0)) (pv 1 0) si_QS).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pt_dual (pv 0 0); pv 1 0] [si_QS]);
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
  unfold si_cli. cbn. tstep.
  - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (sip 7)) (TSess si_Q2 (sip 7)));
      [|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sip 7: Skip;Q2 after select₁ *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip si_Q2) (sip 7))).
    { apply teq_steq. split; [done|by apply skip_l]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (sip 6))
              (TSess (SPlus (SSeq SSkip si_Q2) (SSeq XN si_Q2)) (sip 6)));
      [|apply KTSel1, (Haa (take 6 si_cw) false (negb (wpol (take 6 si_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sip 6: Skip;(XformC;Q2) after select₁, the left leaf of Node 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC si_Q2)) (sip 6))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ2]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (sip 5))
              (TSess (SPlus (SSeq SSkip (SSeq XformC si_Q2)) (SSeq XN (SSeq XformC si_Q2))) (sip 5)));
      [|apply KTSel1, (Haa (take 5 si_cw) false (negb (wpol (take 5 si_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sip 5: XformC;(XformC;Q2) after the send of 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC si_Q2)) (sip 5))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (sip 4))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC si_Q2))) (sip 4))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC si_Q2)) (sip 4)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    (* sip 4: XN;Q1 after select₂, Node 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN si_Q1) (sip 4))).
    { apply teq_steq. split; [done|by apply xnode_snd]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (sip 3)) (TSess (SPlus (SSeq SSkip si_Q1) (SSeq XN si_Q1)) (sip 3)));
      [|apply KTSel2, (Haa (take 3 si_cw) true (negb (wpol (take 3 si_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sip 3: Skip;(XformC;Q1) after select₁, the leaf left of 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC si_Q1)) (sip 3))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ1]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (sip 2))
              (TSess (SPlus (SSeq SSkip (SSeq XformC si_Q1)) (SSeq XN (SSeq XformC si_Q1))) (sip 2)));
      [|apply KTSel1, (Haa (take 2 si_cw) false (negb (wpol (take 2 si_cw))) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* sip 2: XformC;(XformC;Q1) after the send of 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC si_Q1)) (sip 2))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (sip 1))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC si_Q1))) (sip 1))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC si_Q1)) (sip 1)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    (* sip 1: XN;Close after select₂, Node 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN si_Q0) (sip 1))).
    { apply teq_steq. split; [done|by apply xnode_snd]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 0 0)) (TSess (SPlus (SSeq SSkip si_Q0) (SSeq XN si_Q0)) (pv 0 0)));
      [|apply KTSel2, (Haa [] true true true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply XformC_seq].
  - (* the two replies and close *)
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (sip 8)) (TSess si_Q1 (sip 8)));
        [tstep|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
    cbn. tstep; [tstep|]. cbn.
    tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (sip 9)) (TSess si_Q0 (sip 9)));
        [tstep|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (sip 10)) (TSess SEnd (sip 10)));
      [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
Qed.


Theorem si_deadlock_free : deadlock_free (∅, {[+ si_go +]}).
Proof. apply (soundness_source 1 top_C0 _ TUnit (c0_acyclic_creation _ _ top_acyclic)); [constructor|apply si_typed]. Qed.
