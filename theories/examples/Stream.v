(** * Padovani's stream: typable

    Example (4) of Padovani (padovani2014deadlock p. 2):

      *stream?(x,y^h).(ν a^k)(y!<x,a> | stream!<x+1,a>)

    The producer receives a value and an output channel y, creates a
    fresh channel a, sends the pair (x, a) on y, and calls itself with
    a in y's position. Padovani notes that a stands where y stood, so a
    monomorphic system wants h = k while the carried output wants h < k,
    and that polymorphism over the replicated channel stream is what
    types the program (padovani2014deadlock p. 2).

    Here:

      Sst   = µα. ?⟨κ⟩(∗ ⊗ α@κ).Close
      C     = {ι[0]ⁿ + 1 ≺ ι[0]ⁿ⁺¹  ∣  n ∈ ℕ}                  (positions from 0)
      stprod : □(∀ι. C. ∗ ⊸ (S̄st@ι ⊸^{ι+1} ∗))
      stprod = !(g = λc. let (e, e′) = new ∗ in
                        let (c, u) = ⟨send ⟨⟨∗, e⟩, c⟩, ∗⟩ in let () = u in
                        let () = close c in
                        spawn (λw. let () = w in (force g) e′))
      stcons : □(∀ι. C. ∗ ⊸ (Sst@ι ⊸^{ι+1} ∗))
      stcons = !(h = λc. let (p, c) = recv c in let (v, d) = p in let () = v in
                        let () = close c in
                        spawn (λw. let () = w in (force h) d))
      st_main = let (q, r) = ⟨stcons, stprod⟩ in let (c, c′) = new ∗ in
                let () = spawn (λu. let () = u in (force r) c′) in (force q) c

    Simplifications. The calculus has no replicated channels, so the
    replicated input *stream?(x,y).Q is the box stprod and the output
    stream!<x+1,a> is a spawned call. It has no integers, so x is ∗ and
    the successor x+1 is ∗ again, which is why the payload is ∗ ⊗ α@κ
    and not a number and a channel. Padovani's outputs do not block, so
    his (4) runs with no consumer; ours is synchronous, so stcons reads
    the stream and closes each round. One round of the session is one
    message and a close, which is where Padovani's a takes over from y.

    Points. The fresh continuation of a round sits at ι[0], the point of the first
    channel carried by the message it travels on, so sender and receiver
    name it alike. send asks ι ≺ ι[0], and the close of the round at
    ι+1 runs while the next round's channel is held, which asks
    ι+1 ≺ ι[0]. C states that for every depth, and the recursive call
    forces at ι[0], where C[ι[0]/ι] ⊆ C ([st_sub]). The order rises along
    the depth, and [ult] of LitTools.v orders it ([st_ok]). With end
    points the producer keeps e′ at (ι[0])‾ and recurses there, and C
    holds its facts at all polarities, so C[(ι[0])‾/ι] ⊆ C as well.

    examples/ReceivedChain.v is the same shape with a bare channel as
    the payload, and the file is ours. This one is Padovani's program,
    with his pair. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

Definition Sst : sty := SMu (SSeq (SRcv 1 (TProd TUnit (TSess (SVar 0) (pvar 0)))) SEnd).

(** With end points the facts hold between all polarities of their two
    points. The producer keeps e′ at (ι[0])‾ and calls itself there, the
    consumer calls itself at ι[0], and the gates compare with partner
    points. *)
Definition st_P (g : fact) : Prop :=
  ∃ n c c', g = FLt (pt_polar c (Pt (payloadv n) 1)) (pt_polar c' (Pt (payloadv (S n)) 0)).

Definition st_C : bcs := BCs [] st_P.

Definition stc_body : ty := TLolli (Some (pv 0 1)) None (TSess Sst (pv 0 0)) TUnit.
Definition stp_body : ty := TLolli (Some (pv 0 1)) None (TSess (dual Sst) (pv 0 0)) TUnit.

Definition stcons : expr :=
  EBox (Lam (LetP (App ERecv (Var 0))
    (LetP (Var 1) (LetU (Var 1)
      (LetU (App EClos (Var 2))
        (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Var 1)))))))))).

Definition stprod : expr :=
  EBox (Lam (let_new_pair
    (LetP (Pair (App ESend (Pair (Pair EUnit (Var 1)) (Var 2))) EUnit) (LetU (Var 0)
      (LetU (App EClos (Var 1))
        (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Var 3)))))))))).

Definition st_main : expr :=
  LetP (Pair stcons stprod) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 3)) (Var 1)))))
      (App (App EForce (Var 3)) (Var 1)))).

Lemma st_inst_polar σ c x : pt_inst σ (pt_polar c x) = pt_polar c (pt_inst σ x).
Proof. destruct c; [done|apply pt_inst_dual]. Qed.

Lemma st_polar_polar c d y : pt_polar c (pt_polar d y) = pt_polar (eqb c d) y.
Proof. destruct c, d; simpl; try done. apply pt_dual_dual. Qed.

Lemma payloadv_inst_polar d n : pn_inst (plist [pt_polar d pcr]) (payloadv (S n)) = Pt (payloadv (S (S n))) 0.
Proof.
  induction n as [|n IH]; [by destruct d|].
  change (payloadv (S (S n))) with (NPayload (payloadv (S n)) 0 0). cbn [pn_inst]. by rewrite IH.
Qed.

Lemma st_inst_pv d n k :
  pt_inst (plist [pt_polar d pcr]) (Pt (payloadv n) k) =
  pt_polar (match n with 0 => d | _ => true end) (Pt (payloadv (S n)) k).
Proof.
  destruct n as [|n]; [by destruct d|].
  unfold pt_inst. cbn [pt_name pt_off pt_pol pt_polar]. by rewrite payloadv_inst_polar.
Qed.

Lemma st_inst_root d n k :
  pt_inst (plist [pt_polar d (pvar 0)]) (Pt (payloadv n) k) =
  pt_polar (match n with 0 => d | _ => true end) (Pt (payloadv n) k).
Proof.
  destruct n as [|n]; [by destruct d|].
  assert (∀ m, pn_inst (plist [pt_polar d (pvar 0)]) (payloadv (S m)) = Pt (payloadv (S m)) 0) as H.
  { induction m as [|m IH]; [by destruct d|].
    change (payloadv (S (S m))) with (NPayload (payloadv (S m)) 0 0). cbn [pn_inst]. by rewrite IH. }
  unfold pt_inst. cbn [pt_name pt_off pt_pol pt_polar]. by rewrite H.
Qed.

(** C[ι[0]/ι] ⊆ C and C[(ι[0])‾/ι] ⊆ C. *)
Lemma st_sub d g : st_P g → fact_scoped 1 g → st_P (fact_map (pt_inst (plist [pt_polar d pcr])) g).
Proof.
  intros (n & c & c' & ->) _. cbn [fact_map]. rewrite !st_inst_polar, !st_inst_pv, !st_polar_polar.
  by eexists (S n), _, _.
Qed.

Lemma st_call W Ψ d : (st_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) st_C [pt_polar d pcr].
Proof. intros Hg. apply bcs_hold_self; [done|destruct d; vb_list|exact (st_sub d)]. Qed.

(** C at ῑ follows from C at ι. *)
Lemma st_root W Ψ d : (st_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) st_C [pt_polar d (pvar 0)].
Proof.
  intros Hg. apply bcs_hold_self; [done|destruct d; vb_list|].
  intros g (n & c & c' & ->) _. cbn [fact_map]. rewrite !st_inst_polar, !st_inst_root, !st_polar_polar.
  by eexists n, _, _.
Qed.

Lemma st_ok peq plt : cc_ok peq plt st_C.
Proof.
  apply cc_ok_ult. intros g (n & c & c' & ->) _. destruct c, c'; eexists _, _; (split; [done|]);
  left; cbn; rewrite !sdepth_payloadv; lia.
Qed.

Lemma skn_st W Ψ x : (st_C, [pvar 0]) ∈ Ψ → pt_root x = NVar 0 → Forall (skn W Ψ) [x].
Proof.
  intros Hg Hx. apply Forall_singleton.
  apply (skn_in W Ψ st_C [pvar 0] (pvar 0)); [done|by left|done].
Qed.

Lemma stcons_typed W F :
  world_wf W → typed W ∅ [] ∅ [] F stcons (TBox 1 0 st_C (TLolli None None TUnit stc_body)).
Proof.
  intros HW. unfold stcons.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 st_C stc_body. cbn. unfold stc_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 (TProd TUnit (TSess Sst (pvar 0)))) SEnd) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW). }
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ TUnit (TSess Sst pcr)); [reflexivity|tstep|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy;
      eapply (sl_hyp0 _ _ _ _ (pv 0 1) (pt_dual (Pt (payloadv 1) 0)));
        [by left|by exists 0, true, false|cbn; lia|reflexivity|reflexivity]|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 pcr)) (Some (pt_dual pcr)) 2);
    [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 st_C None stc_body [pcr]);
      [done|done| | |apply ubs_none|tstep].
    + apply (st_call _ _ true). by left.
    + apply (skn_st W _ pcr); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_shift 1 pcr). split; [done|]. apply sle_refl, HW.
Qed.

Lemma stprod_typed W F :
  strict W → typed W ∅ [] ∅ [] F stprod (TBox 1 0 st_C (TLolli None None TUnit stp_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold stprod.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 st_C stp_body. cbn. unfold stp_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  assert (∀ Ψ c, (st_C, [pvar 0]) ∈ Ψ → slt W Ψ (pv 0 1) (pt_polar c pcr)) as Hlt1.
  { intros Ψ c Hg. eapply (sl_hyp0 _ _ _ _ (pv 0 1) (pt_polar c (Pt (payloadv 1) 0)));
      [exact Hg|by exists 0, true, c|destruct c; cbn; lia|reflexivity|by destruct c]. }
  assert (∀ Ψ c, (st_C, [pvar 0]) ∈ Ψ → slt W Ψ (pv 0 0) (pt_polar c pcr)) as Hlt.
  { intros Ψ c Hg. apply (sl_trans _ _ _ (pv 0 1)); [apply (slt_po W _ (pv 0 0) HW)|by apply Hlt1]. }
  cbn. apply (t_new_at W _ _ _ _ _ _ _ Sst pcr HWs).
  { right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]. }
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TProd TUnit (TSess Sst pcr))
                 (TSess (SSeq (SSnd 1 (TProd TUnit (TSess Sst (pvar 0)))) SEnd) (pv 0 0)))).
    - tstep; [|tstep; [tstep|apply (tv_unit W HW); reflexivity]].
      eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 1 (TProd TUnit (TSess Sst (pvar 0))) SEnd (pv 0 0)).
      intros h Hh. cbn in Hh. assert (h = pt_dual pcr) as -> by set_solver. apply (Hlt _ false). by left.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; first [apply (Hlt _ true); by left|apply (Hlt _ false); by left]|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [apply (Hlt1 _ true); by left|apply (Hlt1 _ false); by left]|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 (pt_dual pcr))) (Some pcr) 2);
    [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 st_C None stp_body [pt_dual pcr]);
      [done|done| | |apply ubs_none|tstep].
    + apply (st_call _ _ false). by left.
    + apply (skn_st W _ (pt_dual pcr)); [by left|done].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_shift 1 (pt_dual pcr)). split; [done|]. apply sle_refl, HW.
Qed.

Definition st_Ψ : hyps := hyps_inst (pshift 1) [] ++ [(bcs_inst (pshift 1) st_C, ids 1)].

Lemma st_created : created (Wpo []) st_Ψ.
Proof. apply created_snoc; [constructor|apply st_ok|constructor]. Qed.

Lemma st_typed : styped ∅ st_Ψ [] (∅, None) st_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold st_main, st_Ψ.
  tstep.
  { tstep; (apply typed_hyps_nil; [exact HWs|]); [apply stprod_typed, HWs|apply stcons_typed, HW]. }
  cbn. new_top HWs Sst (pvar 0).
  fresh_clean.
  set (Ψ := [(st_C, [pvar 0])]).
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) st_C [pvar 0]) as HC.
  { apply bcs_hold_self; [by left|vb_list|]. intros g Hg Hs.
    change (plist [pvar 0]) with (plist (ids 1)).
    destruct g as [x y]; destruct Hs as [Hx Hy]; simpl; by rewrite !pt_inst_ids. }
  assert (Forall (skn W Ψ) [pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  assert (Forall (skn W Ψ) [pt_dual (pvar 0)]) as HK'.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 0 1))) (Some (pv 0 0)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 st_C None stp_body [pt_dual (pvar 0)]);
        [done|done|apply (st_root W Ψ false); by left|exact HK'|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual (pv 0 1)). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 st_C None stc_body [pvar 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem st_deadlock_free : deadlock_free (∅, {[+ st_main +]}).
Proof.
  apply (soundness_created_s st_Ψ _ TUnit st_created); [constructor|apply st_typed].
Qed.
