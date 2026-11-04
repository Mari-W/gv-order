(** * Kobayashi's recursive forwarder server: typable

    Example 2 of Kobayashi (kobayashi2006new p. 11):

      P = *f?r. (if b then r!true else (ν r′) (f!r′ | r′?x. r!x))

    The server listens on the replicated channel f. Each request carries
    a reply channel r. The server either answers on r at once, or it
    creates a fresh reply channel r′, calls itself on r′, waits for the
    answer on r′ and forwards it on r. Kobayashi's derivation needs
    r′ ≺ r in the creation order, and he notes that without it the
    process has no type (p. 11).

    Here:

      Sr   = !∗.Close
      C    = {ι[0]ⁿ⁺¹ ≺ ι[0]ⁿ,  ι[0]ⁿ⁺¹ + 1 ≺ ι[0]ⁿ  ∣  n ∈ ℕ}   (positions from 0)
      fwsrv : □(∀ι. C. ∗ ⊸ (Sr@ι ⊸^{ι+1} ∗))
      fwsrv = !(f = λr. case inj₂ ∗ of
                  x. let () = x in close (send ⟨∗, r⟩)
                | y. let () = y in
                     let (p, q) = new ∗ in
                     let () = spawn (λu. let () = u in (force f) p) in
                     let () = recvclose q in close (send ⟨∗, r⟩))
      fw_main = let (s, w) = ⟨fwsrv, ∗⟩ in let () = w in
                let (c, c′) = new ∗ in
                let () = spawn (λu. let () = u in (force s) c) in
                recvclose c′

    Simplifications. The calculus has no replicated channels, so the
    replicated input *f?r.Q is the box fwsrv and the output f!r′ is a
    spawned call (force f) p. It has no booleans, so b is the closed
    value inj₂ ∗ of ∗ ⊕ ∗ and every run takes the recursive branch,
    while E-Case types both branches. It has no integers, so the
    answer true and the forwarded value x are ∗ and the reply session
    is !∗.Close, one message and a close. Kobayashi's r′?x.r!x receives
    and sends again, which this program does; [link] would merge the two
    sessions in one step and is not his program.

    Points. The fresh reply channel of a call sits at ι[0], the point of the first
    channel carried by the message the call answers on, created by
    [t_new_at] at that point. The reply session carries no channel, so
    ι[0] holds no payload, as the ceiling of examples/TailCall.v does
    not. C orders every round strictly below the one that called it, and
    the recursion descends along the depth, so C[ι[0]/ι] ⊆ C ([fw_sub]).
    A creation constraint {κ + k ≺ ι} with the outer point ι would do
    the same job; the chain keeps every fact inside one root, as the
    other examples in the empty world do.

    Acyclicity. C has no rank in ℕ, because the depth grows without
    bound and the order falls along it. [dlt] reads a point
    lexicographically as its depth, reversed, and its offset, and every
    fact of C and program order rise along it ([fw_ok]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

Definition fw_P (g : fact) : Prop :=
  ∃ n, g = FLt (Pt (payloadv (S n)) 0) (Pt (payloadv n) 0) ∨
       g = FLt (Pt (payloadv (S n)) 1) (Pt (payloadv n) 0).

Definition fw_C : bcs := BCs [] fw_P.

Definition fw_body : ty :=
  TLolli (Some (pv 0 1)) None (TSess Sd (pv 0 0)) TUnit.

Definition fwsrv : expr :=
  EBox (Lam (Case (Inj2 EUnit)
    (LetU (Var 0) (sendclose (Var 1)))
    (LetU (Var 0)
      (let_new_pair
        (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 5)) (Var 2)))))
          (LetU (recvclose (Var 0)) (sendclose (Var 3)))))))).

Definition fw_main : expr :=
  LetP (Pair fwsrv EUnit) (LetU (Var 0)
    (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 4)) (Var 2)))))
        (recvclose (Var 0))))).

(** C[ι[0]/ι] ⊆ C: round n goes to round n+1. *)
Lemma fw_sub g : fw_P g → fact_scoped 1 g → fw_P (fact_map (pt_inst (plist [pcr])) g).
Proof.
  intros (n & [-> | ->]) _; exists (S n); [left|right];
    cbn [fact_map]; unfold pt_inst; cbn [pt_name pt_off]; by rewrite !payloadv_inst.
Qed.

Lemma fw_call W Ψ : (fw_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) fw_C [pcr].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact fw_sub]. Qed.

Lemma fw_ok peq plt : cc_ok peq plt fw_C.
Proof.
  apply cc_ok_dlt. intros g [n [-> | ->]] _; eexists _, _; split; [done| |done|];
    left; cbn; rewrite !sdepth_payloadv; lia.
Qed.

Lemma fwsrv_typed W F :
  strict W → typed W ∅ [] ∅ [] F fwsrv (TBox 1 0 fw_C (TLolli None None TUnit fw_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold fwsrv.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 fw_C fw_body. cbn. unfold fw_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  (* the two facts of C at n = 0 *)
  assert (∀ Ψ, (fw_C, [pvar 0]) ∈ Ψ → slt W Ψ pcr (pv 0 0)) as Hq.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (Pt (payloadv 1) 0) (Pt (payloadv 0) 0));
      [exact Hg|cmem|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ Ψ, (fw_C, [pvar 0]) ∈ Ψ → slt W Ψ (pt_shift 1 pcr) (pv 0 0)) as Hq1.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (Pt (payloadv 1) 1) (Pt (payloadv 0) 0));
      [exact Hg|cmem|cbn; lia|reflexivity|reflexivity]. }
  (* case inj₂ ∗ *)
  eapply (t_case W _ _ ∅ ∅ ∅ _ _ _ _ _ _ _ TUnit TUnit TUnit).
  { apply (comp0 W HW). }
  { apply lenv_split_nones_l. }
  { apply t_inj2. apply (tv_unit W HW); reflexivity. }
  - (* the answer at once: send r at ι, close r at ι+1 *)
    cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
    + tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)); cbn; set_solver|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW).
    + apply KTClos.
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
  - (* the fresh reply channel at ι[0], the call, the forward *)
    cbn. tstep; [tstep|]. cbn.
    apply (t_new_at W _ _ _ _ _ _ _ Sd pcr HWs).
    { right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]. }
    cbn. tstep.
    { (* spawn (force f) p *)
      tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 pcr)) (Some pcr) 2);
        [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - apply (typed_force0 W _ _ _ _ _ _ 1 fw_C None fw_body [pcr]);
          [done|done| | |apply ubs_none|tstep].
        + apply fw_call. by left.
        + constructor; [right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]
                       |constructor].
      - tstep.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_shift 1 pcr). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { (* recvclose q at ι[0] and ι[0]+1, holding r at ι *)
      unfold recvclose. tstep.
      - tstep; [tstep|apply KTRecv|kscope|].
        apply ubs_intro;
          [intros y Hy; mem_cases Hy;
           first [apply Hq; by left|apply Hq1; by left|apply (slt_po W _ pcr HW)]|].
        exists (pv 0 1). split; [done|]. right.
        eapply sl_trans; [apply Hq; by left|apply (slt_po W _ (pv 0 0) HW)].
      - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
        apply ubs_intro;
          [intros y Hy; mem_cases Hy;
           first [apply Hq1; by left|apply Hq; by left]|].
        exists (pv 0 1). split; [done|]. right.
        eapply sl_trans; [apply Hq1; by left|apply (slt_po W _ (pv 0 0) HW)]. }
    cbn. unfold sendclose. tstep.
    + tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)); cbn; set_solver|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW).
    + apply KTClos.
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma fw_typed : styped ∅ [] [] (∅, None) fw_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fw_main.
  eapply (tv_letp W HW _ _ _ _ _ _ (TBox 1 0 fw_C (TLolli None None TUnit fw_body)) TUnit);
    [reflexivity| |].
  { tstep; [tstep|apply fwsrv_typed, HWs]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_open W _ _ ∅ _ _ _ _ Sd fw_C); [apply fw_ok|constructor|].
  fresh_clean.
  set (Ψ := [(fw_C, [pvar 0])]).
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fw_C [pvar 0]) as HC.
  { apply bcs_hold_self; [by left|vb_list|]. intros g Hg Hs.
    change (plist [pvar 0]) with (plist (ids 1)).
    destruct g as [x y|x y]; destruct Hs as [Hx Hy]; simpl; by rewrite !pt_inst_ids. }
  assert (Forall (skn W Ψ) [pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pv 0 0)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 fw_C None fw_body [pvar 0]);
        [done|done|exact HC|exact HK|apply ubs_none|].
      tstep.
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. unfold recvclose. tstep.
  - tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem fw_deadlock_free_kob : deadlock_free (∅, {[+ fw_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply fw_typed].
Qed.
