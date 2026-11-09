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
    With end points q sits at (ι[0])‾, and C states its facts between
    all polarities of their points.
    A creation constraint {κ + k ≺ ι} with the outer point ι would do
    the same job; the chain keeps every fact inside one root, as the
    other examples do. main types under the hypothesis of its top-level
    point ι ([kfw_Ψ], sharp edges 172).

    Acyclicity. C has no rank in ℕ, because the depth grows without
    bound and the order falls along it. [dlt] reads a point
    lexicographically as its depth, reversed, and its offset, and every
    fact of C and program order rise along it ([fw_ok]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

(** With end points the facts hold between all polarities of their two
    points: the forwarder blocks on q at (ι[0])‾ while it holds r at ι,
    whose partner point is ῑ. *)
Definition fw_P (g : fact) : Prop :=
  ∃ n c c', g = FLt (pt_polar c (Pt (payloadv (S n)) 0)) (pt_polar c' (Pt (payloadv n) 0)) ∨
            g = FLt (pt_polar c (Pt (payloadv (S n)) 1)) (pt_polar c' (Pt (payloadv n) 0)).

Definition fw_C : bcs := BCs [] fw_P.

(** Under syntactic points the server takes the point ι of r as a
    parameter π, creates r′ by new (π[0]) and calls itself with π[0]
    (sharp edges 173). *)
Definition fw_body : ty :=
  TLolli None None (TPt (pv 0 0)) (TLolli (Some (pv 0 1)) None (TSess Sd (pv 0 0)) TUnit).

Definition fwsrv : expr :=
  EBox (Lam (Lam (Case (Inj2 EUnit)
    (LetU (Var 0) (sendclose (Var 1)))
    (LetU (Var 0)
      (let_new_pair_at (App (Konst (KPay 0)) (Var 2))
        (LetU (App ESpawn (Lam (LetU (Var 0)
                 (App (App (App EForce (Var 6)) (App (Konst (KPay 0)) (Var 5))) (Var 2)))))
          (LetU (recvclose (Var 0)) (sendclose (Var 3))))))))).

Definition fw_main : expr :=
  LetP (Pair fwsrv EUnit) (LetU (Var 0)
    (let_new_pair_at (EPt (pconst 0))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App (App (App EForce (Var 4)) (EPt (pconst 0))) (Var 2)))))
        (recvclose (Var 0))))).

(** C[ι[0]/ι] ⊆ C: round n goes to round n+1. *)
Lemma fw_inst_polar σ c x : pt_inst σ (pt_polar c x) = pt_polar c (pt_inst σ x).
Proof. destruct c; [done|apply pt_inst_dual]. Qed.

Lemma fw_sub g : fw_P g → fact_scoped 1 g → fw_P (fact_map (pt_inst (plist [pcr])) g).
Proof.
  intros (n & c & c' & [-> | ->]) _; exists (S n), c, c'; [left|right];
    cbn [fact_map]; rewrite !fw_inst_polar; unfold pt_inst; cbn [pt_name pt_off pt_pol pt_polar];
    by rewrite !payloadv_inst.
Qed.

Lemma fw_call W Ψ : (fw_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) fw_C [pcr].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact fw_sub]. Qed.

Lemma fw_ok peq plt : cc_ok peq plt fw_C.
Proof.
  apply cc_ok_dlt. intros g (n & c & c' & [-> | ->]) _; destruct c, c'; eexists _, _; (split; [done|]);
    left; cbn; rewrite !sdepth_payloadv; lia.
Qed.

Lemma fwsrv_typed W F :
  strict W → typed W ∅ [] ∅ [] F fwsrv (TBox 1 0 fw_C (TLolli None None TUnit fw_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold fwsrv.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 fw_C fw_body. cbn. unfold fw_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ None None 1); [set_solver|cbn; set_solver|].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 2); [set_solver|cbn; set_solver|].
  assert (∀ Ψ, (fw_C, [pvar 0]) ∈ Ψ → skn W Ψ pcr) as Hkr.
  { intros Ψ Hg. right; eexists _, _, (pvar 0); split_and!; [exact Hg|by left|done]. }
  (* the two facts of C at n = 0 *)
  assert (∀ Ψ, (fw_C, [pvar 0]) ∈ Ψ → slt W Ψ (pt_dual pcr) (pt_dual (pv 0 0))) as Hq.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (pt_dual (Pt (payloadv 1) 0)) (pt_dual (Pt (payloadv 0) 0)));
      [exact Hg|exists 0, false, false; by left|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ Ψ, (fw_C, [pvar 0]) ∈ Ψ → slt W Ψ (pt_shift 1 (pt_dual pcr)) (pt_dual (pv 0 0))) as Hq1.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (pt_dual (Pt (payloadv 1) 1)) (pt_dual (Pt (payloadv 0) 0)));
      [exact Hg|exists 0, false, false; by right|cbn; lia|reflexivity|reflexivity]. }
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
    unfold let_new_pair_at. apply (t_new_v W _ _ _ _ _ _ _ Sd pcr _ HWs); [| |].
    { intros F'. cbn. eapply (tv_appk W HW _ _ _ _ (KPay 0) _ None (TPt (pv 0 0)));
        [tstep|apply KTPay, Hkr; by left|done|apply ubs_none]. }
    { apply Hkr. by left. }
    cbn. tstep.
    { (* spawn (force f) p *)
      tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 pcr)) (Some (pt_dual pcr)) 3);
        [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - eapply (tv_app W HW _ _ _ _ _ _ None None (TPt pcr)); [reflexivity| | |apply ubs_none].
        + apply (typed_force0 W _ _ _ _ _ _ 1 fw_C None fw_body [pcr]);
            [done|done| | |apply ubs_none|tstep].
          * apply fw_call. by left.
          * constructor; [apply Hkr; by left|constructor].
        + eapply (tv_appk W HW _ _ _ _ (KPay 0) _ None (TPt (pv 0 0)));
            [tstep|apply KTPay, Hkr; by left|done|apply ubs_none].
      - tstep.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_shift 1 pcr). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { (* recvclose q at ι[0] and ι[0]+1, holding r at ι *)
      unfold recvclose. tstep.
      - tstep; [tstep|apply KTRecv|kscope|].
        apply ubs_intro;
          [intros y Hy; mem_cases Hy;
           first [apply Hq; by left|apply Hq1; by left|apply (slt_po W _ (pt_dual pcr) HW)]|].
        exists (pv 0 1). split; [done|]. right.
        eapply sl_trans; [apply Hq; by left|apply (sl_dpo W _ (pt_dual (pv 0 0)))].
      - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
        apply ubs_intro;
          [intros y Hy; mem_cases Hy;
           first [apply Hq1; by left|apply Hq; by left]|].
        exists (pv 0 1). split; [done|]. right.
        eapply sl_trans; [apply Hq1; by left|apply (sl_dpo W _ (pt_dual (pv 0 0)))]. }
    cbn. unfold sendclose. tstep.
    + tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)); cbn; set_solver|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW).
    + apply KTClos.
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
Qed.

Definition kfw_Ψ : hyps := [] ++ [(fw_C, [pconst 0])].

Lemma kfw_created : created (Wpo []) kfw_Ψ.
Proof. apply created_snoc; [constructor|apply fw_ok|constructor|fresh_const]. Qed.

Lemma fw_typed : styped ∅ kfw_Ψ [] (∅, None) fw_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fw_main, let_new_pair_at, kfw_Ψ.
  eapply (tv_letp W HW _ _ _ _ _ _ (TBox 1 0 fw_C (TLolli None None TUnit fw_body)) TUnit);
    [reflexivity| |].
  { tstep; [tstep|apply typed_hyps_nil; [exact HWs|apply fwsrv_typed, HWs]]. }
  cbn. tstep; [tstep|]. cbn.
  new_top HWs Sd (pconst 0).
  fresh_clean.
  set (Ψ := [(fw_C, [pconst 0])]).
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fw_C [pconst 0]) as HC.
  { apply hyp_in_fact. by left. }
  assert (Forall (skn W Ψ) [pconst 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pt_dual (pc 0 0))) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - eapply (tv_app W HW _ _ _ _ _ _ None None (TPt (pconst 0))); [reflexivity| | |apply ubs_none].
      + apply (typed_force0 W _ _ _ _ _ _ 1 fw_C None fw_body [pconst 0]);
          [done|done|exact HC|exact HK|apply ubs_none|].
        tstep.
      + tstep. eapply skn_inst; [by left|by left|done].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. unfold recvclose. tstep.
  - tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem fw_deadlock_free_kob : deadlock_free (∅, {[+ fw_main +]}).
Proof.
  apply (soundness_created_s kfw_Ψ _ TUnit kfw_created); [constructor|apply fw_typed].
Qed.
