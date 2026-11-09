(** * Kobayashi's and Padovani's factorial server: typable

    Kobayashi's running example (kobayashi2006new p. 2):

      *fact?(n,r). if n=0 then r!1 else new r1 in (fact!(n-1,r1) | r1?x.r!(x*n))

    Padovani's (3) is the same program with priorities
    (padovani2014deadlock p. 2):

      *fact?(x,y^h). if x=0 then y!<1> else (ν a^k)(fact!<x-1,a> | a?(z).y!<x*z>)

    The server receives a number and a reply channel. At zero it answers
    at once. Otherwise it creates a fresh reply channel, calls itself on
    it, blocks on the answer and sends its own. Padovani notes that the
    fresh channel a stands in y's position, so a monomorphic system
    wants h = k while the blocking input wants k < h, and that
    polymorphism over the replicated channel is what types the program
    (padovani2014deadlock p. 2). Kobayashi needs r1 ≺ r in the creation
    order for the same reason (kobayashi2006new p. 11).

    Here:

      Sr   = !∗.Close
      C    = {ι[0]ⁿ⁺¹ ≺ ι[0]ⁿ,  ι[0]ⁿ⁺¹ + 1 ≺ ι[0]ⁿ  ∣  n ∈ ℕ}   (positions from 0)
      fact : □(∀ι. C. ∗ ⊸ ((∗ ⊕ ∗) ⊗ Sr@ι ⊸^{ι+1} ∗))
      fact = !(f = λnr. let (n, r) = nr in case n of
                 x. let () = x in close (send ⟨∗, r⟩)
               | y. let () = y in
                    let (p, q) = new ∗ in
                    let () = spawn (λu. let () = u in (force f) ⟨inj₂ ∗, p⟩) in
                    let () = recvclose q in close (send ⟨∗, r⟩))
      fc_main = let (g, w) = ⟨fact, ∗⟩ in let () = w in
                let (c, c′) = new ∗ in
                let () = spawn (λu. let () = u in (force g) ⟨inj₂ ∗, c⟩) in
                recvclose c′

    Simplifications. The calculus has no replicated channels, so the
    replicated input *fact?(n,r).Q is the box fact and the output
    fact!(n-1,r1) is a spawned call. It has no integers, so n is a value
    of ∗ ⊕ ∗, the test n = 0 is E-Case on it, and the answers 1 and x*n
    are ∗. The recursive call passes inj₂ ∗ in place of n-1, which the
    calculus cannot compute, so the run recurses for ever while E-Case
    types both branches. The reply session is !∗.Close, one message and
    a close.

    Points. The fresh reply channel of a call sits at ι[0], the point of the first
    channel carried by the message the call answers on, and C orders every
    round strictly below the one that called it. This is the shape of
    examples/KobForwarder.v, and the two programs differ in where the
    branch comes from: there the server tests a boolean of its own, here
    it tests the value it was called with. The order falls along the
    depth, so C has no rank in ℕ and [dlt] orders it ([fc_ok]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

(** With end points the facts hold between all polarities of their two
    points: the server blocks on the fresh reply channel at (ι[0])‾ while it holds r at ι,
    whose partner point is ῑ. *)
Definition fc_P (g : fact) : Prop :=
  ∃ n c c', g = FLt (pt_polar c (Pt (payloadv (S n)) 0)) (pt_polar c' (Pt (payloadv n) 0)) ∨
            g = FLt (pt_polar c (Pt (payloadv (S n)) 1)) (pt_polar c' (Pt (payloadv n) 0)).

Definition fc_C : bcs := BCs [] fc_P.

(** Under syntactic points the server takes the point ι of r as a
    parameter π, creates the reply channel by new (π[0]) and calls
    itself with π[0] (sharp edges 173). *)
Definition fc_body : ty :=
  TLolli None None (TPt (pv 0 0)) (TLolli (Some (pv 0 1)) None
    (TProd (TSum TUnit TUnit) (TSess Sd (pv 0 0))) TUnit).

Definition fcsrv : expr :=
  EBox (Lam (Lam (LetP (Var 0) (Case (Var 1)
    (LetU (Var 0) (sendclose (Var 1)))
    (LetU (Var 0)
      (let_new_pair_at (App (Konst (KPay 0)) (Var 4))
        (LetU (App ESpawn (Lam (LetU (Var 0)
                 (App (App (App EForce (Var 8)) (App (Konst (KPay 0)) (Var 7))) (Pair (Inj2 EUnit) (Var 2))))))
          (LetU (recvclose (Var 0)) (sendclose (Var 3)))))))))).

Definition fc_main : expr :=
  LetP (Pair fcsrv EUnit) (LetU (Var 0)
    (let_new_pair_at (EPt (pconst 0))
      (LetU (App ESpawn (Lam (LetU (Var 0)
               (App (App (App EForce (Var 4)) (EPt (pconst 0))) (Pair (Inj2 EUnit) (Var 2))))))
        (recvclose (Var 0))))).

Lemma fc_inst_polar σ c x : pt_inst σ (pt_polar c x) = pt_polar c (pt_inst σ x).
Proof. destruct c; [done|apply pt_inst_dual]. Qed.

Lemma fc_sub g : fc_P g → fact_scoped 1 g → fc_P (fact_map (pt_inst (plist [pcr])) g).
Proof.
  intros (n & c & c' & [-> | ->]) _; exists (S n), c, c'; [left|right];
    cbn [fact_map]; rewrite !fc_inst_polar; unfold pt_inst; cbn [pt_name pt_off pt_pol pt_polar];
    by rewrite !payloadv_inst.
Qed.

Lemma fc_call W Ψ : (fc_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) fc_C [pcr].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact fc_sub]. Qed.

Lemma fc_ok peq plt : cc_ok peq plt fc_C.
Proof.
  apply cc_ok_dlt. intros g (n & c & c' & [-> | ->]) _; destruct c, c'; eexists _, _; (split; [done|]);
    left; cbn; rewrite !sdepth_payloadv; lia.
Qed.

Lemma fcsrv_typed W F :
  strict W → typed W ∅ [] ∅ [] F fcsrv (TBox 1 0 fc_C (TLolli None None TUnit fc_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold fcsrv.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 fc_C fc_body. cbn. unfold fc_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ None None 1); [set_solver|cbn; set_solver|].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 2); [set_solver|cbn; set_solver|].
  assert (∀ Ψ, (fc_C, [pvar 0]) ∈ Ψ → skn W Ψ pcr) as Hkr.
  { intros Ψ Hg. right; eexists _, _, (pvar 0); split_and!; [exact Hg|by left|done]. }
  assert (∀ Ψ, (fc_C, [pvar 0]) ∈ Ψ → slt W Ψ (pt_dual pcr) (pt_dual (pv 0 0))) as Hq.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (pt_dual (Pt (payloadv 1) 0)) (pt_dual (Pt (payloadv 0) 0)));
      [exact Hg|exists 0, false, false; by left|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ Ψ, (fc_C, [pvar 0]) ∈ Ψ → slt W Ψ (pt_shift 1 (pt_dual pcr)) (pt_dual (pv 0 0))) as Hq1.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (pt_dual (Pt (payloadv 1) 1)) (pt_dual (Pt (payloadv 0) 0)));
      [exact Hg|exists 0, false, false; by right|cbn; lia|reflexivity|reflexivity]. }
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ (TSum TUnit TUnit) (TSess Sd (pv 0 0)));
    [reflexivity|tstep|].
  cbn. eapply (tv_case W _ _ _ _ _ _ _ TUnit TUnit TUnit); [exact HW|reflexivity|tstep| |].
  - (* n = 0: answer at once *)
    cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
    + tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)); cbn; set_solver|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW).
    + apply KTClos.
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
  - (* n > 0: the fresh reply channel at ι[0], the call, the answer *)
    cbn. tstep; [tstep|]. cbn.
    unfold let_new_pair_at. apply (t_new_v W _ _ _ _ _ _ _ Sd pcr _ HWs); [| |].
    { intros F'. cbn. eapply (tv_appk W HW _ _ _ _ (KPay 0) _ None (TPt (pv 0 0)));
        [tstep|apply KTPay, Hkr; by left|done|apply ubs_none]. }
    { apply Hkr. by left. }
    cbn. tstep.
    { tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 pcr)) (Some (pt_dual pcr)) 3);
        [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - eapply (tv_app W HW _ _ _ _ _ _ None None (TPt pcr)); [reflexivity| | |apply ubs_none].
        + apply (typed_force0 W _ _ _ _ _ _ 1 fc_C None fc_body [pcr]);
            [done|done| | |apply ubs_none|tstep].
          * apply fc_call. by left.
          * constructor; [apply Hkr; by left|constructor].
        + eapply (tv_appk W HW _ _ _ _ (KPay 0) _ None (TPt (pv 0 0)));
            [tstep|apply KTPay, Hkr; by left|done|apply ubs_none].
      - tstep; [tstep|apply t_inj2, (tv_unit W HW); reflexivity].
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_shift 1 pcr). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { unfold recvclose. tstep.
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

Definition fc_Ψ : hyps := [] ++ [(fc_C, [pconst 0])].

Lemma fc_created : created (Wpo []) fc_Ψ.
Proof. apply created_snoc; [constructor|apply fc_ok|constructor|fresh_const]. Qed.

Lemma fc_typed : styped ∅ fc_Ψ [] (∅, None) fc_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fc_main, let_new_pair_at, fc_Ψ.
  eapply (tv_letp W HW _ _ _ _ _ _ (TBox 1 0 fc_C (TLolli None None TUnit fc_body)) TUnit);
    [reflexivity| |].
  { tstep; [tstep|apply typed_hyps_nil; [exact HWs|apply fcsrv_typed, HWs]]. }
  cbn. tstep; [tstep|]. cbn.
  new_top HWs Sd (pconst 0).
  fresh_clean.
  set (Ψ := [(fc_C, [pconst 0])]).
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) fc_C [pconst 0]) as HC.
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
      + apply (typed_force0 W _ _ _ _ _ _ 1 fc_C None fc_body [pconst 0]);
          [done|done|exact HC|exact HK|apply ubs_none|tstep].
      + tstep. eapply skn_inst; [by left|by left|done].
    - tstep; [tstep|apply t_inj2, (tv_unit W HW); reflexivity].
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. unfold recvclose. tstep.
  - tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem fc_deadlock_free : deadlock_free (∅, {[+ fc_main +]}).
Proof.
  apply (soundness_created_s fc_Ψ _ TUnit fc_created); [constructor|apply fc_typed].
Qed.
