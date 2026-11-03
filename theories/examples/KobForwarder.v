(** * Kobayashi's recursive forwarder server: typable

    Example 2 of Kobayashi (kobayashi2006new p. 11) reads

      P = *f?r. (if b then r!true else (ν r′) (f!r′ | r′?x. r!x))

    The server listens on the replicated channel f. Each request carries
    a reply channel r. The server either answers on r at once, or it
    creates a fresh reply channel r′, calls itself on r′, waits for the
    answer on r′ and forwards it on r. Kobayashi's derivation needs
    r′ ≺ r in the creation order, and he notes that without it the
    process has no type (p. 11).

    Written here as

      Sd    = !∗.Close
      C     = {ι.0ⁿ⁺¹ ≺ ι.0ⁿ,  ι.0ⁿ⁺¹ + 1 ≺ ι.0ⁿ  ∣  n ∈ ℕ}

      fwsrv : □(∀ι. C. ∗ ⊸^⊥_⊤ (Sd@ι ⊸^{ι+1}_⊤ ∗))
      fwsrv = ! f ∀ι { C }. λ^{ι+1}_⊤ r : Sd@ι.
                  case inj₂ ∗ of
                    x. x; close (send ⟨∗, r⟩)
                  | y. y;
                       let (p : Sd@ι.0, q : S̄d@ι.0) = new κ { κ ≡ ι.0 } ∗ in
                       spawn (λ^{ι.0+1}_{ι.0} ∗. (force f [ι.0]) p);
                       recvclose q;
                       close (send ⟨∗, r⟩)

      kfw_main = let (c : Sd@ι, c′ : S̄d@ι) = new ι { C } ∗ in
                 spawn (λ^{ι+1}_{ι} ∗. (force fwsrv [ι]) c);
                 recvclose c′

      recvclose r = let (v : ∗, r′ : Close@(x+1)) = recv r in v; close r′
                                                            r at x

    Simplifications. The calculus has no replicated channels, so the
    replicated input *f?r.Q is the box fwsrv and the output f!r′ is a
    spawned call (force f [ι.0]) p. It has no booleans, so b is the closed
    value inj₂ ∗ of ∗ ⊕ ∗ and every run takes the recursive branch,
    while E-Case types both branches. It has no integers, so the
    answer true and the forwarded value x are ∗ and the reply session
    is !∗.Close, one message and a close. Kobayashi's r′?x.r!x receives
    and sends again, which this program does. [link] would merge the two
    sessions in one step and is not his program.

    Points. The fresh reply channel of a call sits at ι.0, the first
    carried root of the channel the call answers on, and
    new κ { κ ≡ ι.0 } creates it there. The reply session carries no
    channel, so ι.0 holds no payload, as the ceiling of
    examples/TailCall.v does not. C orders every round strictly below
    the one that called it, and the recursion descends along the depth,
    so C[ι.0/ι] ⊆ C ([kfw_sub]). A creation constraint {κ + k ≺ ι} with
    the outer point ι would do the same job. The chain keeps every fact
    inside one root, as the other examples do.

    Acyclicity. The depth grows without bound and the order falls
    along it, so the rank −2·depth + offset lands in ℤ, not ℕ. Every
    fact of C and program order rise along it ([kfw_ok]).

      ∅; · ⊢^∅ kfw_main : ∗   so   thread kfw_main is deadlock free *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

Definition kfw_P (g : fact) : Prop :=
  ∃ n, g = FLt (Pt (slotv (S n)) 0) (Pt (slotv n) 0) ∨
       g = FLt (Pt (slotv (S n)) 1) (Pt (slotv n) 0).

Definition kfw_C : bcs := BCs [] kfw_P.

Definition kfw_body : ty :=
  TLolli (Some (pv 0 1)) None (TSess Sd (pv 0 0)) TUnit.

Definition fwsrv : expr :=
  EBox (Lam (Case (Inj2 EUnit)
    (LetU (Var 0) (sendclose (Var 1)))
    (LetU (Var 0)
      (let_new_pair
        (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 5)) (Var 2)))))
          (LetU (recvclose (Var 0)) (sendclose (Var 3)))))))).

Definition kfw_main : expr :=
  LetP (Pair fwsrv EUnit) (LetU (Var 0)
    (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 4)) (Var 2)))))
        (recvclose (Var 0))))).

(** C[ι.0/ι] ⊆ C. Round n goes to round n+1. *)
Lemma kfw_sub g : kfw_P g → fact_scoped 1 g → kfw_P (fact_map (pt_inst (plist [pcr])) g).
Proof.
  intros (n & [-> | ->]) _; exists (S n); [left|right];
    cbn [fact_map]; unfold pt_inst; cbn [pt_name pt_off]; by rewrite !slotv_inst.
Qed.

Lemma kfw_call W Ψ : (kfw_C, ids 1) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) kfw_C [pcr].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact kfw_sub]. Qed.

(** As in examples/FactServer.v, the rank −2·depth + offset in ℤ. *)
Definition kfw_rank (x : point) : Z :=
  (-2 * Z.of_nat (sdepth (pt_name x)) + Z.of_nat (pt_off x))%Z.

Lemma kfw_ok peq plt : cc_ok peq plt kfw_C.
Proof.
  apply (cc_ok_inner peq plt kfw_P (λ x y, (kfw_rank x < kfw_rank y)%Z)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n o] _. unfold kfw_rank, pt_shift. cbn [pt_name pt_off]. lia.
  - intros g [n [-> | ->]] _; eexists _, _; (split; [done|]);
      unfold kfw_rank; cbn [pt_name pt_off]; rewrite !sdepth_slotv; lia.
Qed.

Lemma fwsrv_typed W F :
  strict W → typed W ∅ [] ∅ [] F fwsrv (TBox 1 kfw_C (TLolli None None TUnit kfw_body)).
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold fwsrv.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open1 kfw_C kfw_body. cbn. unfold kfw_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  (* the two facts of C at n = 0 *)
  assert (∀ Ψ, (kfw_C, [pvar 0]) ∈ Ψ → slt W Ψ pcr (pv 0 0)) as Hq.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (Pt (slotv 1) 0) (Pt (slotv 0) 0));
      [exact Hg|cmem|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ Ψ, (kfw_C, [pvar 0]) ∈ Ψ → slt W Ψ (pt_shift 1 pcr) (pv 0 0)) as Hq1.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (Pt (slotv 1) 1) (Pt (slotv 0) 0));
      [exact Hg|cmem|cbn; lia|reflexivity|reflexivity]. }
  (* case inj₂ ∗ *)
  eapply (t_case W _ _ ∅ ∅ ∅ _ _ _ _ _ _ _ TUnit TUnit TUnit).
  { apply (comp0 W HW). }
  { apply lenv_split_nones_l. }
  { apply t_inj2. apply (tv_unit W HW); reflexivity. }
  - (* the answer at once, send r at ι and close r at ι+1 *)
    cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
    + tstep; [tstep; tstep|apply (KTSend _ _ _ TUnit SEnd (pv 0 0)); cbn; set_solver|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW).
    + apply KTClos.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
  - (* the fresh reply channel at ι.0, the call, the forward *)
    cbn. tstep; [tstep|]. cbn.
    apply (t_new_at W _ _ _ _ _ _ _ Sd pcr HWs).
    { right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]. }
    cbn. tstep.
    { (* spawn (force f [ι.0]) p *)
      tstep; [|apply KTSpawn|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 pcr)) (Some pcr) 2);
        [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - apply (typed_force W _ _ _ _ _ _ 1 kfw_C None kfw_body [pcr]);
          [done|done| | |apply ubs_none|tstep].
        + apply kfw_call. by left.
        + constructor; [right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]
                       |constructor].
      - tstep.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_shift 1 pcr). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { (* recvclose q at ι.0 and ι.0+1, holding r at ι *)
      unfold recvclose. tstep.
      - tstep; [tstep|apply KTRecv|].
        apply ubs_intro;
          [intros y Hy; mem_cases Hy;
           first [apply Hq; by left|apply Hq1; by left|apply (slt_po W _ pcr HW)]|].
        exists (pv 0 1). split; [done|]. right.
        eapply sl_trans; [apply Hq; by left|apply (slt_po W _ (pv 0 0) HW)].
      - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|].
        apply ubs_intro;
          [intros y Hy; mem_cases Hy;
           first [apply Hq1; by left|apply Hq; by left]|].
        exists (pv 0 1). split; [done|]. right.
        eapply sl_trans; [apply Hq1; by left|apply (slt_po W _ (pv 0 0) HW)]. }
    cbn. unfold sendclose. tstep.
    + tstep; [tstep; tstep|apply (KTSend _ _ _ TUnit SEnd (pv 0 0)); cbn; set_solver|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW).
    + apply KTClos.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma kfw_typed : styped ∅ [] [] (∅, None) kfw_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold kfw_main.
  eapply (tv_letp W HW _ _ _ _ _ _ (TBox 1 kfw_C (TLolli None None TUnit kfw_body)) TUnit);
    [reflexivity| |].
  { tstep; [tstep|apply fwsrv_typed, HWs]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_open W _ _ ∅ _ _ _ _ Sd kfw_C); [apply kfw_ok|constructor|].
  fresh_clean.
  set (Ψ := [(kfw_C, [pvar 0])]).
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) kfw_C [pvar 0]) as HC.
  { apply bcs_hold_self; [by left|vb_list|]. intros g Hg Hs.
    change (plist [pvar 0]) with (plist (ids 1)).
    destruct g as [x y|x y]; destruct Hs as [Hx Hy]; simpl; by rewrite !pt_inst_ids. }
  assert (Forall (skn W Ψ) [pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pv 0 0)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 1 kfw_C None kfw_body [pvar 0]);
        [done|done|exact HC|exact HK|apply ubs_none|].
      tstep.
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. unfold recvclose. tstep.
  - tstep; [tstep|apply KTRecv|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem kfw_deadlock_free : deadlock_free (∅, {[+ kfw_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply kfw_typed].
Qed.
