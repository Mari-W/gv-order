(** * A derivation that uses the congruences of ≡: typable

    The fact theory closes ≡ under successor and under x ↦ x[i]
    ([se_shift], [se_payload], static-system.md §3). No example before this
    one derives a fact by either rule. examples/Scheduler.v needs
    c+1 ≡ a+1 from its alias c ≡ a, and it derives that inside the world
    through the closure field [wf_eq_shift] and lifts it with [se_w], so
    the static rule stays unused. examples/Forwarder.v states its alias
    of payload points fact by fact in a constraint instead of deriving
    it.

    The box below is the smallest program we found whose derivation uses
    both rules. It takes two point variables ι and ι′ aliased by its
    constraint, holds a channel c at ι that sends one channel, a channel
    e at ι′[0], and a channel d at ι′+2.

      Scg = !⟨κ⟩(Close@κ).Close
      C   = {ι ≡ ι′,  ι′ ≺ ι′[0]}                             (positions from 0)
      cg : □(∀ι ι′. C. ∗ ⊸
               ((Scg@ι ⊗ Close@ι′[0]) ⊗ Close@(ι′+2) ⊸^{ι′+2}_{ι} ∗))
      cg = !(f = λp. let (q, d) = p in let (c, e) = q in
                    let (c, w) = ⟨send ⟨e, c⟩, ∗⟩ in let () = w in
                    let () = close c in close d)

    The two steps that need a congruence:

      send ⟨e, c⟩ at ι   the payload of c at ι is Close@ι[0], and e is
                         Close@ι′[0]. E-Conv moves it along
                         ι′[0] ≡ ι[0], which is [se_payload] of ι ≡ ι′.
                         send's own premise ι ≺ ι[0] reads ι ≡ ι′ ≺ ι′[0]
                         and the same alias of the payload points.
      close c at ι+1     the future holds d at ι′+2, so E-App asks
                         ι+1 ≺ ι′+2. The hypothesis states no fact at
                         ι+1. [se_shift] of ι ≡ ι′ gives ι+1 ≡ ι′+1, and
                         program order gives ι′+1 ≺ ι′+2.

    The caller instantiates both variables by one point γ, where the
    alias is reflexivity.

      cg_main = let (g, w) = ⟨cg, ∗⟩ in let () = w in
                let (c, c′) = new ∗ in            C_c = {γ ≺ γ[0], γ[0] ≺ γ+1}
                let (e, e′) = new ∗ in            at γ[0]
                let (d, d′) = new ∗ in            at γ+2
                let () = spawn (λu. let () = u in
                           let (x, c′) = recv c′ in
                           let () = close x in close c′) in
                let () = spawn (λu. let () = u in close e′) in
                let () = spawn (λu. let () = u in close d′) in
                (force g) ⟨⟨c, e⟩, d⟩

    What the congruences are worth. Neither rule is forced by any
    program. A derivation that uses [se_payload] at x[j] ≡ y[j] can state
    that fact in the constraint it read x ≡ y from, and a derivation
    that uses [se_shift] at x+1 ≡ y+1 can state that one. The two rules
    are what lets a constraint carry one alias between base points in
    place of one alias per offset and per payload point, and for an alias
    at every depth that is the difference between a finite constraint
    and an infinite one. A creation constraint cannot state a fact
    between two points that both lie outside the new channel, so an
    alias between two outer points has to come from elsewhere, but
    "elsewhere" is again a constraint or a world, which may state it.
    docs/extensions/literature-examples.md records this. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

(** !⟨κ⟩(Close@κ).Close, one channel sent and then a close. *)
Definition Scg : sty := SSeq (SSnd 1 (TSess SEnd (pvar 0))) SEnd.

Abbreviation cgs a := (Pt (NPayload (NVar a) 0 0) 0).

Definition cg_P (g : fact) : Prop :=
  g = FEq (pvar 0) (pvar 1) ∨ g = FLt (pvar 1) (Pt (NPayload (NVar 1) 0 0) 0).

Definition cg_C : bcs := BCs [] cg_P.

Definition cg_body : ty :=
  TLolli (Some (pv 1 2)) (Some (pv 0 0))
    (TProd (TProd (TSess Scg (pv 0 0)) (TSess SEnd (cgs 1))) (TSess SEnd (pv 1 2)))
    TUnit.

Definition cgbox : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Var 1)
    (LetP (Pair (App ESend (Pair (Var 0) (Var 1))) EUnit) (LetU (Var 0)
      (LetU (App EClos (Var 1)) (App EClos (Var 4)))))))).

(** The creation constraint of c in main, {γ ≺ γ[0], γ[0] ≺ γ+1}. *)
Definition cgc_P (g : fact) : Prop :=
  g = FLt (pvar 0) (cgs 0) ∨ g = FLt (cgs 0) (pv 0 1).

Definition cgc_C : bcs := BCs [] cgc_P.

Definition cg_main : expr :=
  LetP (Pair cgbox EUnit) (LetU (Var 0)
    (let_new_pair (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0)
               (LetP (App ERecv (Var 5)) (LetU (App EClos (Var 1)) (App EClos (Var 0)))))))
        (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
          (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
            (App (App EForce (Var 7)) (Pair (Pair (Var 5) (Var 3)) (Var 1)))))))))).

(** γ at 3k, γ[0] at 1+k: the two facts and program order rise. *)
Definition cg_rank (x : point) : nat :=
  match pt_name x with
  | NVar 0 => 3 * pt_off x
  | NPayload (NVar 0) 0 0 => 1 + pt_off x
  | _ => pt_off x
  end.

Lemma cgc_ok peq plt : cc_ok peq plt cgc_C.
Proof.
  apply (cc_ok_inner peq plt cgc_P (λ x y, cg_rank x < cg_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [p o] _. unfold cg_rank, pt_shift. cbn.
    destruct p as [a|a|q b i]; cbn; [lia| |]; repeat case_match; lia.
  - intros g [-> | ->] _; eexists _, _; split; [done|cbn; lia|done|cbn; lia].
Qed.

Lemma cgbox_typed W F :
  world_wf W → typed W ∅ [] ∅ [] F cgbox (TBox 2 0 cg_C (TLolli None None TUnit cg_body)).
Proof.
  intros HW. unfold cgbox.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open cg_C cg_body. cbn. unfold cg_body.
  (* the facts of C and what the congruences give *)
  assert (∀ Ψ, (cg_C, [pvar 0; pvar 1]) ∈ Ψ → seqs W Ψ (pv 0 0) (pv 1 0)) as Heq.
  { intros Ψ Hg. eapply (se_hyp0 _ _ _ _ (pvar 0) (pvar 1));
      [exact Hg|by left|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ Ψ, (cg_C, [pvar 0; pvar 1]) ∈ Ψ → slt W Ψ (pv 1 0) (cgs 1)) as Hs.
  { intros Ψ Hg. eapply (sl_hyp0 _ _ _ _ (pvar 1) (Pt (NPayload (NVar 1) 0 0) 0));
      [exact Hg|by right|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ Ψ, (cg_C, [pvar 0; pvar 1]) ∈ Ψ → seqs W Ψ (cgs 1) (cgs 0)) as Hpayload.
  { intros Ψ Hg. apply (se_payload W Ψ (pv 1 0) (pv 0 0) 0), se_sym, Heq, Hg. }
  assert (∀ Ψ, (cg_C, [pvar 0; pvar 1]) ∈ Ψ → slt W Ψ (pv 0 0) (cgs 0)) as HsendP.
  { intros Ψ Hg. eapply sl_eql; [by apply Heq|].
    eapply sl_eqr; [by apply Hs|by apply Hpayload]. }
  assert (∀ Ψ, (cg_C, [pvar 0; pvar 1]) ∈ Ψ → slt W Ψ (pv 0 0) (cgs 1)) as Hlo.
  { intros Ψ Hg. eapply sl_eql; [by apply Heq|by apply Hs]. }
  assert (∀ Ψ, (cg_C, [pvar 0; pvar 1]) ∈ Ψ → slt W Ψ (pv 0 0) (pv 1 2)) as Hd.
  { intros Ψ Hg. eapply sl_eql; [by apply Heq|]. apply slt_po_lt; [exact HW|cbn; lia]. }
  assert (∀ Ψ, (cg_C, [pvar 0; pvar 1]) ∈ Ψ → slt W Ψ (pv 0 1) (pv 1 2)) as Hcd.
  { intros Ψ Hg. eapply sl_eql.
    - apply (se_shift W Ψ (pv 0 0) (pv 1 0)), Heq, Hg.
    - apply slt_po_lt; [exact HW|cbn; lia]. }
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ _ 1); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [apply sle_refl, HW|right; first [apply Hlo; by left|apply Hd; by left]]. }
  cbn. eapply (tv_letp W HW _ _ _ _ _ _
                 (TProd (TSess Scg (pv 0 0)) (TSess SEnd (cgs 1))) (TSess SEnd (pv 1 2)));
    [reflexivity|tstep|].
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ (TSess Scg (pv 0 0)) (TSess SEnd (cgs 1)));
    [reflexivity|tstep|].
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess SEnd (cgs 0)) (TSess Scg (pv 0 0)))).
    - tstep; [tstep|].
      (* e : Close@ι′[0] becomes Close@ι[0] along ι′[0] ≡ ι[0] *)
      eapply t_conv; [|tstep]. split; [|apply seq_refl]. apply Hpayload. by left.
    - apply (KTSend _ _ _ 1 (TSess SEnd (pvar 0)) SEnd (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. apply HsendP. by left.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; apply Hd; by left|].
      exists (pv 1 2). split; [done|]. right. apply Hd. by left. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { (* close c at ι+1 against d at ι′+2 *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; apply Hcd; by left|].
    exists (pv 1 2). split; [done|]. right. apply Hcd. by left. }
  tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|].
  exists (pv 1 2). split; [done|]. apply sle_refl, HW.
Qed.

Lemma cg_typed : styped ∅ [] [] (∅, None) cg_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold cg_main.
  eapply (tv_letp W HW _ _ _ _ _ _ (TBox 2 0 cg_C (TLolli None None TUnit cg_body)) TUnit);
    [reflexivity| |].
  { tstep; [tstep|apply cgbox_typed, HW]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_open W _ _ ∅ _ _ _ _ Scg cgc_C); [apply cgc_ok|constructor|].
  fresh_clean.
  set (Ψ := [(cgc_C, [pvar 0])]).
  assert (slt W Ψ (pvar 0) (cgs 0)) as Hgs.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (cgs 0)); [by left|by left|cbn; lia|done|done]. }
  assert (slt W Ψ (cgs 0) (pv 0 1)) as Hsg.
  { eapply (sl_hyp0 _ _ _ _ (cgs 0) (pv 0 1)); [by left|by right|cbn; lia|done|done]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) cg_C [pvar 0; pvar 0]) as HC.
  { apply bcs_hold_intro. intros g [-> | ->] _; cbn; [apply se_refl|exact Hgs]. }
  assert (Forall (skn W Ψ) [pvar 0; pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|].
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (cgs 0) HWs).
  { eapply skn_inst; [by left|by left|done]. }
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (pv 0 2) HWs).
  { eapply skn_inst; [by left|by left|done]. }
  cbn. tstep.
  { (* the receiver of c: recv at γ, close the payload at γ[0], close at γ+1 *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pv 0 0)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_letp W HW _ _ _ _ _ _ (TSess SEnd (cgs 0)) (TSess SEnd (pv 0 1)));
      [reflexivity| |].
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (dual Scg) (pv 0 0))).
      - tstep.
      - apply KTRecv.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW). }
    cbn. tstep.
    { tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hsg|].
      exists (pv 0 1). split; [done|]. right. exact Hsg. }
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { (* close e′ at γ[0] *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (cgs 0)) (Some (cgs 0)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (cgs 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { (* close d′ at γ+2 *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 2)) (Some (pv 0 2)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 0 2). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 cg_C None cg_body [pvar 0; pvar 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep; [tstep|tstep; [tstep|tstep]].
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem cg_deadlock_free : deadlock_free (∅, {[+ cg_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply cg_typed].
Qed.
