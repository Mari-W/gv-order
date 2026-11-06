(** * The congruence example without ≡: typable (branch no-eq)

    On main this file held the smallest program whose derivation used
    the congruences of ≡ (successor and payload). Its box took two point
    variables ι and ι′ aliased by its constraint {ι ≡ ι′, …}, and every
    caller instantiated both by one point γ. Without ≡ the alias is
    syntactic equality, so the box takes one variable and the two
    congruence steps become reflexivity.

      Scg = !⟨κ⟩(Close@κ).Close
      C   = {ι ≺ (ι[0])‾,  ῑ ≺ (ι[0])‾}                          (positions from 0)
      cg : □(∀ι. C. ∗ ⊸
               ((Scg@ι ⊗ Close@ι[0]) ⊗ Close@(ι+2) ⊸^{ι+2}_{ῑ} ∗))
      cg = !(f = λp. let (q, d) = p in let (c, e) = q in
                    let (c, w) = ⟨send ⟨e, c⟩, ∗⟩ in let () = w in
                    let () = close c in close d)

    send ⟨e, c⟩ at ι reads its payload Close@ι[0] directly. close c at
    ι+1 against d at ι+2 is program order.

      cg_main = let (g, w) = ⟨cg, ∗⟩ in let () = w in
                let (c, c′) = new ∗ in            C_c = {γ ≺ (γ[0])‾, γ̄ ≺ (γ[0])‾, γ[0] ≺ γ+1, γ[0] ≺ γ̄+1}
                let (e, e′) = new@(γ[0]) ∗ in
                let (d, d′) = new@(γ+2) ∗ in
                let () = spawn (λu. let () = u in
                           let (x, c′) = recv c′ in
                           let () = close x in close c′) in
                let () = spawn (λu. let () = u in close e′) in
                let () = spawn (λu. let () = u in close d′) in
                (force g) ⟨⟨c, e⟩, d⟩

    What the congruences were worth (docs/extensions/no-equality.md).
    They let one alias between base points stand for an alias at every
    offset and payload depth. A box whose variables are always
    instantiated alike needs no alias at all, it needs fewer variables. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

(** !⟨κ⟩(Close@κ).Close, one channel sent and then a close. *)
Definition Scg : sty := SSeq (SSnd 1 (TSess SEnd (pvar 0))) SEnd.

Abbreviation cgs a := (Pt (NPayload (NVar a) 0 0) 0).

(** Without ≡ the box has one variable ι, the former ι = ι′. The send
    owes ι ≺ (ι[0])‾, the partner point of the payload, and the lower
    point ῑ of the box asks ῑ ≺ (ι[0])‾. *)
Definition cg_P (g : fact) : Prop :=
  g = FLt (pvar 0) (pt_dual (cgs 0)) ∨ g = FLt (pt_dual (pvar 0)) (pt_dual (cgs 0)).

Definition cg_C : bcs := BCs [] cg_P.

Definition cg_body : ty :=
  TLolli (Some (pv 0 2)) (Some (pt_dual (pv 0 0)))
    (TProd (TProd (TSess Scg (pv 0 0)) (TSess SEnd (cgs 0))) (TSess SEnd (pv 0 2)))
    TUnit.

Definition cgbox : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Var 1)
    (LetP (Pair (App ESend (Pair (Var 0) (Var 1))) EUnit) (LetU (Var 0)
      (LetU (App EClos (Var 1)) (App EClos (Var 4)))))))).

(** The creation constraint of c in main, {γ ≺ (γ[0])‾, γ̄ ≺ (γ[0])‾,
    γ[0] ≺ γ+1, γ[0] ≺ γ̄+1}. *)
Definition cgc_P (g : fact) : Prop :=
  g = FLt (pvar 0) (pt_dual (cgs 0)) ∨ g = FLt (pt_dual (pvar 0)) (pt_dual (cgs 0)) ∨
  g = FLt (cgs 0) (pv 0 1) ∨ g = FLt (cgs 0) (pt_dual (pv 0 1)).

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
  - intros [p pb o] _. unfold cg_rank, pt_shift. cbn.
    destruct p as [a|a|q b i]; cbn; [lia| |]; repeat case_match; lia.
  - intros g [-> | [-> | [-> | ->]]] _; eexists _, _; (split; [done|]); cbn; lia.
  - intros [p pb o] _. unfold cg_rank, pt_shift, pt_dual. cbn.
    destruct p as [a|a|q b i]; cbn; [lia| |]; repeat case_match; lia.
Qed.

Lemma cgbox_typed W F :
  world_wf W → typed W ∅ [] ∅ [] F cgbox (TBox 1 0 cg_C (TLolli None None TUnit cg_body)).
Proof.
  intros HW. unfold cgbox.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open1 cg_C cg_body. cbn. unfold cg_body.
  set (Ψ := [(cg_C, [pvar 0])]).
  assert (slt W Ψ (pv 0 0) (pt_dual (cgs 0))) as HsendP.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (pt_dual (cgs 0))); [by left|by left|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (pt_dual (pv 0 0)) (pt_dual (cgs 0))) as Hlo.
  { eapply (sl_hyp0 _ _ _ _ (pt_dual (pvar 0)) (pt_dual (cgs 0))); [by left|by right|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (pv 0 0) (pv 0 2)) as Hd by (apply slt_po_lt; [exact HW|cbn; lia]).
  assert (slt W Ψ (pv 0 1) (pt_dual (pv 0 2))) as Hcd by apply (sl_dpo W Ψ (pv 0 1)).
  assert (slt W Ψ (pv 0 0) (pt_dual (pv 0 2))) as Hd'.
  { eapply sl_trans; [apply (slt_po_lt W Ψ _ 0 1 HW); lia|exact Hcd]. }
  assert (slt W Ψ (pt_dual (pv 0 0)) (pt_dual (pv 0 2))) as Hld.
  { pose proof (slt_po W Ψ (pt_dual (pv 0 0)) HW) as G1. pose proof (slt_po W Ψ (pt_dual (pv 0 1)) HW) as G2.
    unfold pt_shift, pt_dual in G1, G2. simpl in G1, G2. eapply sl_trans; [exact G1|exact G2]. }
  assert (slt W Ψ (pv 0 1) (pv 0 2)) as Hcd' by (apply slt_po_lt; [exact HW|cbn; lia]).
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ _ 1); [set_solver| |].
  { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; first [exact Hlo|exact Hld]]. }
  cbn. eapply (tv_letp W HW _ _ _ _ _ _
                 (TProd (TSess Scg (pv 0 0)) (TSess SEnd (cgs 0))) (TSess SEnd (pv 0 2)));
    [reflexivity|tstep|].
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ (TSess Scg (pv 0 0)) (TSess SEnd (cgs 0)));
    [reflexivity|tstep|].
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess SEnd (cgs 0)) (TSess Scg (pv 0 0)))).
    - tstep; tstep.
    - apply (KTSend _ _ _ 1 (TSess SEnd (pvar 0)) SEnd (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. exact HsendP.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hd'|].
      exists (pv 0 2). split; [done|]. right. exact Hd. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { (* close c at ι+1 against d at ι+2 *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hcd|].
    exists (pv 0 2). split; [done|]. right. exact Hcd'. }
  tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|].
  exists (pv 0 2). split; [done|]. apply sle_refl, HW.
Qed.

Lemma cg_typed : styped ∅ [] [] (∅, None) cg_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold cg_main.
  eapply (tv_letp W HW _ _ _ _ _ _ (TBox 1 0 cg_C (TLolli None None TUnit cg_body)) TUnit);
    [reflexivity| |].
  { tstep; [tstep|apply cgbox_typed, HW]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_open W _ _ ∅ _ _ _ _ Scg cgc_C); [apply cgc_ok|constructor|].
  fresh_clean.
  set (Ψ := [(cgc_C, [pvar 0])]).
  assert (slt W Ψ (pvar 0) (pt_dual (cgs 0))) as Hgs.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (pt_dual (cgs 0))); [by left|by left|cbn; lia|done|done]. }
  assert (slt W Ψ (pt_dual (pvar 0)) (pt_dual (cgs 0))) as Hgs'.
  { eapply (sl_hyp0 _ _ _ _ (pt_dual (pvar 0)) (pt_dual (cgs 0))); [by left|by right; left|cbn; lia|done|done]. }
  assert (slt W Ψ (cgs 0) (pv 0 1)) as Hsg.
  { eapply (sl_hyp0 _ _ _ _ (cgs 0) (pv 0 1)); [by left|by right; right; left|cbn; lia|done|done]. }
  assert (slt W Ψ (cgs 0) (pt_dual (pv 0 1))) as Hsg'.
  { eapply (sl_hyp0 _ _ _ _ (cgs 0) (pt_dual (pv 0 1))); [by left|by right; right; right|cbn; lia|done|done]. }
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) cg_C [pvar 0]) as HC.
  { apply bcs_hold_intro. intros g [-> | ->] _; cbn; [exact Hgs|exact Hgs']. }
  assert (Forall (skn W Ψ) [pvar 0]) as HK.
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (cgs 0) HWs).
  { eapply skn_inst; [by left|by left|done]. }
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (pv 0 2) HWs).
  { eapply skn_inst; [by left|by left|done]. }
  cbn. tstep.
  { (* the receiver of c: recv at γ, close the payload at γ[0], close at γ+1 *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 0 1))) (Some (pv 0 0)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_letp W HW _ _ _ _ _ _ (TSess SEnd (cgs 0)) (TSess SEnd (pt_dual (pv 0 1))));
      [reflexivity| |].
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pt_dual (pv 0 0))) (TSess (dual Scg) (pt_dual (pv 0 0)))).
      - tstep.
      - apply KTRecv.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_dual (pv 0 1)). split; [done|]. right. apply (slt_po W _ (pt_dual (pv 0 0)) HW). }
    cbn. tstep.
    { tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hsg|].
      exists (pt_dual (pv 0 1)). split; [done|]. right. exact Hsg'. }
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (pv 0 1)). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { (* close e′ at γ[0] *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (cgs 0))) (Some (cgs 0)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (cgs 0)). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { (* close d′ at γ+2 *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 0 2))) (Some (pv 0 2)) 0);
      [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (pv 0 2)). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 cg_C None cg_body [pvar 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep; [tstep|tstep; [tstep|tstep]].
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem cg_deadlock_free : deadlock_free (∅, {[+ cg_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply cg_typed].
Qed.
