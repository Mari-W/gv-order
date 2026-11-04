(** * Falling sessions of PGV: typable

    docs/extensions/adequacy/pgv-adequacy.md §8 gives two closed programs
    that repaired PGV types with a session whose priorities fall,
    S1 = !⁵1.?⁰1.end⁶? (theories/pgv/PGVFalling.v, [fall2_typed] and
    [fallxy_typed]). No translation that reads a point off a session
    type covers [fallxy] (§8.2), and the section states that a
    derivation with a fresh point per [new] exists without giving it.
    This file gives both derivations in the core ([fall2_styped],
    [fallxy_styped]) and deadlock freedom through [soundness_source].

    [fall2] is the pair of threads of §2.

      fall2 = let (x, y) = new ∗ in
              spawn (λu. let () = u in
                         let (v, y) = recv y in let () = v in close (send ⟨∗, y⟩));
              let x = send ⟨∗, x⟩ in let (v, x) = recv x in let () = v in close x

    The channel sits at ξ, and its three actions at ξ, ξ+1, ξ+2 need
    program order only.

    [fallxy] is the program of §8.1.

      fallxy = let (x, x̄) = new ∗ in let (b, b̄) = new ∗ in let (c, c̄) = new ∗ in
               spawn (λu. let () = u in
                          let b = send ⟨∗, b⟩ in let x = send ⟨∗, x⟩ in
                          let (v, x) = recv x in let () = v in close x; close b);
               spawn (partner1 x̄); spawn (partner2 b̄); spawn (partner1 c̄);
               let c = send ⟨∗, c⟩ in let (d, d̄) = new ∗ in spawn (partner2 d̄);
               let (v, c) = recv c in let () = v in
               let d = send ⟨∗, d⟩ in close c; close d
      partner1 y = λu. let () = u in let (v, y) = recv y in let () = v in close (send ⟨∗, y⟩)
      partner2 y = λu. let () = u in recvclose y

    x and c have S1 = !∗.?∗.Close ([FS1]) and b and d have S2 = !∗.Close.
    With x at ξ, b at β, c at γ and d at δ, the thread X asks β ≺ ξ at
    its send on b, and ξ ≺ β+1, ξ+1 ≺ β+1 and ξ+2 ≺ β+1 at its actions
    on x while it holds b. The main thread asks γ+1 ≺ δ at its receive
    on c, δ ≺ γ+2 at its send on d and γ+2 ≺ δ+1 at its close of c.
    The creation constraints state them.

      x : ∅      b : {β ≺ ξ, ξ+2 ≺ β+1}      c : ∅
      d : {γ+1 ≺ δ, δ ≺ γ+2, γ+2 ≺ δ+1}

    §8.2 names the first fact of each constraint. The others are the
    facts at the later instants of the same threads. Each fact relates
    the new channel to one older one, so each constraint is conservative
    over the context. b's constraint orders β ≺ ξ ≺ ξ+1 ≺ ξ+2 ≺ β+1 and
    d's orders γ+1 ≺ δ ≺ γ+2 ≺ δ+1, so neither closes a cycle.

    In PGV the priority of x falls from 5 to 0 along the session. Here
    the points rise along program order, and the facts against other
    channels say where each instant of x lies. The two readings differ
    in what a point means: PGV's priority of an endpoint is a property
    of the current instant (pgv-adequacy.md §2), our point is one
    instant of one channel.

    Simplifications. The payload 1 is ∗, PGV's [wait] and [close] are
    both [close], and [partner] is written out for both session types.
    PGV's [let y = M in N] is an application of λy. N. The main thread
    of [fallxy] writes [let c = send ⟨∗, c⟩ in …] as
    [let (c, _) = ⟨send ⟨∗, c⟩, ∗⟩ in …], because the λ of an
    application needs an upper point above every action of its body,
    and the body creates d, which has no point outside it. The other
    lets are applications, as in PGV. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.lit.LitLib.
From LRGV Require Import examples.cfst.CfstTools.

Set Default Proof Using "All".

(** !∗.?∗.Close *)
Definition FS1 : sty := SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) SEnd).

(** The partner of FS1 and of S2 = Sd on the channel variable k. *)
Definition partner1 (k : nat) : expr :=
  Lam (LetU (Var 0) (LetP (App ERecv (Var k)) (LetU (Var 1) (sendclose (Var 0))))).
Definition partner2 (k : nat) : expr :=
  Lam (LetU (Var 0) (recvclose (Var k))).

(** ** fall2 *)

Definition fall2_main : expr :=
  let_new_pair
    (LetU (App ESpawn (partner1 1))
      (App (Lam (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0)))))
           (App ESend (Pair EUnit (Var 1))))).

(** ** fallxy

    After the three [new]s x, x̄, b, b̄, c, c̄ are 5 to 0. *)

Definition fx_X : expr :=
  Lam (LetU (Var 0)
    (App (Lam
       (App (Lam
          (LetP (App ERecv (Var 0))
             (LetU (Var 1) (LetU (App EClos (Var 0)) (App EClos (Var 3))))))
        (App ESend (Pair EUnit (Var 7)))))
     (App ESend (Pair EUnit (Var 4))))).

Definition fx_tail : expr :=
  LetP (App ERecv (Var 3)) (LetU (Var 1)
    (App (Lam (LetU (App EClos (Var 1)) (App EClos (Var 0)))) (App ESend (Pair EUnit (Var 3))))).

Definition fallxy_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn fx_X)
      (LetU (App ESpawn (partner1 5))
        (LetU (App ESpawn (partner2 3))
          (LetU (App ESpawn (partner1 1))
            (LetP (Pair (App ESend (Pair EUnit (Var 1))) EUnit) (LetU (Var 0)
              (let_new_pair (LetU (App ESpawn (partner2 1)) fx_tail)))))))))).

(** A partner of FS1 on the point (a, 0), spawned. *)
Ltac fx_partner1 HW a :=
  tstep;
  [ tstep; [|apply KTSpawn|done|apply ubs_none];
    eapply (tv_lam _ HW _ _ _ _ _ TUnit TUnit (Some (pv a 2)) (Some (pv a 0)) 0);
      [set_solver|intros y Hy; mem_cases Hy; apply sle_refl, HW|];
    cbn; tstep; [tstep|]; cbn; tstep;
    [ tstep; [tstep|apply KTRecv|kscope|]; po_gate HW (pv a 2)
    | cbn; tstep; [tstep|]; cbn; unfold sendclose; tstep;
      [ tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pv a 1)); cbn; set_solver|done|];
        po_gate HW (pv a 2)
      | apply KTClos | done | po_gate HW (pv a 2) ] ]
  | ].

(** A partner of S2 = Sd on the point (a, 0), spawned. *)
Ltac fx_partner2 HW a :=
  tstep;
  [ tstep; [|apply KTSpawn|done|apply ubs_none];
    eapply (tv_lam _ HW _ _ _ _ _ TUnit TUnit (Some (pv a 1)) (Some (pv a 0)) 0);
      [set_solver|intros y Hy; mem_cases Hy; apply sle_refl, HW|];
    cbn; tstep; [tstep|]; cbn; unfold recvclose; tstep;
    [ tstep; [tstep|apply KTRecv|kscope|]; po_gate HW (pv a 1)
    | cbn; tstep; [tstep|]; cbn; tstep; [tstep|apply KTClos|done|]; po_gate HW (pv a 1) ]
  | ].

(** ** The creation constraints *)

Definition fx0_C : bcs := BCs [] (λ _, False).

Lemma fx0_ok peq plt : cc_ok peq plt fx0_C.
Proof.
  apply (cc_ok_out _ _ fx0_C olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po| | |].
  - intros a b (f & [] & _).
  - intros a b (f & [] & _).
  - intros u p q v (f & [] & _).
Qed.

(** b at 0 under x at 1. *)
Definition fxb_P (g : fact) : Prop := g = FLt (pv 0 0) (pv 1 0) ∨ g = FLt (pv 1 2) (pv 0 1).
Definition fxb_C : bcs := BCs [pvar 0] fxb_P.

Lemma fxb_ok peq plt : cc_ok peq plt fxb_C.
Proof.
  apply (cc_ok_out _ _ fxb_C olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po| | |].
  - intros a b (f & [-> | ->] & _ & E); discriminate E.
  - intros a b (f & [-> | ->] & _ & E); injection E as -> ->; cbn; auto.
  - intros u p q v (f & [-> | ->] & _ & E) (f' & [-> | ->] & _ & E') Hu Hp Hq Hv Hpq;
      injection E as -> ->; injection E' as -> ->; cbn in Hu, Hp, Hq, Hv; try done.
    destruct Hpq as [Hpq|[_ Hpq]]; [discriminate Hpq|cbn in Hpq; lia].
Qed.

(** d at 0 under c at 1. *)
Definition fxd_P (g : fact) : Prop :=
  g = FLt (pv 1 1) (pv 0 0) ∨ g = FLt (pv 0 0) (pv 1 2) ∨ g = FLt (pv 1 2) (pv 0 1).
Definition fxd_C : bcs := BCs [pvar 0] fxd_P.

Lemma fxd_ok peq plt : cc_ok peq plt fxd_C.
Proof.
  apply (cc_ok_out _ _ fxd_C olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po| | |].
  - intros a b (f & [-> | [-> | ->]] & _ & E); discriminate E.
  - intros a b (f & [-> | [-> | ->]] & _ & E); injection E as -> ->; cbn; auto.
  - intros u p q v (f & [-> | [-> | ->]] & _ & E) (f' & [-> | [-> | ->]] & _ & E') Hu Hp Hq Hv Hpq;
      injection E as -> ->; injection E' as -> ->; cbn in Hu, Hp, Hq, Hv; try done.
    + cbn. apply glt_ofs. simpl. lia.
    + destruct Hpq as [Hpq|[_ Hpq]]; [discriminate Hpq|cbn in Hpq; lia].
Qed.

Lemma fallxy_styped : styped ∅ [] [] (∅, None) fallxy_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fallxy_main.
  apply (t_new_open W _ _ ∅ _ _ _ _ FS1 fx0_C); [apply fx0_ok|constructor|].
  fresh_clean.
  apply (t_new_open W _ _ ∅ _ _ _ _ Sd fxb_C); [apply fxb_ok|..].
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  apply (t_new_open W _ _ ∅ _ _ _ _ FS1 fx0_C); [apply fx0_ok|constructor|].
  fresh_clean.
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (pvar 0))) with (pv 2 0).
  change (pt_inst (pshift 1) (pvar 0)) with (pv 1 0).
  match goal with |- typed _ _ ?G _ _ _ _ _ => set (Ψ := G) end.
  assert (slt W Ψ (pv 1 0) (pv 2 0)) as Hbx.
  { eapply (sl_hyp W Ψ [pvar 2] fxb_P [pvar 1] (FLt (pv 0 0) (pv 1 0)));
      [by right; left|by left|fsc|reflexivity]. }
  assert (slt W Ψ (pv 2 2) (pv 1 1)) as Hxb.
  { eapply (sl_hyp W Ψ [pvar 2] fxb_P [pvar 1] (FLt (pv 1 2) (pv 0 1)));
      [by right; left|by right|fsc|reflexivity]. }
  assert (slt W Ψ (pv 2 0) (pv 1 1)) as Hx0.
  { eapply sl_trans; [|exact Hxb]. apply slt_po_lt; [exact HW|lia]. }
  assert (slt W Ψ (pv 2 1) (pv 1 1)) as Hx1.
  { eapply sl_trans; [|exact Hxb]. apply slt_po_lt; [exact HW|lia]. }
  (* the thread X *)
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 1)) (Some (pv 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; [apply sle_refl, HW|right; exact Hbx]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 1)) (Some (pv 2 0)) (TSess SEnd (pv 1 1)) TUnit);
      [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pv 1 1)) (Some (pv 2 0)) 1); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn.
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 1)) (Some (pv 1 1))
                (TSess (SSeq (SRcv 0 TUnit) SEnd) (pv 2 1)) TUnit); [reflexivity| | |].
      + eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pv 1 1)) (Some (pv 1 1)) 2); [set_solver| |].
        { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
        cbn. tstep.
        * eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 2 1)) (TSess (SSeq (SRcv 0 TUnit) SEnd) (pv 2 1)));
            [tstep|apply KTRecv|kscope|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hx1|].
          exists (pv 1 1). split; [done|]. right; exact Hx1.
        * cbn. tstep; [tstep|]. cbn. tstep.
          -- eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 2 2)) (TSess SEnd (pv 2 2))); [tstep|apply KTClos|done|].
             apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hxb|].
             exists (pv 1 1). split; [done|]. right; exact Hxb.
          -- eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 1)) (TSess SEnd (pv 1 1))); [tstep|apply KTClos|done|].
             apply ubs_intro; [intros y Hy; mem_cases Hy|].
             exists (pv 1 1). split; [done|]. apply sle_refl, HW.
      + eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 2 0)) (TProd TUnit (TSess FS1 (pv 2 0)))).
        * tstep; tstep.
        * apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) SEnd) (pv 2 0)). cbn. set_solver.
        * kscope.
        * apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hx0|].
          exists (pv 1 1). split; [done|]. right; exact Hx0.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 1). split; [done|]. apply sle_refl, HW.
    - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0)) (TProd TUnit (TSess Sd (pv 1 0)))).
      + tstep; tstep.
      + apply (KTSend _ _ _ 0 TUnit SEnd (pv 1 0)). cbn. set_solver.
      + kscope.
      + apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hbx|].
        exists (pv 1 1). split; [done|]. right. apply slt_po_lt; [exact HW|lia].
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 1). split; [done|]. apply sle_refl, HW. }
  cbn. fx_partner1 HW 2. cbn. fx_partner2 HW 1. cbn. fx_partner1 HW 0. cbn.
  (* the main thread: send on c at γ, then d under its constraint *)
  tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0)) (TProd TUnit (TSess FS1 (pv 0 0)))).
    - tstep; tstep.
    - apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) SEnd) (pv 0 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn.
  change (pt_shift 1 (pv 0 0)) with (pv 0 1).
  apply (t_new_open W _ _ ∅ _ _ _ _ Sd fxd_C); [apply fxd_ok|..].
  { constructor; [eapply skn_inst; [by right; right; left|by left|done]|constructor]. }
  fresh_clean.
  change (pt_inst (pshift 1) (pv 0 1)) with (pv 1 1).
  clear Hbx Hxb Hx0 Hx1.
  match goal with |- typed _ _ ?G _ _ _ _ _ => set (Ψ' := G) end.
  assert (slt W Ψ' (pv 1 1) (pv 0 0)) as Hcd.
  { eapply (sl_hyp W Ψ' [pt_inst (pshift 1) (pvar 0)] fxd_P [pvar 0] (FLt (pv 1 1) (pv 0 0)));
      [by right; right; right; left|by left|fsc|reflexivity]. }
  assert (slt W Ψ' (pv 0 0) (pv 1 2)) as Hdc.
  { eapply (sl_hyp W Ψ' [pt_inst (pshift 1) (pvar 0)] fxd_P [pvar 0] (FLt (pv 0 0) (pv 1 2)));
      [by right; right; right; left|by right; left|fsc|reflexivity]. }
  assert (slt W Ψ' (pv 1 2) (pv 0 1)) as Hcd2.
  { eapply (sl_hyp W Ψ' [pt_inst (pshift 1) (pvar 0)] fxd_P [pvar 0] (FLt (pv 1 2) (pv 0 1)));
      [by right; right; right; left|by right; right|fsc|reflexivity]. }
  fx_partner2 HW 0. cbn.
  (* receive on c at γ+1 while d waits at δ *)
  tstep.
  { tstep; [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hcd|done]. }
  cbn. tstep; [tstep|]. cbn.
  eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 0 1)) (Some (pv 1 2)) (TSess SEnd (pv 0 1)) TUnit);
    [reflexivity| | |].
  - eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pv 0 1)) (Some (pv 1 2)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep.
    + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 2)) (TSess SEnd (pv 1 2))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hcd2|].
      exists (pv 0 1). split; [done|]. right; exact Hcd2.
    + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 1)) (TSess SEnd (pv 0 1))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
  - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0)) (TProd TUnit (TSess Sd (pv 0 0)))).
    + tstep; tstep.
    + apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)). cbn. set_solver.
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hdc|done].
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma fall2_styped : styped ∅ [] [] (∅, None) fall2_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fall2_main.
  apply (t_new_open W _ _ ∅ _ _ _ _ FS1 fx0_C); [apply fx0_ok|constructor|].
  fresh_clean.
  fx_partner1 HW 0. cbn.
  eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 0 2)) None (TSess (SSeq (SRcv 0 TUnit) SEnd) (pv 0 1)) TUnit);
    [reflexivity| | |].
  - eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pv 0 2)) None 0); [set_solver|cbn; set_solver|].
    cbn. tstep.
    + tstep; [tstep|apply KTRecv|kscope|]. po_gate HW (pv 0 2).
    + cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|]. po_gate HW (pv 0 2).
  - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0)) (TProd TUnit (TSess FS1 (pv 0 0)))).
    + tstep; tstep.
    + apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) SEnd) (pv 0 0)). cbn. set_solver.
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** ** Deadlock freedom, through [soundness_source] *)

Theorem fall2_deadlock_free : deadlock_free (∅, {[+ fall2_main +]}).
Proof. apply (soundness_source_nil _ TUnit); [constructor|apply fall2_styped]. Qed.

Theorem fallxy_deadlock_free : deadlock_free (∅, {[+ fallxy_main +]}).
Proof. apply (soundness_source_nil _ TUnit); [constructor|apply fallxy_styped]. Qed.
