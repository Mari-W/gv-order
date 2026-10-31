(** * The arithmetic expression server (Thiemann and Vasconcelos 2016, Listing 3, stage D)

      TermC = µX. ⊕(!∗, ⊕(X;X, X;X))
      TermD = dual TermC = µX. &(?∗, &(X;X, X;X))

    The ternary choice {Const, Add, Mult} of TermChan becomes binary
    choices, Const = select₁, Add = select₂ select₁, Mult = select₂
    select₂. Int becomes ∗. [receiveEval] serves TermD;β. On Const it
    receives the constant, on Add and Mult it recurses on both subterms.
    The paper returns n₁+n₂ or n₁∗n₂ next to the channel. The calculus
    has no integers, so receiveEval returns the channel alone, and the
    Add and Mult branches run the same code.

      receiveEval : □(∀κ ζ β. C. ∗ ⊸^⊥_⊤ ((TermD;β)@κ ⊸^ζ_⊤ ∃κ′≽κ. C′. β@κ′))
      C  = {κ+k ≺ ζ ∣ k}      C′ = {κ ≺ κ′} ∪ {κ′+k ≺ ζ ∣ k}

    computeService runs receiveEval on TermD;(!∗;Close) and sends the
    result. The client is the paper's, Add (Const 5) (Mult (Const 7)
    (Const 9)) followed by a receive, as a fixed sequence of selections
    and sends. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.TreeSum.

Set Default Proof Using "All".

Definition TermC : sty :=
  SMu (SPlus (SSnd 0 TUnit) (SPlus (SSeq (SVar 0) (SVar 0)) (SSeq (SVar 0) (SVar 0)))).

Definition TermD : sty :=
  SMu (SWith (SRcv 0 TUnit) (SWith (SSeq (SVar 0) (SVar 0)) (SSeq (SVar 0) (SVar 0)))).

(** The choice between Add and Mult. *)
Definition OpC : sty := SPlus (SSeq TermC TermC) (SSeq TermC TermC).
Definition OpD : sty := SWith (SSeq TermD TermD) (SSeq TermD TermD).

Lemma dual_TermC : dual TermC = TermD.
Proof. reflexivity. Qed.

Lemma unfoldS_TermC : unfoldS TermC = SPlus (SSnd 0 TUnit) OpC.
Proof. reflexivity. Qed.

Lemma unfoldS_TermD : unfoldS TermD = SWith (SRcv 0 TUnit) OpD.
Proof. reflexivity. Qed.

Lemma TermC_contractive : contractive TermC.
Proof. unfold contractive. by rewrite unfoldS_TermC. Qed.

Lemma TermD_contractive : contractive TermD.
Proof. unfold contractive. by rewrite unfoldS_TermD. Qed.

Lemma TermC_hc : hcontractive TermC.
Proof.
  apply (hc_ind (λ s, s = TermC)); [|done]. intros n s -> IH.
  specialize (IH TermC eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_TermC). cbn [view]. split; [apply hcontractive_snd|].
  destruct n as [|m]; [done|]. rewrite ahc_S. unfold hc_step, OpC.
  rewrite (hd_of _ _ (unfoldS_plus _ _)). cbn [view].
  pose proof (ahc_mono (S m) m TermC ltac:(lia) IH) as IH'. split; by apply ahc_seq.
Qed.

Lemma TermD_hc : hcontractive TermD.
Proof.
  apply (hc_ind (λ s, s = TermD)); [|done]. intros n s -> IH.
  specialize (IH TermD eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_TermD). cbn [view]. split; [apply hcontractive_rcv|].
  destruct n as [|m]; [done|]. rewrite ahc_S. unfold hc_step, OpD.
  rewrite (hd_of _ _ (unfoldS_with _ _)). cbn [view].
  pose proof (ahc_mono (S m) m TermD ltac:(lia) IH) as IH'. split; by apply ahc_seq.
Qed.

(** The heads of TermC;s and TermD;s. *)
Lemma TermC_seq s : seq (SSeq TermC s) (SPlus (SSeq (SSnd 0 TUnit) s) (SSeq OpC s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply TermC_contractive|by rewrite unfoldS_TermC].
  by rewrite unfoldS_TermC, unfoldS_plus.
Qed.

Lemma TermD_seq s : seq (SSeq TermD s) (SWith (SSeq (SRcv 0 TUnit) s) (SSeq OpD s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply TermD_contractive|by rewrite unfoldS_TermD].
  by rewrite unfoldS_TermD, unfoldS_with.
Qed.

(** Add and Mult distributed over the continuation and reassociated. *)
Lemma opC_seq s : hcontractive s →
  seq (SSeq OpC s) (SPlus (SSeq TermC (SSeq TermC s)) (SSeq TermC (SSeq TermC s))).
Proof.
  intros Hs. eapply seq_trans; [apply seq_choice_dist_plus|].
  apply seq_plus_cong; apply seq_assoc; auto using TermC_hc.
Qed.

Lemma opD_seq s : hcontractive s →
  seq (SSeq OpD s) (SWith (SSeq TermD (SSeq TermD s)) (SSeq TermD (SSeq TermD s))).
Proof.
  intros Hs. eapply seq_trans; [apply seq_choice_dist_with|].
  apply seq_with_cong; apply seq_assoc; auto using TermD_hc.
Qed.

(** Case with Θ = ∅ and two equal branches. *)
Lemma tv_case_same W Φ Ψ Δ F e e1 T1 T : world_wf W →
  sok e 0 (Lam (Pair e1 e1)) 0 Δ = true →
  typed W Φ Ψ ∅ (lp e 0 Δ) (sf_union F (lenv_heads (lp (Lam (Pair e1 e1)) 0 Δ))) e (TSum T1 T1) →
  typed W Φ Ψ ∅ (Some T1 :: lp (Lam (Pair e1 e1)) 0 Δ) F e1 T →
  typed W Φ Ψ ∅ Δ F (Case e e1 e1) T.
Proof. intros HW Hs H H1. by apply (tv_case W HW Φ Ψ Δ F e e1 e1 T1 T1 T). Qed.

(** ** receiveEval *)

Definition reval_body : ty :=
  TLolli (Some (pv 1 0)) None (TSess (SSeq TermD (SVar 0)) (pv 0 0)) send_after.

Definition reval_ty : ty := TBox 2 1 send_C (TLolli None None TUnit reval_body).

(** Add and Mult: two recursive calls, the second inside an open and
    re-pack, as in drain. *)
Definition reval_op : expr :=
  App (Lam (App (Lam (Var 0)) (App (App EForce (Var 4)) (Var 0))))
      (App (App EForce (Var 3)) (Var 0)).

Definition reval : expr :=
  EBox (Lam (Case (App EBra (Var 0))
    (LetP (App ERecv (Var 0)) (LetU (Var 1) (Var 0)))
    (Case (App EBra (Var 0)) reval_op reval_op))).

Lemma reval_ty_pscoped : pscoped 0 reval_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma reval_inst x z s :
  sinst_ty (slist [s]) (ty_inst [x; z] reval_body) =
  TLolli (Some z) None (TSess (SSeq TermD s) x)
    (TEx (Some x) 1 (BCs [x; z] after_P) (TSess s (pv 0 0))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma reval_typed W F : world_wf W → typed W ∅ [] ∅ [] F reval reval_ty.
Proof.
  intros HW. unfold reval, reval_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  intros ss Hss Hhc. destruct ss as [|s [|]]; try discriminate Hss.
  rewrite Forall_singleton in Hhc. fold reval_ty.
  change (lenv_pinst (pshift 2) [Some reval_ty]) with [Some (pinst_ty (pshift 2) reval_ty)].
  rewrite (pinst_closed _ reval_ty) by apply reval_ty_pscoped.
  cbn. fold TermD. change (bcs_inst (pshift 2) send_C) with send_C.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 0))
              (TSess (SWith (SSeq (SRcv 0 TUnit) s) (SSeq OpD s)) (pv 0 0))).
    + eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TermD_seq].
    + apply KTBra.
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0).
  - (* Const: receive, then pack at κ+2 *)
    cbn. apply (t_pack W _ _ _ _ _ _ (Some (pv 0 0)) 1 after_C (TSess s (pv 0 0)) [pv 0 2]).
    + done.
    + apply Forall_singleton. apply (skn_in W _ send_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done].
    + unfold after_C. apply bcs_hold_env. intros f [-> | (k & ->)] _; cbn.
      * eapply sl_trans; [apply (slt_po W _ (pv 0 0) HW)|apply (slt_po W _ (pv 0 1) HW)].
      * hyp0 (pv 0 (S (S k))) (pv 1 0).
    + intros y Hy. mem_cases Hy. right.
      eapply sl_trans; [apply (slt_po W _ (pv 0 0) HW)|apply (slt_po W _ (pv 0 1) HW)].
    + cbn. tstep.
      { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 1)) (TSess (SSeq (SRcv 0 TUnit) s) (pv 0 1))).
        - tstep.
        - apply KTRecv.
        - kscope.
        - apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 1) (pv 1 0). }
      cbn. tstep; [tstep|]. tstep.
  - (* Add or Mult *)
    cbn. eapply (tv_case_same W _ _ _ _ _ _ (TSess (SSeq TermD (SSeq TermD s)) (pv 0 2))); [exact HW|reflexivity| |].
    { eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 1))
                (TSess (SWith (SSeq TermD (SSeq TermD s)) (SSeq TermD (SSeq TermD s))) (pv 0 1))).
      - eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply opD_seq].
      - apply KTBra.
      - done.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 1) (pv 1 0). }
    unfold reval_op. cbn.
    set (R1 := TEx (Some (pv 0 2)) 1 (BCs [pv 0 2; pv 1 0] after_P) (TSess (SSeq TermD s) (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 1 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pv 0 2)) 1 (BCs [pv 0 2; pv 1 0] after_P)
                  (TSess (SSeq TermD s) (pv 0 0)) _
                  (<[2:=Some (pv 2 0)]> (<[1:=Some (pv 2 0)]> (<[0:=None]> ∅)))
                  [(send_C, [pv 1 0; pv 2 0]); (BCs [pv 1 2; pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq TermD s) (pv 0 0)); None; None; None; Some reval_ty]
                  (∅, Some 2)
                  (TEx (Some (pv 1 0)) 1 (BCs [pv 1 0; pv 2 0] after_P) (TSess s (pv 0 0))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (R2 := TEx (Some (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P) (TSess s (pv 0 0))).
      assert (∀ Ψ, (BCs [pv 1 2; pv 2 0] after_P, [pv 0 0]) ∈ Ψ → (send_C, [pv 1 0; pv 2 0]) ∈ Ψ →
                   Forall (skn W Ψ) [pv 0 0; pv 2 0]) as Hkn.
      { intros Ψ H1 H2. apply Forall_cons. split; [|apply Forall_singleton].
        - apply (skn_in W Ψ (BCs [pv 1 2; pv 2 0] after_P) [pv 0 0] (pv 0 0)); [exact H1|by left|done].
        - apply (skn_in W Ψ send_C [pv 1 0; pv 2 0] (pv 2 0)); [exact H2|by right; left|done]. }
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None R2); [reflexivity| | |].
      * eapply (tv_lam W HW _ _ _ _ _ R2 _ (Some (pv 2 0)) None 3); [set_solver|cbn; set_solver|].
        cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P)
                  (TSess s (pv 0 0)) _
                  (<[3:=Some (pv 3 0)]> (<[2:=Some (pv 3 0)]> (<[1:=Some (pv 3 0)]> (<[0:=None]> ∅))))
                  [(send_C, [pv 2 0; pv 3 0]); (BCs [pv 2 2; pv 3 0] after_P, [pv 1 0]);
                   (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]
                  [Some (TSess s (pv 0 0)); None; None; None; None; Some reval_ty]
                  (∅, Some 3)
                  (TEx (Some (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0))));
          [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
        assert (slt W [(send_C, [pv 2 0; pv 3 0]); (BCs [pv 2 2; pv 3 0] after_P, [pv 1 0]);
                       (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])] (pv 2 0) (pv 0 0)) as Hch.
        { eapply sl_trans; [apply (slt_po W _ (pv 2 0) HW)|].
          eapply sl_trans; [apply (slt_po W _ (pv 2 1) HW)|].
          eapply sl_trans.
          - eapply (sl_hyp W _ [pv 2 2; pv 3 0] after_P [pv 1 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|by left|fsc|reflexivity].
          - eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|by left|fsc|reflexivity]. }
        apply (t_pack W _ _ _ _ _ _ (Some (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0)) [pv 0 0]).
        -- done.
        -- apply Forall_singleton.
           apply (skn_in W _ (BCs [pv 1 0; pv 3 0] after_P) [pv 0 0] (pv 0 0)); [inlist|by left|done].
        -- apply bcs_hold_env. intros f [-> | (k & ->)] _; cbn; [exact Hch|].
           eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 0 k) (pv 2 0)));
             [inlist|right; by exists k|fsc|reflexivity].
        -- intros y Hy. mem_cases Hy. by right.
        -- cbn. tstep.
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq TermD s) (pv 0 0)) R2);
          [reflexivity| | |].
        -- unfold R2. rewrite <-(reval_inst (pv 0 0) (pv 2 0) s).
           apply (typed_force W _ _ _ _ _ _ 2 1 send_C None reval_body [pv 0 0; pv 2 0] [s]);
             [done|done| | |done| |apply ubs_none|tstep].
           ++ apply bcs_hold_intro. intros g (k & ->) _. cbn.
              eapply (sl_hyp W _ [pv 1 2; pv 2 0] after_P [pv 0 0] (FLt (pv 0 k) (pv 2 0)));
                [inlist|right; by exists k|fsc|reflexivity].
           ++ apply Hkn; inlist.
           ++ by apply Forall_singleton.
        -- tstep.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy|].
           exists (pv 2 0). split; [done|]. apply sle_refl, HW.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. apply sle_refl, HW.
    + eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None
                (TSess (SSeq TermD (SSeq TermD s)) (pv 0 2)) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(reval_inst (pv 0 2) (pv 1 0) (SSeq TermD s)).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None reval_body [pv 0 2; pv 1 0] [SSeq TermD s]);
          [done|done| | |done| |apply ubs_none|tstep].
        -- apply bcs_hold_self; [by left|vb_list|]. intros g (k & ->) _. by exists (S (S k)).
        -- apply (skn_ids2 W _ send_C); [by left|done|done].
        -- apply Forall_singleton, hcontractive_seq; [apply TermD_hc|done].
      * tstep.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

(** ** The closed program go

      go = let (re, re′) = ⟨receiveEval, receiveEval⟩ in
           let (c, s) = new ∗ in
           spawn (λu. let () = u in close (send ⟨∗, open (force re′ s)⟩));
           let (_, c′) = recv (send ⟨∗, select₁ (send ⟨∗, select₁ (select₂ (select₂
                           (send ⟨∗, select₁ (select₁ (select₂ c))⟩)))⟩)⟩) in
           close c′

    The spawned thread is computeService. The client sends Add (Const 5)
    (Mult (Const 7) (Const 9)) with ∗ for the constants and receives the
    result. The ends have type TermC;(?∗;Close) and TermD;(!∗;Close) at
    (a,0), the client acts at (a,0), …, (a,11), and z is the ceiling of
    receiveEval, in the world Wsum of TreeSum.v. *)

Definition as_srv : expr :=
  LetU (Var 0) (App (Lam (App EClos (App ESend (Pair EUnit (Var 0)))))
                    (App (App EForce (Var 3)) (Var 1))).

Definition as_cli : expr :=
  LetP (App ERecv (App ESend (Pair EUnit (App ESel1 (App ESend (Pair EUnit
          (App ESel1 (App ESel2 (App ESel2 (App ESend (Pair EUnit
            (App ESel1 (App ESel1 (App ESel2 (Var 1)))))))))))))))
    (LetU (Var 1) (App EClos (Var 0))).

Definition as_go : expr :=
  LetP (Pair reval reval) (LetP (App ENew EUnit) (LetU (App ESpawn (Lam as_srv)) as_cli)).

(** The client's continuation, the reply. *)
Definition as_Q : sty := SSeq (SRcv 0 TUnit) SEnd.

Lemma as_typed W : world_wf W → pt_known W (pc 0 0) → pt_known W (pc 1 0) →
  (∀ k, w_lt W (pc 0 k) (pc 1 0)) → typed W ∅ [] ∅ [] (∅, None) as_go TUnit.
Proof.
  intros HW Ha Hz Haz. unfold as_go.
  assert (hcontractive as_Q) as HQ by (apply hcontractive_seq; [apply hcontractive_rcv|apply hcontractive_end]).
  assert (hcontractive (SSeq TermC as_Q)) as HQ' by (apply hcontractive_seq; [apply TermC_hc|exact HQ]).
  tstep.
  { tstep; apply reval_typed, HW. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ (SSeq TermC as_Q) (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { (* computeService *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold as_srv. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (Some (pc 0 0)) 1 (BCs [pc 0 0; pc 1 0] after_P) (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pc 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pc 0 0)) 1 (BCs [pc 0 0; pc 1 0] after_P)
                  (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0)) _
                  (<[1:=Some (pc 1 0)]> (<[0:=Some (pc 1 0)]> ∅))
                  [(BCs [pc 0 0; pc 1 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0)); None; None; None; Some reval_ty; Some reval_ty]
                  (∅, Some 1) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      assert (∀ k, slt W [(BCs [pc 0 0; pc 1 0] after_P, [pv 0 0])] (pv 0 k) (pc 1 0)) as Hz'.
      { intros k. eapply (sl_hyp W _ [pc 0 0; pc 1 0] after_P [pv 0 0] (FLt (pv 0 k) (pv 2 0)));
          [by left|right; by exists k|fsc|reflexivity]. }
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 1)) (TSess SEnd (pv 0 1)));
        [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|]].
      + eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
                  (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0)))).
        * tstep; [|tstep]. tstep.
        * apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)). cbn. set_solver.
        * kscope.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 1 0). split; [done|]. right. apply (Hz' 0).
      + exists (pc 1 0). split; [done|]. right. apply (Hz' 1).
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 1 0)) None
                (TSess (SSeq TermD (SSeq (SSnd 0 TUnit) SEnd)) (pc 0 0)) RD); [reflexivity| | |].
      + unfold RD. rewrite <-(reval_inst (pc 0 0) (pc 1 0) (SSeq (SSnd 0 TUnit) SEnd)).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None reval_body [pc 0 0; pc 1 0] [SSeq (SSnd 0 TUnit) SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (k & ->) _. cbn. apply sl_w, Haz.
        * constructor; [by left|constructor; [by left|constructor]].
        * apply Forall_singleton, hcontractive_seq; [apply hcontractive_snd|apply hcontractive_end].
      + tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 1 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 0). split; [done|]. apply sle_refl, HW. }
  (* the client *)
  unfold as_cli. cbn. tstep.
  - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pc 0 10)) (TSess as_Q (pc 0 10)));
      [|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,9): Const 9 *)
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 0 9))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) as_Q) (pc 0 9))));
      [|apply (KTSend _ _ _ 0 TUnit as_Q (pc 0 9)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pc 0 8))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) as_Q) (SSeq OpC as_Q)) (pc 0 8)));
      [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,8): TermC;Q after the send of 7 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TermC as_Q) (pc 0 8))).
    { apply teq_steq. split; [done|apply TermC_seq]. }
    (* (a,7): Const 7 *)
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 0 7))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TermC as_Q)) (pc 0 7))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq TermC as_Q) (pc 0 7)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pc 0 6))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) (SSeq TermC as_Q)) (SSeq OpC (SSeq TermC as_Q))) (pc 0 6)));
      [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,6): TermC;(TermC;Q) after Mult *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TermC (SSeq TermC as_Q)) (pc 0 6))).
    { apply teq_steq. split; [done|apply TermC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pc 0 5))
              (TSess (SPlus (SSeq TermC (SSeq TermC as_Q)) (SSeq TermC (SSeq TermC as_Q))) (pc 0 5)));
      [|apply KTSel2|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq OpC as_Q) (pc 0 5))).
    { apply teq_steq. split; [done|by apply opC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pc 0 4))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) as_Q) (SSeq OpC as_Q)) (pc 0 4)));
      [|apply KTSel2|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,4): TermC;Q after the send of 5 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TermC as_Q) (pc 0 4))).
    { apply teq_steq. split; [done|apply TermC_seq]. }
    (* (a,3): Const 5 *)
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 0 3))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TermC as_Q)) (pc 0 3))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq TermC as_Q) (pc 0 3)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pc 0 2))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) (SSeq TermC as_Q)) (SSeq OpC (SSeq TermC as_Q))) (pc 0 2)));
      [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,2): TermC;(TermC;Q) after Add *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TermC (SSeq TermC as_Q)) (pc 0 2))).
    { apply teq_steq. split; [done|apply TermC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pc 0 1))
              (TSess (SPlus (SSeq TermC (SSeq TermC as_Q)) (SSeq TermC (SSeq TermC as_Q))) (pc 0 1)));
      [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq OpC as_Q) (pc 0 1))).
    { apply teq_steq. split; [done|by apply opC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pc 0 0))
              (TSess (SPlus (SSeq (SSnd 0 TUnit) as_Q) (SSeq OpC as_Q)) (pc 0 0)));
      [|apply KTSel2|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TermC_seq].
  - (* the result and close *)
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 0 11)) (TSess SEnd (pc 0 11)));
      [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
Qed.

Lemma as_deadlock_free : deadlock_free (∅, {[+ as_go +]}).
Proof.
  apply (soundness Wsum _ TUnit Wsum_strict).
  apply ptyped_closed; [constructor|]. apply as_typed; [apply Wsum_strict| | |].
  - unfold pt_known, Wsum. simpl. set_solver.
  - unfold pt_known, Wsum. simpl. set_solver.
  - intros k. apply glt_base. by exists k.
Qed.
