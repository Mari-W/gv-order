(** * Remote tree sum (Thiemann and Vasconcelos 2016, Listing 2, stage D)

      XformC = µX. ⊕(Skip, (!∗;(X;X));?∗)
      XformD = dual XformC = µX. &(Skip, (?∗;(X;X));!∗)

    [treeSum] serves XformD;β. On Node it receives the node value,
    recurses on both subtrees and sends the reply. The paper sends
    x+l+r. The calculus has no integers, so the value is ∗, and the
    result is the channel alone, not int ⊗ β. The client is the
    paper's transform specialised to aTree = Node 3 Leaf (Node 4 Leaf
    Leaf), a fixed sequence of selections, sends and receives, because
    the calculus has no tree values.

      treeSum : □(∀κ ζ β. C. ∗ ⊸^⊥_⊤ ((XformD;β)@κ ⊸^ζ_⊤ ∃κ′≽κ. C′. β@κ′))
      C  = {κ+k ≺ ζ ∣ k}      C′ = {κ ≺ κ′} ∪ {κ′+k ≺ ζ ∣ k}

    The type is the one of drain (TreeCopy.v) with XformD for TreeD.
    The left call instantiates β at XformD;(!∗;β), the right call at
    !∗;β. The reply comes after the right call, so the code opens its
    result at κ″, sends on the channel and packs at κ with the witness
    κ″+1. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.TreeCopy.

Set Default Proof Using "All".

Definition XformC : sty :=
  SMu (SPlus SSkip (SSeq (SSeq (SSnd 0 TUnit) (SSeq (SVar 0) (SVar 0))) (SRcv 0 TUnit))).

Definition XformD : sty :=
  SMu (SWith SSkip (SSeq (SSeq (SRcv 0 TUnit) (SSeq (SVar 0) (SVar 0))) (SSnd 0 TUnit))).

(** The node branches. *)
Definition XN : sty := SSeq (SSeq (SSnd 0 TUnit) (SSeq XformC XformC)) (SRcv 0 TUnit).
Definition XND : sty := SSeq (SSeq (SRcv 0 TUnit) (SSeq XformD XformD)) (SSnd 0 TUnit).

Lemma dual_XformC : dual XformC = XformD.
Proof. reflexivity. Qed.

Lemma unfoldS_XformC : unfoldS XformC = SPlus SSkip XN.
Proof. reflexivity. Qed.

Lemma unfoldS_XformD : unfoldS XformD = SWith SSkip XND.
Proof. reflexivity. Qed.

Lemma XformC_contractive : contractive XformC.
Proof. unfold contractive. by rewrite unfoldS_XformC. Qed.

Lemma XformD_contractive : contractive XformD.
Proof. unfold contractive. by rewrite unfoldS_XformD. Qed.

Lemma XformC_hc : hcontractive XformC.
Proof.
  apply (hc_ind (λ s, s = XformC)); [|done]. intros n s -> IH.
  specialize (IH XformC eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_XformC). cbn [view]. split; [apply hcontractive_skip|].
  apply ahc_seq; [apply ahc_seq; [apply hcontractive_snd|by apply ahc_seq]|apply hcontractive_rcv].
Qed.

Lemma XformD_hc : hcontractive XformD.
Proof.
  apply (hc_ind (λ s, s = XformD)); [|done]. intros n s -> IH.
  specialize (IH XformD eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_XformD). cbn [view]. split; [apply hcontractive_skip|].
  apply ahc_seq; [apply ahc_seq; [apply hcontractive_rcv|by apply ahc_seq]|apply hcontractive_snd].
Qed.

(** The heads of XformC;s and XformD;s. *)
Lemma XformC_seq s : seq (SSeq XformC s) (SPlus (SSeq SSkip s) (SSeq XN s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply XformC_contractive|by rewrite unfoldS_XformC].
  by rewrite unfoldS_XformC, unfoldS_plus.
Qed.

Lemma XformD_seq s : seq (SSeq XformD s) (SWith (SSeq SSkip s) (SSeq XND s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply XformD_contractive|by rewrite unfoldS_XformD].
  by rewrite unfoldS_XformD, unfoldS_with.
Qed.

(** The node branches reassociated, the reply after both subtrees. *)
Lemma xnode_snd s : hcontractive s →
  seq (SSeq XN s) (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC (SSeq (SRcv 0 TUnit) s)))).
Proof.
  intros Hs. unfold XN.
  eapply seq_trans; [apply seq_assoc|].
  1-3: auto using hcontractive_snd, hcontractive_rcv, hcontractive_seq, XformC_hc.
  eapply seq_trans; [apply seq_assoc|apply seq_snd_cong, seq_assoc];
    auto using hcontractive_snd, hcontractive_rcv, hcontractive_seq, XformC_hc.
Qed.

Lemma xnode_rcv s : hcontractive s →
  seq (SSeq XND s) (SSeq (SRcv 0 TUnit) (SSeq XformD (SSeq XformD (SSeq (SSnd 0 TUnit) s)))).
Proof.
  intros Hs. unfold XND.
  eapply seq_trans; [apply seq_assoc|].
  1-3: auto using hcontractive_snd, hcontractive_rcv, hcontractive_seq, XformD_hc.
  eapply seq_trans; [apply seq_assoc|apply seq_rcv_cong, seq_assoc];
    auto using hcontractive_snd, hcontractive_rcv, hcontractive_seq, XformD_hc.
Qed.

(** ** treeSum *)

Definition tsum_body : ty :=
  TLolli (Some (pv 1 0)) None (TSess (SSeq XformD (SVar 0)) (pv 0 0)) send_after.

Definition tsum_ty : ty := TBox 2 1 send_C (TLolli None None TUnit tsum_body).

Definition tsum : expr :=
  EBox (Lam (Case (App EBra (Var 0))
    (Var 0)
    (LetP (App ERecv (Var 0)) (LetU (Var 1)
      (App (Lam (App (Lam (App ESend (Pair EUnit (Var 0))))
                     (App (App EForce (Var 5)) (Var 0))))
           (App (App EForce (Var 4)) (Var 0))))))).

Lemma tsum_ty_pscoped : pscoped 0 tsum_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma tsum_inst x z s :
  sinst_ty (slist [s]) (ty_inst [x; z] tsum_body) =
  TLolli (Some z) None (TSess (SSeq XformD s) x)
    (TEx (Some x) 1 (BCs [x; z] after_P) (TSess s (pv 0 0))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma tsum_typed W F : world_wf W → typed W ∅ [] ∅ [] F tsum tsum_ty.
Proof.
  intros HW. unfold tsum, tsum_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  intros ss Hss Hhc. destruct ss as [|s [|]]; try discriminate Hss.
  rewrite Forall_singleton in Hhc. fold tsum_ty.
  change (lenv_pinst (pshift 2) [Some tsum_ty]) with [Some (pinst_ty (pshift 2) tsum_ty)].
  rewrite (pinst_closed _ tsum_ty) by apply tsum_ty_pscoped.
  cbn. fold XformD. change (bcs_inst (pshift 2) send_C) with send_C.
  assert (hcontractive (SSeq (SSnd 0 TUnit) s)) as Hhc1 by (apply hcontractive_seq; [apply hcontractive_snd|done]).
  assert (hcontractive (SSeq XformD (SSeq (SSnd 0 TUnit) s))) as Hhc2
    by (apply hcontractive_seq; [apply XformD_hc|done]).
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 0)) (TSess (SWith (SSeq SSkip s) (SSeq XND s)) (pv 0 0))).
    + eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply XformD_seq].
    + apply KTBra.
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0).
  - (* leaf *)
    cbn. apply (t_pack W _ _ _ _ _ _ (Some (pv 0 0)) 1 after_C (TSess s (pv 0 0)) [pv 0 1]).
    + done.
    + apply Forall_singleton. apply (skn_in W _ send_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done].
    + unfold after_C. apply bcs_hold_env. intros f [-> | (k & ->)] _; cbn.
      * apply (slt_po W _ (pv 0 0) HW).
      * hyp0 (pv 0 (S k)) (pv 1 0).
    + intros y Hy. mem_cases Hy. right. apply (slt_po W _ (pv 0 0) HW).
    + cbn. eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply skip_l].
  - (* node *)
    cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 1))
                (TSess (SSeq (SRcv 0 TUnit) (SSeq XformD (SSeq XformD (SSeq (SSnd 0 TUnit) s)))) (pv 0 1))).
      - eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply xnode_rcv].
      - apply KTRecv.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 1) (pv 1 0). }
    cbn. tstep; [tstep|]. cbn.
    set (R1 := TEx (Some (pv 0 2)) 1 (BCs [pv 0 2; pv 1 0] after_P)
                 (TSess (SSeq XformD (SSeq (SSnd 0 TUnit) s)) (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 1 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pv 0 2)) 1 (BCs [pv 0 2; pv 1 0] after_P)
                  (TSess (SSeq XformD (SSeq (SSnd 0 TUnit) s)) (pv 0 0)) _
                  (<[2:=Some (pv 2 0)]> (<[1:=Some (pv 2 0)]> (<[0:=None]> ∅)))
                  [(send_C, [pv 1 0; pv 2 0]); (BCs [pv 1 2; pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq XformD (SSeq (SSnd 0 TUnit) s)) (pv 0 0)); None; None; None; None; Some tsum_ty]
                  (∅, Some 2)
                  (TEx (Some (pv 1 0)) 1 (BCs [pv 1 0; pv 2 0] after_P) (TSess s (pv 0 0))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (R2 := TEx (Some (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P) (TSess (SSeq (SSnd 0 TUnit) s) (pv 0 0))).
      assert (∀ Ψ, (BCs [pv 1 2; pv 2 0] after_P, [pv 0 0]) ∈ Ψ → (send_C, [pv 1 0; pv 2 0]) ∈ Ψ →
                   Forall (skn W Ψ) [pv 0 0; pv 2 0]) as Hkn.
      { intros Ψ H1 H2. apply Forall_cons. split; [|apply Forall_singleton].
        - apply (skn_in W Ψ (BCs [pv 1 2; pv 2 0] after_P) [pv 0 0] (pv 0 0)); [exact H1|by left|done].
        - apply (skn_in W Ψ send_C [pv 1 0; pv 2 0] (pv 2 0)); [exact H2|by right; left|done]. }
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None R2); [reflexivity| | |].
      * eapply (tv_lam W HW _ _ _ _ _ R2 _ (Some (pv 2 0)) None 3); [set_solver|cbn; set_solver|].
        cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P)
                  (TSess (SSeq (SSnd 0 TUnit) s) (pv 0 0)) _
                  (<[3:=Some (pv 3 0)]> (<[2:=Some (pv 3 0)]> (<[1:=Some (pv 3 0)]> (<[0:=None]> ∅))))
                  [(send_C, [pv 2 0; pv 3 0]); (BCs [pv 2 2; pv 3 0] after_P, [pv 1 0]);
                   (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq (SSnd 0 TUnit) s) (pv 0 0)); None; None; None; None; None; Some tsum_ty]
                  (∅, Some 3)
                  (TEx (Some (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0))));
          [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
        set (Ψ2 := [(send_C, [pv 2 0; pv 3 0]); (BCs [pv 2 2; pv 3 0] after_P, [pv 1 0]);
                    (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]).
        assert (slt W Ψ2 (pv 2 0) (pv 0 0)) as Hch.
        { eapply sl_trans; [apply (slt_po W _ (pv 2 0) HW)|].
          eapply sl_trans; [apply (slt_po W _ (pv 2 1) HW)|].
          eapply sl_trans.
          - eapply (sl_hyp W _ [pv 2 2; pv 3 0] after_P [pv 1 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|by left|fsc|reflexivity].
          - eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|by left|fsc|reflexivity]. }
        assert (∀ k, slt W Ψ2 (pv 0 k) (pv 3 0)) as Hz.
        { intros k. eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 0 k) (pv 2 0)));
            [inlist|right; by exists k|fsc|reflexivity]. }
        (* the reply, then the pack at κ with the witness κ″+1 *)
        apply (t_pack W _ _ _ _ _ _ (Some (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0)) [pv 0 1]).
        -- done.
        -- apply Forall_singleton.
           apply (skn_in W _ (BCs [pv 1 0; pv 3 0] after_P) [pv 0 0] (pv 0 0)); [inlist|by left|done].
        -- apply bcs_hold_env. intros f [-> | (k & ->)] _; cbn.
           ++ eapply sl_trans; [exact Hch|apply (slt_po W _ (pv 0 0) HW)].
           ++ apply (Hz (S k)).
        -- intros y Hy. mem_cases Hy. right.
           eapply sl_trans; [exact Hch|apply (slt_po W _ (pv 0 0) HW)].
        -- cbn. eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
                         (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) s) (pv 0 0)))).
           ++ tstep; [|tstep]. tstep.
           ++ apply (KTSend _ _ _ 0 TUnit s (pv 0 0)). cbn. set_solver.
           ++ kscope.
           ++ apply ubs_intro; [intros y Hy; mem_cases Hy|].
              exists (pv 3 0). split; [done|]. right. apply (Hz 0).
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None
                  (TSess (SSeq XformD (SSeq (SSnd 0 TUnit) s)) (pv 0 0)) R2); [reflexivity| | |].
        -- unfold R2. rewrite <-(tsum_inst (pv 0 0) (pv 2 0) (SSeq (SSnd 0 TUnit) s)).
           apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pv 0 0; pv 2 0] [SSeq (SSnd 0 TUnit) s]);
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
                (TSess (SSeq XformD (SSeq XformD (SSeq (SSnd 0 TUnit) s))) (pv 0 2)) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(tsum_inst (pv 0 2) (pv 1 0) (SSeq XformD (SSeq (SSnd 0 TUnit) s))).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pv 0 2; pv 1 0]
                 [SSeq XformD (SSeq (SSnd 0 TUnit) s)]); [done|done| | |done| |apply ubs_none|tstep].
        -- apply bcs_hold_self; [by left|vb_list|]. intros g (k & ->) _. by exists (S (S k)).
        -- apply (skn_ids2 W _ send_C); [by left|done|done].
        -- by apply Forall_singleton.
      * tstep.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

(** ** The closed program go

      go = let (ts, ts′) = ⟨treeSum, treeSum⟩ in
           let (c, s) = new ∗ in
           spawn (λu. let () = u in close (open (force ts′ s)));
           let (_, c′) = recv (select₁ (select₁ (send ⟨∗, select₂ (select₁
                           (send ⟨∗, select₂ c⟩))⟩))) in
           let (_, c″) = recv c′ in close c″

    The client sends aTree = Node 3 Leaf (Node 4 Leaf Leaf) with ∗ for
    3 and 4 and receives the two replies, inner node first. Both ends
    have type XformC;Close and XformD;Close at (a,0), and z is the
    ceiling of treeSum. The client acts at (a,0), …, (a,9). The world
    has (a,k) ≺ (z,0) for every k. *)

Definition ts_srv : expr :=
  LetU (Var 0) (App (Lam (App EClos (Var 0))) (App (App EForce (Var 3)) (Var 1))).

Definition ts_cli : expr :=
  LetP (App ERecv (App ESel1 (App ESel1 (App ESend (Pair EUnit
          (App ESel2 (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 1)))))))))))
    (LetU (Var 1) (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Definition ts_go : expr :=
  LetP (Pair tsum tsum) (LetP (App ENew EUnit) (LetU (App ESpawn (Lam ts_srv)) ts_cli)).

(** The client's continuations after the left and the right reply. *)
Definition ts_Q1 : sty := SSeq (SRcv 0 TUnit) SEnd.
Definition ts_Q2 : sty := SSeq (SRcv 0 TUnit) ts_Q1.

Lemma ts_typed W : world_wf W → pt_known W (pc 0 0) → pt_known W (pc 1 0) →
  (∀ k, w_lt W (pc 0 k) (pc 1 0)) → typed W ∅ [] ∅ [] (∅, None) ts_go TUnit.
Proof.
  intros HW Ha Hz Haz. unfold ts_go.
  assert (hcontractive ts_Q1) as HQ1 by (apply hcontractive_seq; [apply hcontractive_rcv|apply hcontractive_end]).
  assert (hcontractive ts_Q2) as HQ2 by (apply hcontractive_seq; [apply hcontractive_rcv|exact HQ1]).
  tstep.
  { tstep; apply tsum_typed, HW. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ (SSeq XformC SEnd) (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { (* the server *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold ts_srv. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (Some (pc 0 0)) 1 (BCs [pc 0 0; pc 1 0] after_P) (TSess SEnd (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pc 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pc 0 0)) 1 (BCs [pc 0 0; pc 1 0] after_P)
                  (TSess SEnd (pv 0 0)) _
                  (<[1:=Some (pc 1 0)]> (<[0:=Some (pc 1 0)]> ∅))
                  [(BCs [pc 0 0; pc 1 0] after_P, [pv 0 0])]
                  [Some (TSess SEnd (pv 0 0)); None; None; None; Some tsum_ty; Some tsum_ty]
                  (∅, Some 1) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 0). split; [done|]. right.
      eapply (sl_hyp W _ [pc 0 0; pc 1 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
        [by left|right; by exists 0|fsc|reflexivity].
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 1 0)) None (TSess (SSeq XformD SEnd) (pc 0 0)) RD);
        [reflexivity| | |].
      + unfold RD. rewrite <-(tsum_inst (pc 0 0) (pc 1 0) SEnd).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pc 0 0; pc 1 0] [SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (k & ->) _. cbn. apply sl_w, Haz.
        * constructor; [by left|constructor; [by left|constructor]].
        * apply Forall_singleton, hcontractive_end.
      + tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 1 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 0). split; [done|]. apply sle_refl, HW. }
  (* the client *)
  unfold ts_cli. cbn. tstep.
  - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pc 0 7)) (TSess ts_Q2 (pc 0 7)));
      [|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,7): Skip;Q2 after select₁ *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip ts_Q2) (pc 0 7))).
    { apply teq_steq. split; [done|by apply skip_l]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pc 0 6))
              (TSess (SPlus (SSeq SSkip ts_Q2) (SSeq XN ts_Q2)) (pc 0 6)));
      [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,6): Skip;(XformC;Q2) after select₁, the left leaf of Node 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC ts_Q2)) (pc 0 6))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ2]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pc 0 5))
              (TSess (SPlus (SSeq SSkip (SSeq XformC ts_Q2)) (SSeq XN (SSeq XformC ts_Q2))) (pc 0 5)));
      [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,5): XformC;(XformC;Q2) after the send of 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC ts_Q2)) (pc 0 5))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 0 4))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC ts_Q2))) (pc 0 4))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC ts_Q2)) (pc 0 4)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    (* (a,4): XN;Q1 after select₂, Node 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN ts_Q1) (pc 0 4))).
    { apply teq_steq. split; [done|by apply xnode_snd]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pc 0 3)) (TSess (SPlus (SSeq SSkip ts_Q1) (SSeq XN ts_Q1)) (pc 0 3)));
      [|apply KTSel2|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,3): Skip;(XformC;Q1) after select₁, the leaf left of 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC ts_Q1)) (pc 0 3))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ1]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pc 0 2))
              (TSess (SPlus (SSeq SSkip (SSeq XformC ts_Q1)) (SSeq XN (SSeq XformC ts_Q1))) (pc 0 2)));
      [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* (a,2): XformC;(XformC;Q1) after the send of 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC ts_Q1)) (pc 0 2))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 0 1))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC ts_Q1))) (pc 0 1))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC ts_Q1)) (pc 0 1)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    (* (a,1): XN;Close after select₂, Node 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN SEnd) (pc 0 1))).
    { apply teq_steq. split; [done|apply xnode_snd, hcontractive_end]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pc 0 0)) (TSess (SPlus (SSeq SSkip SEnd) (SSeq XN SEnd)) (pc 0 0)));
      [|apply KTSel2|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply XformC_seq].
  - (* the two replies and close *)
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pc 0 8)) (TSess ts_Q1 (pc 0 8)));
        [tstep|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 0 9)) (TSess SEnd (pc 0 9)));
      [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
Qed.

(** The world: the instants of a below the ceiling z. *)
Definition sum_L (x y : point) : Prop := ∃ k, x = pc 0 k ∧ y = pc 1 0.

Definition Wsum : world := wgen (list_to_set (NConst <$> [0; 1])) (λ _ _, False) sum_L.

(** The ranks (0, k) for (a,k) and (1, k) for (z,k). *)
Definition sum_rank (x : point) : nat * nat :=
  match pt_root x with
  | NConst 1 => (1, pt_off x)
  | _ => (0, pt_off x)
  end.

Lemma Wsum_strict : strict Wsum.
Proof.
  apply (wgen_strict_lex _ _ _ id sum_rank); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y (k & -> & ->). right. rewrite !elem_of_list_to_set. cbn. set_solver.
  - intros x. unfold lexlt, sum_rank, pt_shift, pt_root. cbn.
    destruct (pn_root (pt_name x)) as [[|[|a]]| |]; cbn; right; split; try done; lia.
  - intros x y (k & -> & ->). unfold lexlt, sum_rank, id. cbn. lia.
Qed.

Lemma ts_deadlock_free : deadlock_free (∅, {[+ ts_go +]}).
Proof.
  apply (soundness Wsum _ TUnit Wsum_strict).
  apply ptyped_closed; [constructor|]. apply ts_typed; [apply Wsum_strict| | |].
  - unfold pt_known, Wsum. simpl. set_solver.
  - unfold pt_known, Wsum. simpl. set_solver.
  - intros k. apply glt_base. by exists k.
Qed.
