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

      treeSum : □(∀κ ζ β. C. ∗ ⊸ ((XformD;β)@κ ⊸^ζ ∃κ′≽κ. C′. β@κ′))
      C  = {κ·w ≺ ζ, κ·w ≺ (κ·w)[i] ∣ w, i}
      C′ = {κ ≺ κ′} ∪ C[κ′/κ]

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
    (TEx (LPt x) 1 (BCs [x; z] after_P) (TSess s (pv 0 0))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma tsum_typed W F : world_wf W → typed W ∅ [] ∅ [] F tsum tsum_ty.
Proof.
  intros HW. unfold tsum, tsum_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
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
    + apply KTBra; [hypb ([] : list (option bool)) false|hypb ([] : list (option bool)) true].
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hypw ([] : list (option bool)).
  - (* leaf *)
    cbn. apply (t_pack W _ _ _ _ _ _ (LPt (pv 0 0)) 1 after_C (TSess s (pv 0 0)) [psl 0 false 0]).
    + done.
    + apply Forall_singleton. apply (skn_in W _ send_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done].
    + unfold after_C. apply bcs_hold_env. intros f [-> | (w & [-> | (i & ->)])] _;
        cbn [fact_map fact_holds]; rewrite ?wstep_inst, ?pwalk_inst.
      * hypb ([] : list (option bool)) false.
      * hypw (Some false :: w).
      * hypb (Some false :: w) i.
    + split; [|done]. intros y Hy. mem_cases Hy. right. hypb ([] : list (option bool)) false.
    + cbn. eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply skip_l].
  - (* node *)
    cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (psl 0 true 0))
                (TSess (SSeq (SRcv 0 TUnit) (SSeq XformD (SSeq XformD (SSeq (SSnd 0 TUnit) s)))) (psl 0 true 0))).
      - eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply xnode_rcv].
      - apply KTRecv.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. right. hypw [Some true]. }
    cbn. tstep; [tstep|]. cbn.
    set (R1 := TEx (LPt (psl 0 true 1)) 1 (BCs [psl 0 true 1; pv 1 0] after_P)
                 (TSess (SSeq XformD (SSeq (SSnd 0 TUnit) s)) (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 1 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (psl 0 true 1)) 1 (BCs [psl 0 true 1; pv 1 0] after_P)
                  (TSess (SSeq XformD (SSeq (SSnd 0 TUnit) s)) (pv 0 0)) _
                  (<[2:=Some (pv 2 0)]> (<[1:=Some (pv 2 0)]> (<[0:=None]> ∅)))
                  [(send_C, [pv 1 0; pv 2 0]); (BCs [psl 1 true 1; pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq XformD (SSeq (SSnd 0 TUnit) s)) (pv 0 0)); None; None; None; None; Some tsum_ty]
                  (∅, Some (FVar 2))
                  (TEx (LPt (pv 1 0)) 1 (BCs [pv 1 0; pv 2 0] after_P) (TSess s (pv 0 0))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (R2 := TEx (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P) (TSess (SSeq (SSnd 0 TUnit) s) (pv 0 0))).
      assert (∀ Ψ, (BCs [psl 1 true 1; pv 2 0] after_P, [pv 0 0]) ∈ Ψ → (send_C, [pv 1 0; pv 2 0]) ∈ Ψ →
                   Forall (skn W Ψ) [pv 0 0; pv 2 0]) as Hkn.
      { intros Ψ H1 H2. apply Forall_cons. split; [|apply Forall_singleton].
        - apply (skn_in W Ψ (BCs [psl 1 true 1; pv 2 0] after_P) [pv 0 0] (pv 0 0)); [exact H1|by left|done].
        - apply (skn_in W Ψ send_C [pv 1 0; pv 2 0] (pv 2 0)); [exact H2|by right; left|done]. }
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None R2); [reflexivity| | |].
      * eapply (tv_lam W HW _ _ _ _ _ R2 _ (Some (pv 2 0)) None 3); [set_solver|cbn; set_solver|].
        cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P)
                  (TSess (SSeq (SSnd 0 TUnit) s) (pv 0 0)) _
                  (<[3:=Some (pv 3 0)]> (<[2:=Some (pv 3 0)]> (<[1:=Some (pv 3 0)]> (<[0:=None]> ∅))))
                  [(send_C, [pv 2 0; pv 3 0]); (BCs [psl 2 true 1; pv 3 0] after_P, [pv 1 0]);
                   (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq (SSnd 0 TUnit) s) (pv 0 0)); None; None; None; None; None; Some tsum_ty]
                  (∅, Some (FVar 3))
                  (TEx (LPt (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0))));
          [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
        set (Ψ2 := [(send_C, [pv 2 0; pv 3 0]); (BCs [psl 2 true 1; pv 3 0] after_P, [pv 1 0]);
                    (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]).
        assert (slt W Ψ2 (pv 2 0) (pv 0 0)) as Hch.
        { eapply sl_trans.
          { eapply (sl_hyp0 _ _ send_P _ (pv 0 0) (wstep (pv 0 0) (Some true)));
              [inlist|exists []; right; by exists true|fscw|reflexivity|reflexivity]. }
          eapply sl_trans; [apply (slt_po W _ (psl 2 true 0) HW)|].
          eapply sl_trans.
          - eapply (sl_hyp W _ [psl 2 true 1; pv 3 0] after_P [pv 1 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|by left|fsc|reflexivity].
          - eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|by left|fsc|reflexivity]. }
        assert (∀ w, slt W Ψ2 (pwalk (pv 0 0) w) (pv 3 0)) as Hz.
        { intros w. hypaw [pv 1 0; pv 3 0] [pv 0 0] w. }
        assert (∀ w i, slt W Ψ2 (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))) as Hzb.
        { intros w i. hypab [pv 1 0; pv 3 0] [pv 0 0] w i. }
        (* the reply, then the pack at κ with the witness κ″+1 *)
        apply (t_pack W _ _ _ _ _ _ (LPt (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0)) [pv 0 1]).
        -- done.
        -- apply Forall_singleton.
           apply (skn_in W _ (BCs [pv 1 0; pv 3 0] after_P) [pv 0 0] (pv 0 0)); [inlist|by left|done].
        -- apply bcs_hold_env. intros f [-> | (w & [-> | (i & ->)])] _;
             cbn [fact_map fact_holds]; rewrite ?wstep_inst, ?pwalk_inst.
           ++ eapply sl_trans; [exact Hch|apply (slt_po W _ (pv 0 0) HW)].
           ++ apply (Hz (None :: w)).
           ++ apply (Hzb (None :: w) i).
        -- split; [|done]. intros y Hy. mem_cases Hy. right.
           eapply sl_trans; [exact Hch|apply (slt_po W _ (pv 0 0) HW)].
        -- cbn. eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
                         (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) s) (pv 0 0)))).
           ++ tstep; [|tstep]. tstep.
           ++ apply (KTSend _ _ _ 0 TUnit s (pv 0 0)). cbn. set_solver.
           ++ kscope.
           ++ apply ubs_intro; [intros y Hy; mem_cases Hy|].
              exists (pv 3 0). split; [done|]. right. apply (Hz []).
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None
                  (TSess (SSeq XformD (SSeq (SSnd 0 TUnit) s)) (pv 0 0)) R2); [reflexivity| | |].
        -- unfold R2. rewrite <-(tsum_inst (pv 0 0) (pv 2 0) (SSeq (SSnd 0 TUnit) s)).
           apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pv 0 0; pv 2 0] [SSeq (SSnd 0 TUnit) s]);
             [done|done| | |done| |apply ubs_none|tstep].
           ++ apply bcs_hold_intro. intros g (w & [-> | (i & ->)]) _;
                cbn [fact_map fact_holds]; rewrite ?wstep_inst, ?pwalk_inst.
              ** hypaw [psl 1 true 1; pv 2 0] [pv 0 0] w.
              ** hypab [psl 1 true 1; pv 2 0] [pv 0 0] w i.
           ++ apply Hkn; inlist.
           ++ by apply Forall_singleton.
        -- tstep.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy|].
           exists (pv 2 0). split; [done|]. apply sle_refl, HW.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. apply sle_refl, HW.
    + eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None
                (TSess (SSeq XformD (SSeq XformD (SSeq (SSnd 0 TUnit) s))) (psl 0 true 1)) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(tsum_inst (psl 0 true 1) (pv 1 0) (SSeq XformD (SSeq (SSnd 0 TUnit) s))).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [psl 0 true 1; pv 1 0]
                 [SSeq XformD (SSeq (SSnd 0 TUnit) s)]); [done|done| | |done| |apply ubs_none|tstep].
        -- apply bcs_hold_self; [by left|vb_list|]. intros g (w & [-> | (i & ->)]) _;
             exists (Some true :: None :: w); [left|right; exists i]; fmw.
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
    have type XformC;Close and XformD;Close at the point α of c. The
    top-level point z, which no channel occupies, is the ceiling of
    treeSum. c is created with the facts of C at α and z ([tca_C] of
    TreeCopy.v), α·w ≺ z and α·w ≺ (α·w)[i] for every walk w and i. The
    client acts at the points [tsp k] of its walk from α, and each
    select at α·w moves it to (α·w)[i]. *)

(** The client's walk: select₂, send, select₁, select₂, send, select₁,
    select₁, recv, recv. *)
Definition ts_cw : list (option bool) :=
  [Some true; None; Some false; Some true; None; Some false; Some false; None; None].
Definition tsp (k : nat) : point := pwalk (pv 0 0) (take k ts_cw).

Definition ts_srv : expr :=
  LetU (Var 0) (App (Lam (App EClos (Var 0))) (App (App EForce (Var 3)) (Var 1))).

Definition ts_cli : expr :=
  LetP (App ERecv (App ESel1 (App ESel1 (App ESend (Pair EUnit
          (App ESel2 (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 1)))))))))))
    (LetU (Var 1) (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Definition ts_go : expr :=
  LetP (Pair tsum tsum) (let_new_pair (LetU (App ESpawn (Lam ts_srv)) ts_cli)).

Definition ts_Q1 : sty := SSeq (SRcv 0 TUnit) SEnd.
Definition ts_Q2 : sty := SSeq (SRcv 0 TUnit) ts_Q1.

(** After the [new] a is 0 and z is 1. *)
Lemma ts_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) ts_go TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold ts_go.
  assert (hcontractive ts_Q1) as HQ1 by (apply hcontractive_seq; [apply hcontractive_rcv|apply hcontractive_end]).
  assert (hcontractive ts_Q2) as HQ2 by (apply hcontractive_seq; [apply hcontractive_rcv|exact HQ1]).
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply tsum_typed, HW|exact HWs|apply tsum_typed, HW]. }
  cbn. apply (t_new_open W _ _ ∅ _ _ _ _ (SSeq XformC SEnd) tca_C); [apply tca_ok|..].
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  set (Ψ := [(top_C0, [pvar 1]); (BCs [pvar 1] send_P, [pvar 0])]).
  assert (∀ w, slt W Ψ (pwalk (pv 0 0) w) (pv 1 0)) as Haz.
  { intros w. eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0] (FLt (pwalk (pv 0 0) w) (pv 1 0)));
      [inlist|exists w; by left|fscw|fmw]. }
  assert (∀ w i, slt W Ψ (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))) as Haa.
  { intros w i. eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0]
                          (FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))));
      [inlist|exists w; right; by exists i|fscw|fmw]. }
  cbn. tstep.
  { (* the server *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold ts_srv. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 1 0] after_P) (TSess SEnd (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pv 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 1 0] after_P)
                  (TSess SEnd (pv 0 0)) _
                  (<[1:=Some (pv 2 0)]> (<[0:=Some (pv 2 0)]> ∅))
                  [(top_C0, [pvar 2]); (BCs [pvar 2] send_P, [pvar 1]); (BCs [pv 1 0; pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess SEnd (pv 0 0)); None; None; None; None; None; Some tsum_ty; Some tsum_ty]
                  (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. right.
      eapply (sl_hyp W _ [pv 1 0; pv 2 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
        [inlist|right; exists []; by left|fsc|reflexivity].
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None (TSess (SSeq XformD SEnd) (pv 0 0)) RD);
        [reflexivity| | |].
      + unfold RD. rewrite <-(tsum_inst (pv 0 0) (pv 1 0) SEnd).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None tsum_body [pv 0 0; pv 1 0] [SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & [-> | (i & ->)]) _; cbn [fact_map fact_holds];
            rewrite ?wstep_inst, ?pwalk_inst; [apply Haz|apply Haa].
        * constructor; [eapply skn_inst; [by right; left|by left|done]|].
          constructor; [eapply skn_inst; [by left|by left|done]|constructor].
        * apply Forall_singleton, hcontractive_end.
      + tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  (* the client *)
  unfold ts_cli. cbn. tstep.
  - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (tsp 7)) (TSess ts_Q2 (tsp 7)));
      [|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* tsp 7: Skip;Q2 after select₁ *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip ts_Q2) (tsp 7))).
    { apply teq_steq. split; [done|by apply skip_l]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (tsp 6))
              (TSess (SPlus (SSeq SSkip ts_Q2) (SSeq XN ts_Q2)) (tsp 6)));
      [|apply KTSel1, (Haa (take 6 ts_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* tsp 6: Skip;(XformC;Q2) after select₁, the left leaf of Node 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC ts_Q2)) (tsp 6))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ2]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (tsp 5))
              (TSess (SPlus (SSeq SSkip (SSeq XformC ts_Q2)) (SSeq XN (SSeq XformC ts_Q2))) (tsp 5)));
      [|apply KTSel1, (Haa (take 5 ts_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* tsp 5: XformC;(XformC;Q2) after the send of 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC ts_Q2)) (tsp 5))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (tsp 4))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC ts_Q2))) (tsp 4))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC ts_Q2)) (tsp 4)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    (* tsp 4: XN;Q1 after select₂, Node 4 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN ts_Q1) (tsp 4))).
    { apply teq_steq. split; [done|by apply xnode_snd]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (tsp 3)) (TSess (SPlus (SSeq SSkip ts_Q1) (SSeq XN ts_Q1)) (tsp 3)));
      [|apply KTSel2, (Haa (take 3 ts_cw) true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* tsp 3: Skip;(XformC;Q1) after select₁, the leaf left of 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq XformC ts_Q1)) (tsp 3))).
    { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply XformC_seq].
      apply hcontractive_seq; [apply XformC_hc|exact HQ1]. }
    eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (tsp 2))
              (TSess (SPlus (SSeq SSkip (SSeq XformC ts_Q1)) (SSeq XN (SSeq XformC ts_Q1))) (tsp 2)));
      [|apply KTSel1, (Haa (take 2 ts_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    (* tsp 2: XformC;(XformC;Q1) after the send of 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XformC (SSeq XformC ts_Q1)) (tsp 2))).
    { apply teq_steq. split; [done|apply XformC_seq]. }
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (tsp 1))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq XformC (SSeq XformC ts_Q1))) (tsp 1))));
      [|apply (KTSend _ _ _ 0 TUnit (SSeq XformC (SSeq XformC ts_Q1)) (tsp 1)); cbn; set_solver
       |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    tstep; [|tstep].
    (* tsp 1: XN;Close after select₂, Node 3 *)
    apply (t_conv W _ _ _ _ _ _ (TSess (SSeq XN SEnd) (tsp 1))).
    { apply teq_steq. split; [done|apply xnode_snd, hcontractive_end]. }
    eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 0 0)) (TSess (SPlus (SSeq SSkip SEnd) (SSeq XN SEnd)) (pv 0 0)));
      [|apply KTSel2, (Haa [] true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
    eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply XformC_seq].
  - (* the two replies and close *)
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (tsp 8)) (TSess ts_Q1 (tsp 8)));
        [tstep|apply KTRecv|kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (tsp 9)) (TSess SEnd (tsp 9)));
      [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
Qed.

Theorem ts_deadlock_free : deadlock_free (∅, {[+ ts_go +]}).
Proof. apply (soundness_source 1 top_C0 _ TUnit (c0_acyclic_creation _ _ top_acyclic)); [constructor|apply ts_typed]. Qed.
