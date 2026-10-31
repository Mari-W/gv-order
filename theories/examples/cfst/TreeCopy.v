(** * Tree serialization over channels (Thiemann and Vasconcelos 2016, stage D)

      TreeC = µX. ⊕(Skip, !∗;X;X)       TreeD = dual TreeC = µX. &(Skip, ?∗;X;X)

    The calculus has no recursive data types, so the tree comes from a
    channel. [drain] is recvTree without the tree it builds: it reads
    a tree on one channel and discards it. It is also the binary tree
    channel of Mordido and Pérez (2026, p. 5) with one point per node.
    [copy] fuses recvTree and sendTree: it reads a tree on one channel
    and writes the same tree on another, recursing on both subtrees
    with polymorphic recursion in both continuations. The payload Int
    becomes ∗.

      drain : □(∀κ ζ β. C. ∗ ⊸^⊥_⊤ ((TreeD;β)@κ ⊸^ζ_⊤ ∃κ′≽κ. C′. β@κ′))
      C  = {κ·w ≺ ζ ∣ w}      C′ = {κ ≺ κ′} ∪ {κ′·w ≺ ζ ∣ w}

      copy : □(∀κ ι ζ β α. D. ∗ ⊸^⊥_⊤
               ((TreeD;β)@κ ⊗ (TreeC;α)@ι ⊸^ζ_⊤ ∃κ′ ι′≽κ. D′. β@κ′ ⊗ α@ι′))
      D  = {κ·w ≺ ι·w, ι·w ≺ (κ·w)·s, κ·w ≺ ζ, ι·w ≺ ζ ∣ w, s}
      D′ = {κ ≺ κ′} ∪ D[κ′, ι′, ζ]

    A walk w is a list of steps, each a successor or a branch root
    (K10), and κ·w is its end from κ. A branch moves κ to κ◁i and the
    select that copies it moves ι to ι◁i, so both channels take the
    same walk. Copy's zigzag relates the points of κ and ι at the same
    walk, and D[κ·u, ι·u] ⊆ D for every walk u. Before K10 the walks
    were the offsets κ+k. The main program runs a producer of the fixed
    tree Node(Leaf, Leaf) on channel a, copy from a to b, and drain
    on b. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.SendTreeType examples.cfst.CfstTools.

Set Default Proof Using "All".

Definition TreeD : sty :=
  SMu (SWith SSkip (SSeq (SRcv 0 TUnit) (SSeq (SVar 0) (SVar 0)))).

Lemma dual_TreeC : dual TreeC = TreeD.
Proof. reflexivity. Qed.

Lemma unfoldS_TreeC : unfoldS TreeC = SPlus SSkip (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)).
Proof. reflexivity. Qed.

Lemma unfoldS_TreeD : unfoldS TreeD = SWith SSkip (SSeq (SRcv 0 TUnit) (SSeq TreeD TreeD)).
Proof. reflexivity. Qed.

Lemma TreeC_contractive : contractive TreeC.
Proof. unfold contractive. by rewrite unfoldS_TreeC. Qed.

Lemma TreeD_contractive : contractive TreeD.
Proof. unfold contractive. by rewrite unfoldS_TreeD. Qed.

Lemma TreeC_hc : hcontractive TreeC.
Proof.
  apply (hc_ind (λ s, s = TreeC)); [|done]. intros n s -> IH.
  specialize (IH TreeC eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_TreeC). cbn [view]. split; [apply hcontractive_skip|].
  apply ahc_seq; [apply hcontractive_snd|by apply ahc_seq].
Qed.

Lemma TreeD_hc : hcontractive TreeD.
Proof.
  apply (hc_ind (λ s, s = TreeD)); [|done]. intros n s -> IH.
  specialize (IH TreeD eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_TreeD). cbn [view]. split; [apply hcontractive_skip|].
  apply ahc_seq; [apply hcontractive_rcv|by apply ahc_seq].
Qed.

(** The heads of TreeC;α and TreeD;β. *)
Lemma TreeC_seq s :
  seq (SSeq TreeC s) (SPlus (SSeq SSkip s) (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply TreeC_contractive|by rewrite unfoldS_TreeC].
  by rewrite unfoldS_TreeC, unfoldS_plus.
Qed.

Lemma TreeD_seq s :
  seq (SSeq TreeD s) (SWith (SSeq SSkip s) (SSeq (SSeq (SRcv 0 TUnit) (SSeq TreeD TreeD)) s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply TreeD_contractive|by rewrite unfoldS_TreeD].
  by rewrite unfoldS_TreeD, unfoldS_with.
Qed.

(** The node branch reassociated, as Thiemann and Vasconcelos do on p. 3. *)
Lemma node_rcv s : hcontractive s →
  seq (SSeq (SSeq (SRcv 0 TUnit) (SSeq TreeD TreeD)) s)
      (SSeq (SRcv 0 TUnit) (SSeq TreeD (SSeq TreeD s))).
Proof.
  intros Hs. eapply seq_trans; [apply seq_assoc|apply seq_rcv_cong, seq_assoc];
    auto using hcontractive_rcv, hcontractive_seq, TreeD_hc.
Qed.

Lemma node_snd s : hcontractive s →
  seq (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) s)
      (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC s))).
Proof.
  intros Hs. eapply seq_trans; [apply seq_assoc|apply seq_snd_cong, seq_assoc];
    auto using hcontractive_snd, hcontractive_seq, TreeC_hc.
Qed.

Lemma skip_l s : hcontractive s → seq (SSeq SSkip s) s.
Proof. intros Hs. by apply seq_skip_l, hcontractive_contractive. Qed.


(** ** drain *)

Definition drain_body : ty :=
  TLolli (Some (pv 1 0)) None (TSess (SSeq TreeD (SVar 0)) (pv 0 0)) send_after.

Definition drain_ty : ty := TBox 2 1 send_C (TLolli None None TUnit drain_body).

Definition drain : expr :=
  EBox (Lam (Case (App EBra (Var 0))
    (Var 0)
    (LetP (App ERecv (Var 0)) (LetU (Var 1)
      (App (Lam (App (Lam (Var 0)) (App (App EForce (Var 5)) (Var 0))))
           (App (App EForce (Var 4)) (Var 0))))))).

Lemma drain_ty_pscoped : pscoped 0 drain_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma drain_inst x z s :
  sinst_ty (slist [s]) (ty_inst [x; z] drain_body) =
  TLolli (Some z) None (TSess (SSeq TreeD s) x)
    (TEx (Some x) 1 (BCs [x; z] after_P) (TSess s (pv 0 0))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

(** A ≺ fact ι·w ≺ ζ of a hypothesis C = {ι·w ≺ ζ ∣ w}. *)
Ltac hypw w := eapply (sl_hyp0 _ _ send_P _ (pwalk (pv 0 0) w) (pv 1 0)); [inlist|by exists w|fscw|piw|piw].

Lemma drain_typed W F : world_wf W → typed W ∅ [] ∅ [] F drain drain_ty.
Proof.
  intros HW. unfold drain, drain_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  intros ss Hss Hhc. destruct ss as [|s [|]]; try discriminate Hss.
  rewrite Forall_singleton in Hhc. fold drain_ty.
  change (lenv_pinst (pshift 2) [Some drain_ty]) with [Some (pinst_ty (pshift 2) drain_ty)].
  rewrite (pinst_closed _ drain_ty) by apply drain_ty_pscoped.
  cbn. fold TreeD. change (bcs_inst (pshift 2) send_C) with send_C.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 0))
              (TSess (SWith (SSeq SSkip s) (SSeq (SSeq (SRcv 0 TUnit) (SSeq TreeD TreeD)) s)) (pv 0 0))).
    + eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TreeD_seq].
    + apply KTBra.
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hypw ([] : list (option bool)).
  - cbn. apply (t_pack W _ _ _ _ _ _ (Some (pv 0 0)) 1 after_C (TSess s (pv 0 0)) [pbr 0 0 false 0]).
    + done.
    + apply Forall_singleton. apply (skn_in W _ send_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done].
    + unfold after_C. apply bcs_hold_env. intros f [-> | (w & ->)] _; cbn [fact_map fact_holds].
      * apply (slt_br W _ (pv 0 0) false HW).
      * rewrite pwalk_inst. hypw (Some false :: w).
    + intros y Hy. mem_cases Hy. right. apply (slt_br W _ (pv 0 0) false HW).
    + cbn. eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply skip_l].
  - cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pbr 0 0 true 0))
                (TSess (SSeq (SRcv 0 TUnit) (SSeq TreeD (SSeq TreeD s))) (pbr 0 0 true 0))).
      - eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply node_rcv].
      - apply KTRecv.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. right. hypw [Some true]. }
    cbn. tstep; [tstep|]. cbn.
    set (R1 := TEx (Some (pbr 0 0 true 1)) 1 (BCs [pbr 0 0 true 1; pv 1 0] after_P) (TSess (SSeq TreeD s) (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 1 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pbr 0 0 true 1)) 1 (BCs [pbr 0 0 true 1; pv 1 0] after_P)
                  (TSess (SSeq TreeD s) (pv 0 0)) _
                  (<[2:=Some (pv 2 0)]> (<[1:=Some (pv 2 0)]> (<[0:=None]> ∅)))
                  [(send_C, [pv 1 0; pv 2 0]); (BCs [pbr 1 0 true 1; pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq TreeD s) (pv 0 0)); None; None; None; None; Some drain_ty]
                  (∅, Some 2)
                  (TEx (Some (pv 1 0)) 1 (BCs [pv 1 0; pv 2 0] after_P) (TSess s (pv 0 0))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (R2 := TEx (Some (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P) (TSess s (pv 0 0))).
      assert (∀ Ψ, (BCs [pbr 1 0 true 1; pv 2 0] after_P, [pv 0 0]) ∈ Ψ → (send_C, [pv 1 0; pv 2 0]) ∈ Ψ →
                   Forall (skn W Ψ) [pv 0 0; pv 2 0]) as Hkn.
      { intros Ψ H1 H2. apply Forall_cons. split; [|apply Forall_singleton].
        - apply (skn_in W Ψ (BCs [pbr 1 0 true 1; pv 2 0] after_P) [pv 0 0] (pv 0 0)); [exact H1|by left|done].
        - apply (skn_in W Ψ send_C [pv 1 0; pv 2 0] (pv 2 0)); [exact H2|by right; left|done]. }
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None R2); [reflexivity| | |].
      * eapply (tv_lam W HW _ _ _ _ _ R2 _ (Some (pv 2 0)) None 3); [set_solver|cbn; set_solver|].
        cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P)
                  (TSess s (pv 0 0)) _
                  (<[3:=Some (pv 3 0)]> (<[2:=Some (pv 3 0)]> (<[1:=Some (pv 3 0)]> (<[0:=None]> ∅))))
                  [(send_C, [pv 2 0; pv 3 0]); (BCs [pbr 2 0 true 1; pv 3 0] after_P, [pv 1 0]);
                   (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]
                  [Some (TSess s (pv 0 0)); None; None; None; None; None; Some drain_ty]
                  (∅, Some 3)
                  (TEx (Some (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0))));
          [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
        assert (slt W [(send_C, [pv 2 0; pv 3 0]); (BCs [pbr 2 0 true 1; pv 3 0] after_P, [pv 1 0]);
                       (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])] (pv 2 0) (pv 0 0)) as Hch.
        { eapply sl_trans; [apply (slt_br W _ (pv 2 0) true HW)|].
          eapply sl_trans; [apply (slt_po W _ (pbr 2 0 true 0) HW)|].
          eapply sl_trans.
          - eapply (sl_hyp W _ [pbr 2 0 true 1; pv 3 0] after_P [pv 1 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|by left|fsc|reflexivity].
          - eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|by left|fsc|reflexivity]. }
        apply (t_pack W _ _ _ _ _ _ (Some (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0)) [pv 0 0]).
        -- done.
        -- apply Forall_singleton.
           apply (skn_in W _ (BCs [pv 1 0; pv 3 0] after_P) [pv 0 0] (pv 0 0)); [inlist|by left|done].
        -- apply bcs_hold_env. intros f [-> | (w & ->)] _; cbn [fact_map fact_holds]; [exact Hch|].
           eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pwalk (pv 0 0) w) (pv 2 0)));
             [inlist|right; by exists w|fscw|fmw].
        -- intros y Hy. mem_cases Hy. by right.
        -- cbn. tstep.
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq TreeD s) (pv 0 0)) R2);
          [reflexivity| | |].
        -- unfold R2. rewrite <-(drain_inst (pv 0 0) (pv 2 0) s).
           apply (typed_force W _ _ _ _ _ _ 2 1 send_C None drain_body [pv 0 0; pv 2 0] [s]);
             [done|done| | |done| |apply ubs_none|tstep].
           ++ apply bcs_hold_intro. intros g (w & ->) _. cbn [fact_map fact_holds].
              eapply (sl_hyp W _ [pbr 1 0 true 1; pv 2 0] after_P [pv 0 0] (FLt (pwalk (pv 0 0) w) (pv 2 0)));
                [inlist|right; by exists w|fscw|fmw].
           ++ apply Hkn; inlist.
           ++ by apply Forall_singleton.
        -- tstep.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy|].
           exists (pv 2 0). split; [done|]. apply sle_refl, HW.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. apply sle_refl, HW.
    + eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None
                (TSess (SSeq TreeD (SSeq TreeD s)) (pbr 0 0 true 1)) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(drain_inst (pbr 0 0 true 1) (pv 1 0) (SSeq TreeD s)).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None drain_body [pbr 0 0 true 1; pv 1 0] [SSeq TreeD s]);
          [done|done| | |done| |apply ubs_none|tstep].
        -- apply bcs_hold_self; [by left|vb_list|]. intros g (w & ->) _.
           exists (Some true :: None :: w). fmw.
        -- apply (skn_ids2 W _ send_C); [by left|done|done].
        -- apply Forall_singleton, hcontractive_seq; [apply TreeD_hc|done].
      * tstep.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

(** ** copy *)

(** D relates the points of κ and ι at the same walk w. The step s
    after ι·w is the next step of the input, a successor or a branch
    root (K10). *)
Definition copy_P (g : fact) : Prop :=
  ∃ w, g = FLt (pwalk (pv 0 0) w) (pwalk (pv 1 0) w) ∨
       (∃ s, g = FLt (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s)) ∨
       g = FLt (pwalk (pv 0 0) w) (pv 2 0) ∨ g = FLt (pwalk (pv 1 0) w) (pv 2 0).
Definition copy_C : bcs := BCs [] copy_P.

(** D′ under the binder of κ′ = 0 and ι′ = 1, with κ and ζ as 2 and 3. *)
Definition cafter_P (g : fact) : Prop :=
  g = FLt (pv 2 0) (pv 0 0) ∨
  ∃ w, g = FLt (pwalk (pv 0 0) w) (pwalk (pv 1 0) w) ∨
       (∃ s, g = FLt (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s)) ∨
       g = FLt (pwalk (pv 0 0) w) (pv 3 0) ∨ g = FLt (pwalk (pv 1 0) w) (pv 3 0).
Definition cafter_C : bcs := BCs [pv 0 0; pv 2 0] cafter_P.

Definition copy_res : ty :=
  TEx (Some (pv 0 0)) 2 cafter_C (TProd (TSess (SVar 0) (pv 0 0)) (TSess (SVar 1) (pv 1 0))).

Definition copy_body : ty :=
  TLolli (Some (pv 2 0)) None
    (TProd (TSess (SSeq TreeD (SVar 0)) (pv 0 0)) (TSess (SSeq TreeC (SVar 1)) (pv 1 0))) copy_res.

Definition copy_ty : ty := TBox 3 2 copy_C (TLolli None None TUnit copy_body).

Definition copy : expr :=
  EBox (Lam (LetP (Var 0)
    (Case (App EBra (Var 1))
      (Pair (Var 0) (App ESel1 (Var 1)))
      (LetP (Pair (App ESel2 (Var 1)) (App ERecv (Var 0)))
        (LetP (Var 0)
          (App (Lam (App (Lam (Var 0)) (App (App EForce (Var 9)) (Var 0))))
               (App (App EForce (Var 8)) (Pair (Var 0) (App ESend (Pair (Var 1) (Var 3))))))))))).

Lemma copy_ty_pscoped : pscoped 0 copy_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma copy_inst x y z sb sa :
  sinst_ty (slist [sb; sa]) (ty_inst [x; y; z] copy_body) =
  TLolli (Some z) None (TProd (TSess (SSeq TreeD sb) x) (TSess (SSeq TreeC sa) y))
    (TEx (Some x) 2 (BCs [x; z] cafter_P) (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)))).
Proof.
  destruct x as [p o], y as [p' o'], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma copy_typed W F : world_wf W → typed W ∅ [] ∅ [] F copy copy_ty.
Proof.
  intros HW. unfold copy, copy_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  intros ss Hss Hhc. destruct ss as [|sb [|sa [|]]]; try discriminate Hss.
  apply Forall_cons in Hhc as [Hb Hhc]. rewrite Forall_singleton in Hhc. rename Hhc into Ha.
  fold copy_ty.
  change (lenv_pinst (pshift 3) [Some copy_ty]) with [Some (pinst_ty (pshift 3) copy_ty)].
  rewrite (pinst_closed _ copy_ty) by apply copy_ty_pscoped.
  cbn. fold TreeD. change (bcs_inst (pshift 3) copy_C) with copy_C.
  assert (∀ Ψ w s, (copy_C, [pv 0 0; pv 1 0; pv 2 0]) ∈ Ψ →
    slt W Ψ (pwalk (pv 0 0) w) (pwalk (pv 1 0) w) ∧
    slt W Ψ (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s) ∧
    slt W Ψ (pwalk (pv 0 0) w) (pv 2 0) ∧ slt W Ψ (pwalk (pv 1 0) w) (pv 2 0)) as Hc.
  { intros Ψ w s Hg. split_and!.
    - eapply (sl_hyp0 W Ψ copy_P [pv 0 0; pv 1 0; pv 2 0] (pwalk (pv 0 0) w) (pwalk (pv 1 0) w));
        [done|exists w; by left|fscw|piw|piw].
    - eapply (sl_hyp0 W Ψ copy_P [pv 0 0; pv 1 0; pv 2 0] (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s));
        [done|exists w; right; left; by exists s|fscw|piw|piw].
    - eapply (sl_hyp0 W Ψ copy_P [pv 0 0; pv 1 0; pv 2 0] (pwalk (pv 0 0) w) (pv 2 0));
        [done|exists w; by right; right; left|fscw|piw|piw].
    - eapply (sl_hyp0 W Ψ copy_P [pv 0 0; pv 1 0; pv 2 0] (pwalk (pv 1 0) w) (pv 2 0));
        [done|exists w; by right; right; right|fscw|piw|piw]. }
  pose proof (λ w s, Hc [(copy_C, [pv 0 0; pv 1 0; pv 2 0])] w s ltac:(by left)) as H0.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 0))
              (TSess (SWith (SSeq SSkip sb) (SSeq (SSeq (SRcv 0 TUnit) (SSeq TreeD TreeD)) sb)) (pv 0 0))).
    + eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TreeD_seq].
    + apply KTBra.
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [] None)|].
      exists (pv 2 0). split; [done|]. right. apply (H0 [] None).
  - (* leaf *)
    cbn. apply (t_pack W _ _ _ _ _ _ (Some (pv 0 0)) 2 cafter_C
                 (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0))) [pbr 0 0 false 0; pbr 1 0 false 0]).
    + done.
    + apply Forall_cons. split; [|apply Forall_singleton].
      * apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 0 0)); [by left|by left|done].
      * apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 1 0)); [by left|by right; left|done].
    + unfold cafter_C. apply bcs_hold_env.
      intros f [-> | (w & [-> | [(s & ->) | [-> | ->]]])] _; cbn [fact_map fact_holds];
        rewrite ?wstep_inst, ?pwalk_inst.
      * apply (slt_br W _ (pv 0 0) false HW).
      * apply (H0 (Some false :: w) None).
      * apply (H0 (Some false :: w) s).
      * apply (H0 (Some false :: w) None).
      * apply (H0 (Some false :: w) None).
    + intros y Hy. mem_cases Hy; right; [apply (slt_br W _ (pv 0 0) false HW)|].
      apply (sl_trans _ _ _ (pv 1 0)); [apply (H0 [] None)|apply (slt_br W _ (pv 1 0) false HW)].
    + cbn. apply (t_conv W _ _ _ _ _ _ (TProd (TSess (SSeq SSkip sb) (pbr 0 0 false 0))
                                                (TSess (SSeq SSkip sa) (pbr 1 0 false 0)))).
      { apply teq_steq. split; split; [done|by apply skip_l|done|by apply skip_l]. }
      eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq SSkip sb) (pbr 0 0 false 0))); [reflexivity| |tstep].
      eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pv 1 0))
                (TSess (SPlus (SSeq SSkip sa) (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) sa)) (pv 1 0))).
      * eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TreeC_seq].
      * apply KTSel1.
      * done.
      * apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [] (Some false))|].
        exists (pv 2 0). split; [done|]. right. apply (H0 [] None).
  - (* node *)
    cbn. tstep.
    { set (S2c := SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC sa))).
      eapply (tv_pair W HW _ _ _ _ _ _ (TSess S2c (pbr 1 0 true 0))); [reflexivity| |].
      - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pbr 0 0 true 0))
                  (TSess (SSeq (SRcv 0 TUnit) (SSeq TreeD (SSeq TreeD sb))) (pbr 0 0 true 0))).
        + eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply node_rcv].
        + apply KTRecv.
        + kscope.
        + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [Some true] None)|].
          exists (pv 2 0). split; [done|]. right. apply (H0 [Some true] None).
      - eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 1 0)) (TSess (SPlus (SSeq SSkip sa) S2c) (pv 1 0))).
        + eapply t_conv; [|tstep]. apply teq_steq. split; [done|].
          eapply seq_trans; [apply TreeC_seq|]. apply seq_plus_cong; [apply seq_refl|by apply node_snd].
        + apply KTSel2.
        + done.
        + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [] (Some true))|].
          exists (pv 2 0). split; [done|]. right. apply (H0 [] None). }
    cbn. tstep; [tstep|]. cbn.
    set (R1 := TEx (Some (pbr 0 0 true 1)) 2 (BCs [pbr 0 0 true 1; pv 2 0] cafter_P)
                 (TProd (TSess (SSeq TreeD sb) (pv 0 0)) (TSess (SSeq TreeC sa) (pv 1 0)))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 2 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pbr 0 0 true 1)) 2 (BCs [pbr 0 0 true 1; pv 2 0] cafter_P)
                  (TProd (TSess (SSeq TreeD sb) (pv 0 0)) (TSess (SSeq TreeC sa) (pv 1 0))) _
                  (<[2:=Some (pv 4 0)]> (<[1:=Some (pv 4 0)]> (<[0:=None]> ∅)))
                  [(copy_C, [pv 2 0; pv 3 0; pv 4 0]); (BCs [pbr 2 0 true 1; pv 4 0] cafter_P, [pv 0 0; pv 1 0])]
                  [Some (TProd (TSess (SSeq TreeD sb) (pv 0 0)) (TSess (SSeq TreeC sa) (pv 1 0)));
                   None; None; None; None; None; None; None; None; Some copy_ty]
                  (∅, Some 2)
                  (TEx (Some (pv 2 0)) 2 (BCs [pv 2 0; pv 4 0] cafter_P)
                     (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (Ψ1 := [(copy_C, [pv 2 0; pv 3 0; pv 4 0]); (BCs [pbr 2 0 true 1; pv 4 0] cafter_P, [pv 0 0; pv 1 0])]).
      assert (∀ Ψ w s, (BCs [pbr 2 0 true 1; pv 4 0] cafter_P, [pv 0 0; pv 1 0]) ∈ Ψ →
        slt W Ψ (pwalk (pv 0 0) w) (pwalk (pv 1 0) w) ∧
        slt W Ψ (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s) ∧
        slt W Ψ (pwalk (pv 0 0) w) (pv 4 0) ∧ slt W Ψ (pwalk (pv 1 0) w) (pv 4 0) ∧
        slt W Ψ (pbr 2 0 true 1) (pv 0 0)) as H1.
      { intros Ψ w s Hg. split_and!.
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pwalk (pv 0 0) w) (pwalk (pv 1 0) w)));
            [exact Hg|right; exists w; by left|fscw|fmw].
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s)));
            [exact Hg|right; exists w; right; left; by exists s|fscw|fmw].
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pwalk (pv 0 0) w) (pv 3 0)));
            [exact Hg|right; exists w; by right; right; left|fscw|fmw].
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pwalk (pv 1 0) w) (pv 3 0)));
            [exact Hg|right; exists w; by right; right; right|fscw|fmw].
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pv 2 0) (pv 0 0))); [exact Hg|by left|fsc|reflexivity]. }
      set (R2 := TEx (Some (pv 0 0)) 2 (BCs [pv 0 0; pv 4 0] cafter_P)
                   (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)))).
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 4 0)) None R2); [reflexivity| | |].
      * eapply (tv_lam W HW _ _ _ _ _ R2 _ (Some (pv 4 0)) None 3); [set_solver|cbn; set_solver|].
        cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pv 0 0)) 2 (BCs [pv 0 0; pv 4 0] cafter_P)
                  (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0))) _
                  (<[3:=Some (pv 6 0)]> (<[2:=Some (pv 6 0)]> (<[1:=Some (pv 6 0)]> (<[0:=None]> ∅))))
                  [(copy_C, [pv 4 0; pv 5 0; pv 6 0]); (BCs [pbr 4 0 true 1; pv 6 0] cafter_P, [pv 2 0; pv 3 0]);
                   (BCs [pv 2 0; pv 6 0] cafter_P, [pv 0 0; pv 1 0])]
                  [Some (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)));
                   None; None; None; None; None; None; None; None; None; Some copy_ty]
                  (∅, Some 3)
                  (TEx (Some (pv 4 0)) 2 (BCs [pv 4 0; pv 6 0] cafter_P)
                     (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)))));
          [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
        set (Ψ2 := [(copy_C, [pv 4 0; pv 5 0; pv 6 0]); (BCs [pbr 4 0 true 1; pv 6 0] cafter_P, [pv 2 0; pv 3 0]);
                   (BCs [pv 2 0; pv 6 0] cafter_P, [pv 0 0; pv 1 0])]).
        assert (∀ w s, (BCs [pv 2 0; pv 6 0] cafter_P, [pv 0 0; pv 1 0]) ∈ Ψ2 →
          slt W Ψ2 (pwalk (pv 0 0) w) (pwalk (pv 1 0) w) ∧
          slt W Ψ2 (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s) ∧
          slt W Ψ2 (pwalk (pv 0 0) w) (pv 6 0) ∧ slt W Ψ2 (pwalk (pv 1 0) w) (pv 6 0) ∧
          slt W Ψ2 (pv 2 0) (pv 0 0)) as H3.
        { intros w s Hg. split_and!.
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pwalk (pv 0 0) w) (pwalk (pv 1 0) w)));
              [exact Hg|right; exists w; by left|fscw|fmw].
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s)));
              [exact Hg|right; exists w; right; left; by exists s|fscw|fmw].
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pwalk (pv 0 0) w) (pv 3 0)));
              [exact Hg|right; exists w; by right; right; left|fscw|fmw].
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pwalk (pv 1 0) w) (pv 3 0)));
              [exact Hg|right; exists w; by right; right; right|fscw|fmw].
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pv 2 0) (pv 0 0))); [exact Hg|by left|fsc|reflexivity]. }
        pose proof (λ w s, H3 w s ltac:(inlist)) as H3'. clear H3.
        assert (slt W Ψ2 (pv 4 0) (pv 0 0)) as Hch.
        { eapply sl_trans; [apply (slt_br W _ (pv 4 0) true HW)|].
          eapply sl_trans; [apply (slt_po W _ (pbr 4 0 true 0) HW)|].
          apply (sl_trans _ _ _ (pv 2 0)); [|apply (H3' [] None)].
          eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pv 2 0) (pv 0 0))); [inlist|by left|fsc|reflexivity]. }
        apply (t_pack W _ _ _ _ _ _ (Some (pv 4 0)) 2 (BCs [pv 4 0; pv 6 0] cafter_P)
                 (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0))) [pv 0 0; pv 1 0]).
        -- done.
        -- apply Forall_cons. split; [|apply Forall_singleton].
           ++ apply (skn_in W _ (BCs [pv 2 0; pv 6 0] cafter_P) [pv 0 0; pv 1 0] (pv 0 0)); [inlist|by left|done].
           ++ apply (skn_in W _ (BCs [pv 2 0; pv 6 0] cafter_P) [pv 0 0; pv 1 0] (pv 1 0)); [inlist|by right; left|done].
        -- apply bcs_hold_env.
           intros f [-> | (w & [-> | [(s & ->) | [-> | ->]]])] _; cbn [fact_map fact_holds];
             rewrite ?wstep_inst, ?pwalk_inst; [exact Hch|apply (H3' w None)|apply (H3' w s)
             |apply (H3' w None)|apply (H3' w None)].
        -- intros y Hy. mem_cases Hy; right; [exact Hch|].
           apply (sl_trans _ _ _ (pv 0 0)); [exact Hch|apply (H3' [] None)].
        -- cbn. tstep.
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 4 0)) None
                  (TProd (TSess (SSeq TreeD sb) (pv 0 0)) (TSess (SSeq TreeC sa) (pv 1 0))) R2);
          [reflexivity| | |].
        -- unfold R2. rewrite <-(copy_inst (pv 0 0) (pv 1 0) (pv 4 0) sb sa).
           apply (typed_force W _ _ _ _ _ _ 3 2 copy_C None copy_body [pv 0 0; pv 1 0; pv 4 0] [sb; sa]);
             [done|done| | |done| |apply ubs_none|tstep].
           ++ apply bcs_hold_intro.
              intros g (w & [-> | [(s & ->) | [-> | ->]]]) _; cbn [fact_map fact_holds];
                rewrite ?wstep_inst, ?pwalk_inst;
                [apply (H1 Ψ1 w None)|apply (H1 Ψ1 w s)|apply (H1 Ψ1 w None)|apply (H1 Ψ1 w None)]; inlist.
           ++ apply Forall_cons. split; [|apply Forall_cons; split; [|apply Forall_singleton]].
              ** apply (skn_in W _ (BCs [pbr 2 0 true 1; pv 4 0] cafter_P) [pv 0 0; pv 1 0] (pv 0 0)); [inlist|by left|done].
              ** apply (skn_in W _ (BCs [pbr 2 0 true 1; pv 4 0] cafter_P) [pv 0 0; pv 1 0] (pv 1 0)); [inlist|by right; left|done].
              ** apply (skn_in W _ copy_C [pv 2 0; pv 3 0; pv 4 0] (pv 4 0)); [inlist|by right; right; left|done].
           ++ apply Forall_cons. split; [done|by apply Forall_singleton].
        -- tstep.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy|].
           exists (pv 4 0). split; [done|]. apply sle_refl, HW.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 4 0). split; [done|]. apply sle_refl, HW.
    + eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None
                (TProd (TSess (SSeq TreeD (SSeq TreeD sb)) (pbr 0 0 true 1))
                       (TSess (SSeq TreeC (SSeq TreeC sa)) (pbr 1 0 true 1))) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(copy_inst (pbr 0 0 true 1) (pbr 1 0 true 1) (pv 2 0) (SSeq TreeD sb) (SSeq TreeC sa)).
        apply (typed_force W _ _ _ _ _ _ 3 2 copy_C None copy_body [pbr 0 0 true 1; pbr 1 0 true 1; pv 2 0]
                 [SSeq TreeD sb; SSeq TreeC sa]); [done|done| | |done| |apply ubs_none|tstep].
        -- apply bcs_hold_self; [by left|vb_list|].
           intros g (w & [-> | [(s & ->) | [-> | ->]]]) _; exists (Some true :: None :: w);
             [left|right; left; exists s|right; right; left|right; right; right]; fmw.
        -- apply Forall_cons. split; [|apply Forall_cons; split; [|apply Forall_singleton]].
           ++ apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 0 0)); [by left|by left|done].
           ++ apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 1 0)); [by left|by right; left|done].
           ++ apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 2 0)); [by left|by right; right; left|done].
        -- apply Forall_cons. split; [|apply Forall_singleton];
             apply hcontractive_seq; auto using TreeD_hc, TreeC_hc.
      * eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq TreeD (SSeq TreeD sb)) (pbr 0 0 true 1))); [reflexivity| |tstep].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pbr 1 0 true 0))
                  (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC sa))) (pbr 1 0 true 0)))).
        -- tstep; [|tstep]. tstep.
        -- apply (KTSend _ _ _ 0 TUnit (SSeq TreeC (SSeq TreeC sa)) (pbr 1 0 true 0)). cbn. set_solver.
        -- kscope.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [Some true] None)|].
           exists (pv 2 0). split; [done|]. right. apply (H0 [Some true] None).
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. apply sle_refl, HW.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. apply sle_refl, HW.
Qed.

(** ** The closed program

      main = let (cp, dr) = ⟨copy, drain⟩ in
             let (a, a′) = new ∗ in let (b, b′) = new ∗ in
             spawn (λu. let () = u in close (open (force dr) b′));
             spawn (λu. let () = u in let (x, y) = open ((force cp) ⟨a′, b⟩) in
                         close x; close y);
             close (select₁ (select₁ (send ⟨∗, select₂ a⟩)))

    The producer sends Node(Leaf, Leaf) on a. Both channels have type
    TreeC;Close at the points (a,0) and (b,0), and z is the ceiling of
    both recursions. The world has a·w ≺ b·w ≺ (a·w)·s and
    a·w, b·w ≺ (z,0) for every walk w and step s. *)

Definition tm_cons : expr :=
  LetU (Var 0) (App (Lam (App EClos (Var 0))) (App (App EForce (Var 5)) (Var 1))).

Definition tm_copier : expr :=
  LetU (Var 0) (App (Lam (LetP (Var 0) (LetU (App EClos (Var 1)) (App EClos (Var 0)))))
                    (App (App EForce (Var 6)) (Pair (Var 3) (Var 2)))).

Definition tm_prod : expr :=
  App EClos (App ESel1 (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 3)))))).

Definition tree_main : expr :=
  LetP (Pair copy drain) (LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam tm_cons)) (LetU (App ESpawn (Lam tm_copier)) tm_prod)))).

Lemma tree_typed W : world_wf W →
  pt_known W (pc 0 0) → pt_known W (pc 1 0) → pt_known W (pc 2 0) →
  (∀ w, w_lt W (pwalk (pc 0 0) w) (pwalk (pc 1 0) w)) →
  (∀ w s, w_lt W (pwalk (pc 1 0) w) (wstep (pwalk (pc 0 0) w) s)) →
  (∀ w, w_lt W (pwalk (pc 0 0) w) (pc 2 0)) → (∀ w, w_lt W (pwalk (pc 1 0) w) (pc 2 0)) →
  typed W ∅ [] ∅ [] (∅, None) tree_main TUnit.
Proof.
  intros HW Ha Hb Hz Hab Hba Haz Hbz. unfold tree_main.
  assert (Forall (skn W []) [pc 0 0; pc 1 0; pc 2 0]) as HK.
  { constructor; [by left|constructor; [by left|constructor; [by left|constructor]]]. }
  tstep.
  { tstep; [apply drain_typed, HW|apply copy_typed, HW]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ (SSeq TreeC SEnd) (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ (SSeq TreeC SEnd) (pc 1 0) (or_introl Hb))|done|apply ubs_none]. }
  cbn. tstep.
  { (* the consumer *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 2 0)) (Some (pc 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold tm_cons. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (Some (pc 1 0)) 1 (BCs [pc 1 0; pc 2 0] after_P) (TSess SEnd (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 2 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pc 2 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pc 1 0)) 1 (BCs [pc 1 0; pc 2 0] after_P)
                  (TSess SEnd (pv 0 0)) _
                  (<[1:=Some (pc 2 0)]> (<[0:=Some (pc 2 0)]> ∅))
                  [(BCs [pc 1 0; pc 2 0] after_P, [pv 0 0])]
                  [Some (TSess SEnd (pv 0 0)); None; None; None; None; None; Some drain_ty; Some copy_ty]
                  (∅, Some 1) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 2 0). split; [done|]. right.
      eapply (sl_hyp W _ [pc 1 0; pc 2 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
        [by left|right; by exists []|fsc|reflexivity].
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 2 0)) None (TSess (SSeq TreeD SEnd) (pc 1 0)) RD);
        [reflexivity| | |].
      + unfold RD. rewrite <-(drain_inst (pc 1 0) (pc 2 0) SEnd).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None drain_body [pc 1 0; pc 2 0] [SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & ->) _. cbn [fact_map fact_holds].
          rewrite pwalk_inst. apply sl_w, Hbz.
        * constructor; [by left|constructor; [by left|constructor]].
        * apply Forall_singleton, hcontractive_end.
      + tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 2 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 2 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { (* the copier *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 2 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply sl_w, (Hab [])]. }
    unfold tm_copier. cbn. tstep; [tstep|]. cbn.
    set (RC := TEx (Some (pc 0 0)) 2 (BCs [pc 0 0; pc 2 0] cafter_P)
                 (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0)))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 2 0)) None RC); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RC _ (Some (pc 2 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (Some (pc 0 0)) 2 (BCs [pc 0 0; pc 2 0] cafter_P)
                  (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0))) _
                  (<[1:=Some (pc 2 0)]> (<[0:=Some (pc 2 0)]> ∅))
                  [(BCs [pc 0 0; pc 2 0] cafter_P, [pv 0 0; pv 1 0])]
                  [Some (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0)));
                   None; None; None; None; None; Some drain_ty; Some copy_ty]
                  (∅, Some 1) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (Ψc := [(BCs [pc 0 0; pc 2 0] cafter_P, [pv 0 0; pv 1 0])]).
      assert (slt W Ψc (pv 0 0) (pv 1 0) ∧ slt W Ψc (pv 0 0) (pc 2 0) ∧ slt W Ψc (pv 1 0) (pc 2 0))
        as (H01 & H0z & H1z).
      { split_and!.
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 0 0) (pv 1 0))); [by left|right; exists []; by left|fsc|reflexivity].
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 0 0) (pv 3 0))); [by left|right; exists []; by right; right; left|fsc|reflexivity].
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 1 0) (pv 3 0))); [by left|right; exists []; by right; right; right|fsc|reflexivity]. }
      tstep; [tstep|]. cbn. tstep.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; exact H01|].
        exists (pc 2 0). split; [done|]. by right.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 0)) (TSess SEnd (pv 1 0))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 2 0). split; [done|]. by right.
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 2 0)) None
                (TProd (TSess (SSeq TreeD SEnd) (pc 0 0)) (TSess (SSeq TreeC SEnd) (pc 1 0))) RC);
        [reflexivity| | |].
      + unfold RC. rewrite <-(copy_inst (pc 0 0) (pc 1 0) (pc 2 0) SEnd SEnd).
        apply (typed_force W _ _ _ _ _ _ 3 2 copy_C None copy_body [pc 0 0; pc 1 0; pc 2 0] [SEnd; SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & [-> | [(s & ->) | [-> | ->]]]) _; cbn [fact_map fact_holds];
            rewrite ?wstep_inst, ?pwalk_inst; apply sl_w; [apply Hab|apply Hba|apply Haz|apply Hbz].
        * exact HK.
        * constructor; [apply hcontractive_end|constructor; [apply hcontractive_end|constructor]].
      + eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq TreeD SEnd) (pc 0 0))); [reflexivity|tstep|tstep].
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 2 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 2 0). split; [done|]. apply sle_refl, HW. }
  (* the producer: a◁2, a◁2+1, (a◁2+1)◁1 and its ◁1 *)
  unfold tm_prod. cbn.
  set (p1 := pwalk (pc 0 0) [Some true]).
  set (p2 := pwalk (pc 0 0) [Some true; None]).
  set (p3 := pwalk (pc 0 0) [Some true; None; Some false]).
  set (p4 := pwalk (pc 0 0) [Some true; None; Some false; Some false]).
  eapply (tv_appk W HW _ _ _ _ KClos _ (Some p4) (TSess SEnd p4));
    [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip SEnd) p4)).
  { apply teq_steq. split; [done|apply skip_l, hcontractive_end]. }
  eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some p3)
            (TSess (SPlus (SSeq SSkip SEnd) (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) SEnd)) p3));
    [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq TreeC SEnd)) p3)).
  { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply TreeC_seq].
    apply hcontractive_seq; [apply TreeC_hc|apply hcontractive_end]. }
  eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some p2)
            (TSess (SPlus (SSeq SSkip (SSeq TreeC SEnd))
                          (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) (SSeq TreeC SEnd))) p2));
    [|apply KTSel1|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TreeC (SSeq TreeC SEnd)) p2)).
  { apply teq_steq. split; [done|apply TreeC_seq]. }
  eapply (tv_appk W HW _ _ _ _ KSend _ (Some p1)
            (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC SEnd))) p1)));
    [|apply (KTSend _ _ _ 0 TUnit (SSeq TreeC (SSeq TreeC SEnd)) p1); cbn; set_solver
     |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  tstep; [|tstep].
  eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pc 0 0))
            (TSess (SPlus (SSeq SSkip SEnd) (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC SEnd)))) (pc 0 0)));
    [|apply KTSel2|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  eapply t_conv; [|tstep]. apply teq_steq. split; [done|].
  eapply seq_trans; [apply TreeC_seq|]. apply seq_plus_cong; [apply seq_refl|apply node_snd, hcontractive_end].
Qed.

(** The world: the zigzag of copy along every walk on a = 0 and b = 1,
    and the ceiling z = 2. The rank of a point is its size, the number
    of steps from its root ([pt_size]), doubled on a and doubled plus
    one on b. *)
Definition copy_L (x y : point) : Prop :=
  ∃ w, (x = pwalk (pc 0 0) w ∧ y = pwalk (pc 1 0) w) ∨
       (∃ s, x = pwalk (pc 1 0) w ∧ y = wstep (pwalk (pc 0 0) w) s) ∨
       (x = pwalk (pc 0 0) w ∧ y = pc 2 0) ∨ (x = pwalk (pc 1 0) w ∧ y = pc 2 0).

Definition Wcopy : world := wgen (list_to_set (NConst <$> [0; 1; 2])) (λ _ _, False) copy_L.

Definition copy_rank (x : point) : nat * nat :=
  match pt_root x with
  | NConst 2 => (1, pt_size x)
  | NConst 1 => (0, 2 * pt_size x + 1)
  | _ => (0, 2 * pt_size x)
  end.

Lemma copy_rank_step x y :
  pt_root y = pt_root x → pt_size y = S (pt_size x) → lexlt (copy_rank x) (copy_rank y).
Proof.
  intros Hr Hs. unfold lexlt, copy_rank. rewrite Hr, Hs.
  destruct (pt_root x) as [[|[|[|a]]]| | |]; cbn; right; split; try done; lia.
Qed.

Lemma Wcopy_strict : strict Wcopy.
Proof.
  apply (wgen_strict_br lexlt _ _ _ id copy_rank); try done.
  - intros a. unfold lexlt. lia.
  - intros a b c. unfold lexlt. lia.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y (w & [[-> ->]|[(s & -> & ->)|[[-> ->]|[-> ->]]]]); right;
      rewrite ?wstep_root, ?pwalk_root; rewrite !elem_of_list_to_set; cbn; set_solver.
  - intros x y i. unfold id. by intros ->.
  - intros x y i. unfold id. by intros ->.
  - intros x. apply copy_rank_step; [done|unfold pt_size, pt_shift; simpl; lia].
  - intros x i. apply copy_rank_step; [done|unfold pt_size, pt_br; simpl; lia].
  - intros x y (w & [[-> ->]|[(s & -> & ->)|[[-> ->]|[-> ->]]]]); unfold lexlt, copy_rank, id;
      rewrite ?wstep_root, ?pwalk_root, ?wstep_size, ?pwalk_size; cbn; lia.
Qed.

Lemma tree_deadlock_free : deadlock_free (∅, {[+ tree_main +]}).
Proof.
  apply (soundness Wcopy _ TUnit Wcopy_strict).
  apply ptyped_closed; [constructor|]. apply tree_typed; [apply Wcopy_strict| | | | | | |].
  - unfold pt_known, Wcopy. simpl. set_solver.
  - unfold pt_known, Wcopy. simpl. set_solver.
  - unfold pt_known, Wcopy. simpl. set_solver.
  - intros w. apply glt_base. exists w. by left.
  - intros w s. apply glt_base. exists w. right; left. by exists s.
  - intros w. apply glt_base. exists w. by right; right; left.
  - intros w. apply glt_base. exists w. by right; right; right.
Qed.
