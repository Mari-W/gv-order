(** * Tree serialization over channels (Thiemann and Vasconcelos 2016, stage D)

      TreeC = µX. ⊕(Skip, !∗;X;X)       TreeD = dual TreeC = µX. &(Skip, ?∗;X;X)

    The calculus has no recursive data types, so the tree comes from a
    channel. [drain] is recvTree without the tree it builds. It reads
    a tree on one channel and discards it. It is also the binary tree
    channel of Mordido and Pérez (2026, p. 5) with one point per node.
    [copy] fuses recvTree and sendTree. It reads a tree on one channel
    and writes the same tree on another, recursing on both subtrees
    with polymorphic recursion in both continuations. The payload Int
    becomes ∗.

      drain : □(∀κ ζ β. C. ∗ ⊸ ((TreeD;β)@κ ⊸^ζ ∃κ′≽κ. C′. β@κ′))
      C  = {κ·w ≺ ζ, κ·w ≺ (κ·w)[i] ∣ w, i}
      C′ = {κ ≺ κ′} ∪ C[κ′/κ]

      copy : □(∀κ ι ζ β α. D. ∗ ⊸
               ((TreeD;β)@κ ⊗ (TreeC;α)@ι ⊸^ζ ∃κ′ ι′≽κ. D′. β@κ′ ⊗ α@ι′))
      D  = {κ·w ≺ ι·w, ι·w ≺ (κ·w)·s, κ·w ≺ ζ, ι·w ≺ ζ ∣ w, s}
      D′ = {κ ≺ κ′} ∪ D[κ′, ι′, ζ]

    A walk w is a list of steps, each a successor or the point where a
    choice continues (K11), and κ·w is its end from κ. A branch moves κ
    to κ[i] and the select that copies it moves ι to ι[i], so both
    channels take the same walk. Copy's zigzag relates the points of κ
    and ι at the same walk, and D[κ·u, ι·u] ⊆ D for every walk u. The
    branch owes κ ≺ κ[i] and the select owes ι ≺ ι[i]. D derives both,
    κ ≺ ι ≺ κ[i] ≺ ι[i]. drain has no second channel, so its C states
    the facts a branch owes for every point of the walks from κ. The
    main program runs a producer of the fixed tree Node(Leaf, Leaf) on
    channel a, copy from a to b, and drain on b. *)

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

(** The point x[i]+k of a point variable x = a, where a choice at x
    continues (K11). *)
Abbreviation psl a i k := (Pt (NSlot (NVar a) 0 (bidx i)) k).

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
    (TEx (LPt x) 1 (BCs [x; z] after_P) (TSess s (pv 0 0))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

(** A ≺ fact ι·w ≺ ζ or ι·w ≺ (ι·w)[i] of a hypothesis C = send_C. *)
Ltac hypw w := eapply (sl_hyp0 _ _ send_P _ (pwalk (pv 0 0) w) (pv 1 0)); [inlist|exists w; by left|fscw|piw|piw].
Ltac hypb w i :=
  eapply (sl_hyp0 _ _ send_P _ (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i)));
    [inlist|exists w; right; by exists i|fscw|piw|piw].

(** The facts of a hypothesis C′ = after_C at the outer points env. *)
Ltac hypaw env xs w :=
  eapply (sl_hyp _ _ env after_P xs (FLt (pwalk (pv 0 0) w) (pv 2 0))); [inlist|right; exists w; by left|fscw|fmw].
Ltac hypab env xs w i :=
  eapply (sl_hyp _ _ env after_P xs (FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))));
    [inlist|right; exists w; right; by exists i|fscw|fmw].

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
    + apply KTBra; [hypb ([] : list (option bool)) false|hypb ([] : list (option bool)) true].
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hypw ([] : list (option bool)).
  - cbn. apply (t_pack W _ _ _ _ _ _ (LPt (pv 0 0)) 1 after_C (TSess s (pv 0 0)) [psl 0 false 0]).
    + done.
    + apply Forall_singleton. apply (skn_in W _ send_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done].
    + unfold after_C. apply bcs_hold_env. intros f [-> | (w & [-> | (i & ->)])] _;
        cbn [fact_map fact_holds]; rewrite ?wstep_inst, ?pwalk_inst.
      * hypb ([] : list (option bool)) false.
      * hypw (Some false :: w).
      * hypb (Some false :: w) i.
    + split; [|done]. intros y Hy. mem_cases Hy. right. hypb ([] : list (option bool)) false.
    + cbn. eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply skip_l].
  - cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (psl 0 true 0))
                (TSess (SSeq (SRcv 0 TUnit) (SSeq TreeD (SSeq TreeD s))) (psl 0 true 0))).
      - eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply node_rcv].
      - apply KTRecv.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. right. hypw [Some true]. }
    cbn. tstep; [tstep|]. cbn.
    set (R1 := TEx (LPt (psl 0 true 1)) 1 (BCs [psl 0 true 1; pv 1 0] after_P) (TSess (SSeq TreeD s) (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 1 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (psl 0 true 1)) 1 (BCs [psl 0 true 1; pv 1 0] after_P)
                  (TSess (SSeq TreeD s) (pv 0 0)) _
                  (<[2:=Some (pv 2 0)]> (<[1:=Some (pv 2 0)]> (<[0:=None]> ∅)))
                  [(send_C, [pv 1 0; pv 2 0]); (BCs [psl 1 true 1; pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess (SSeq TreeD s) (pv 0 0)); None; None; None; None; Some drain_ty]
                  (∅, Some (FVar 2))
                  (TEx (LPt (pv 1 0)) 1 (BCs [pv 1 0; pv 2 0] after_P) (TSess s (pv 0 0))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (R2 := TEx (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P) (TSess s (pv 0 0))).
      assert (∀ Ψ, (BCs [psl 1 true 1; pv 2 0] after_P, [pv 0 0]) ∈ Ψ → (send_C, [pv 1 0; pv 2 0]) ∈ Ψ →
                   Forall (skn W Ψ) [pv 0 0; pv 2 0]) as Hkn.
      { intros Ψ H1 H2. apply Forall_cons. split; [|apply Forall_singleton].
        - apply (skn_in W Ψ (BCs [psl 1 true 1; pv 2 0] after_P) [pv 0 0] (pv 0 0)); [exact H1|by left|done].
        - apply (skn_in W Ψ send_C [pv 1 0; pv 2 0] (pv 2 0)); [exact H2|by right; left|done]. }
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None R2); [reflexivity| | |].
      * eapply (tv_lam W HW _ _ _ _ _ R2 _ (Some (pv 2 0)) None 3); [set_solver|cbn; set_solver|].
        cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P)
                  (TSess s (pv 0 0)) _
                  (<[3:=Some (pv 3 0)]> (<[2:=Some (pv 3 0)]> (<[1:=Some (pv 3 0)]> (<[0:=None]> ∅))))
                  [(send_C, [pv 2 0; pv 3 0]); (BCs [psl 2 true 1; pv 3 0] after_P, [pv 1 0]);
                   (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]
                  [Some (TSess s (pv 0 0)); None; None; None; None; None; Some drain_ty]
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
        apply (t_pack W _ _ _ _ _ _ (LPt (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0)) [pv 0 0]).
        -- done.
        -- apply Forall_singleton.
           apply (skn_in W _ (BCs [pv 1 0; pv 3 0] after_P) [pv 0 0] (pv 0 0)); [inlist|by left|done].
        -- apply bcs_hold_env. intros f [-> | (w & [-> | (i & ->)])] _;
             cbn [fact_map fact_holds]; rewrite ?wstep_inst, ?pwalk_inst; [exact Hch| |].
           ++ hypaw [pv 1 0; pv 3 0] [pv 0 0] w.
           ++ hypab [pv 1 0; pv 3 0] [pv 0 0] w i.
        -- split; [|done]. intros y Hy. mem_cases Hy. by right.
        -- cbn. tstep.
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq TreeD s) (pv 0 0)) R2);
          [reflexivity| | |].
        -- unfold R2. rewrite <-(drain_inst (pv 0 0) (pv 2 0) s).
           apply (typed_force W _ _ _ _ _ _ 2 1 send_C None drain_body [pv 0 0; pv 2 0] [s]);
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
                (TSess (SSeq TreeD (SSeq TreeD s)) (psl 0 true 1)) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(drain_inst (psl 0 true 1) (pv 1 0) (SSeq TreeD s)).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None drain_body [psl 0 true 1; pv 1 0] [SSeq TreeD s]);
          [done|done| | |done| |apply ubs_none|tstep].
        -- apply bcs_hold_self; [by left|vb_list|]. intros g (w & [-> | (i & ->)]) _;
             exists (Some true :: None :: w); [left|right; exists i]; fmw.
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
    after ι·w is the next step of the input, a successor or the point
    where a choice continues. *)
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
  TEx (LPt (pv 0 0)) 2 cafter_C (TProd (TSess (SVar 0) (pv 0 0)) (TSess (SVar 1) (pv 1 0))).

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
    (TEx (LPt x) 2 (BCs [x; z] cafter_P) (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)))).
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
  (* the facts a choice owes, from the zigzag: κ ≺ ι ≺ κ[i] ≺ ι[i] *)
  set (Ψ0 := [(copy_C, [pv 0 0; pv 1 0; pv 2 0])]).
  assert (∀ i, slt W Ψ0 (pv 0 0) (wstep (pv 0 0) (Some i))) as Hκb.
  { intros i. eapply sl_trans; [exact (proj1 (H0 [] None))|exact (proj1 (proj2 (H0 [] (Some i))))]. }
  assert (∀ i, slt W Ψ0 (pv 1 0) (wstep (pv 1 0) (Some i))) as Hιb.
  { intros i. eapply sl_trans; [exact (proj1 (proj2 (H0 [] (Some i))))|exact (proj1 (H0 [Some i] None))]. }
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 0))
              (TSess (SWith (SSeq SSkip sb) (SSeq (SSeq (SRcv 0 TUnit) (SSeq TreeD TreeD)) sb)) (pv 0 0))).
    + eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TreeD_seq].
    + apply KTBra; [apply (Hκb false)|apply (Hκb true)].
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [] None)|].
      exists (pv 2 0). split; [done|]. right. apply (H0 [] None).
  - (* leaf *)
    cbn. apply (t_pack W _ _ _ _ _ _ (LPt (pv 0 0)) 2 cafter_C
                 (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0))) [psl 0 false 0; psl 1 false 0]).
    + done.
    + apply Forall_cons. split; [|apply Forall_singleton].
      * apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 0 0)); [by left|by left|done].
      * apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 1 0)); [by left|by right; left|done].
    + unfold cafter_C. apply bcs_hold_env.
      intros f [-> | (w & [-> | [(s & ->) | [-> | ->]]])] _; cbn [fact_map fact_holds];
        rewrite ?wstep_inst, ?pwalk_inst.
      * apply (Hκb false).
      * apply (H0 (Some false :: w) None).
      * apply (H0 (Some false :: w) s).
      * apply (H0 (Some false :: w) None).
      * apply (H0 (Some false :: w) None).
    + split; [|done]. intros y Hy. mem_cases Hy; right; [apply (Hκb false)|].
      apply (sl_trans _ _ _ (pv 1 0)); [exact (proj1 (H0 [] None))|apply (Hιb false)].
    + cbn. apply (t_conv W _ _ _ _ _ _ (TProd (TSess (SSeq SSkip sb) (psl 0 false 0))
                                                (TSess (SSeq SSkip sa) (psl 1 false 0)))).
      { apply teq_steq. split; split; [done|by apply skip_l|done|by apply skip_l]. }
      eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq SSkip sb) (psl 0 false 0))); [reflexivity| |tstep].
      eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pv 1 0))
                (TSess (SPlus (SSeq SSkip sa) (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) sa)) (pv 1 0))).
      * eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TreeC_seq].
      * apply KTSel1, (Hιb false).
      * done.
      * apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [] (Some false))|].
        exists (pv 2 0). split; [done|]. right. apply (H0 [] None).
  - (* node *)
    cbn. tstep.
    { set (S2c := SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC sa))).
      eapply (tv_pair W HW _ _ _ _ _ _ (TSess S2c (psl 1 true 0))); [reflexivity| |].
      - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (psl 0 true 0))
                  (TSess (SSeq (SRcv 0 TUnit) (SSeq TreeD (SSeq TreeD sb))) (psl 0 true 0))).
        + eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply node_rcv].
        + apply KTRecv.
        + kscope.
        + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [Some true] None)|].
          exists (pv 2 0). split; [done|]. right. apply (H0 [Some true] None).
      - eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 1 0)) (TSess (SPlus (SSeq SSkip sa) S2c) (pv 1 0))).
        + eapply t_conv; [|tstep]. apply teq_steq. split; [done|].
          eapply seq_trans; [apply TreeC_seq|]. apply seq_plus_cong; [apply seq_refl|by apply node_snd].
        + apply KTSel2, (Hιb true).
        + done.
        + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (H0 [] (Some true))|].
          exists (pv 2 0). split; [done|]. right. apply (H0 [] None). }
    cbn. tstep; [tstep|]. cbn.
    set (R1 := TEx (LPt (psl 0 true 1)) 2 (BCs [psl 0 true 1; pv 2 0] cafter_P)
                 (TProd (TSess (SSeq TreeD sb) (pv 0 0)) (TSess (SSeq TreeC sa) (pv 1 0)))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 2 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (psl 0 true 1)) 2 (BCs [psl 0 true 1; pv 2 0] cafter_P)
                  (TProd (TSess (SSeq TreeD sb) (pv 0 0)) (TSess (SSeq TreeC sa) (pv 1 0))) _
                  (<[2:=Some (pv 4 0)]> (<[1:=Some (pv 4 0)]> (<[0:=None]> ∅)))
                  [(copy_C, [pv 2 0; pv 3 0; pv 4 0]); (BCs [psl 2 true 1; pv 4 0] cafter_P, [pv 0 0; pv 1 0])]
                  [Some (TProd (TSess (SSeq TreeD sb) (pv 0 0)) (TSess (SSeq TreeC sa) (pv 1 0)));
                   None; None; None; None; None; None; None; None; Some copy_ty]
                  (∅, Some (FVar 2))
                  (TEx (LPt (pv 2 0)) 2 (BCs [pv 2 0; pv 4 0] cafter_P)
                     (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (Ψ1 := [(copy_C, [pv 2 0; pv 3 0; pv 4 0]); (BCs [psl 2 true 1; pv 4 0] cafter_P, [pv 0 0; pv 1 0])]).
      assert (∀ Ψ w s, (BCs [psl 2 true 1; pv 4 0] cafter_P, [pv 0 0; pv 1 0]) ∈ Ψ →
        slt W Ψ (pwalk (pv 0 0) w) (pwalk (pv 1 0) w) ∧
        slt W Ψ (pwalk (pv 1 0) w) (wstep (pwalk (pv 0 0) w) s) ∧
        slt W Ψ (pwalk (pv 0 0) w) (pv 4 0) ∧ slt W Ψ (pwalk (pv 1 0) w) (pv 4 0) ∧
        slt W Ψ (psl 2 true 1) (pv 0 0)) as H1.
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
      set (R2 := TEx (LPt (pv 0 0)) 2 (BCs [pv 0 0; pv 4 0] cafter_P)
                   (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)))).
      eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 4 0)) None R2); [reflexivity| | |].
      * eapply (tv_lam W HW _ _ _ _ _ R2 _ (Some (pv 4 0)) None 3); [set_solver|cbn; set_solver|].
        cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 0)) 2 (BCs [pv 0 0; pv 4 0] cafter_P)
                  (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0))) _
                  (<[3:=Some (pv 6 0)]> (<[2:=Some (pv 6 0)]> (<[1:=Some (pv 6 0)]> (<[0:=None]> ∅))))
                  [(copy_C, [pv 4 0; pv 5 0; pv 6 0]); (BCs [psl 4 true 1; pv 6 0] cafter_P, [pv 2 0; pv 3 0]);
                   (BCs [pv 2 0; pv 6 0] cafter_P, [pv 0 0; pv 1 0])]
                  [Some (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)));
                   None; None; None; None; None; None; None; None; None; Some copy_ty]
                  (∅, Some (FVar 3))
                  (TEx (LPt (pv 4 0)) 2 (BCs [pv 4 0; pv 6 0] cafter_P)
                     (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0)))));
          [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
        set (Ψ2 := [(copy_C, [pv 4 0; pv 5 0; pv 6 0]); (BCs [psl 4 true 1; pv 6 0] cafter_P, [pv 2 0; pv 3 0]);
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
        { eapply sl_trans.
          { eapply sl_trans.
            - eapply (sl_hyp0 W Ψ2 copy_P [pv 4 0; pv 5 0; pv 6 0] (pv 0 0) (pv 1 0));
                [inlist|exists []; by left|fsc|reflexivity|reflexivity].
            - eapply (sl_hyp0 W Ψ2 copy_P [pv 4 0; pv 5 0; pv 6 0] (pv 1 0) (wstep (pv 0 0) (Some true)));
                [inlist|exists []; right; left; by exists (Some true)|fscw|reflexivity|reflexivity]. }
          eapply sl_trans; [apply (slt_po W _ (psl 4 true 0) HW)|].
          apply (sl_trans _ _ _ (pv 2 0)); [|apply (H3' [] None)].
          eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pv 2 0) (pv 0 0))); [inlist|by left|fsc|reflexivity]. }
        apply (t_pack W _ _ _ _ _ _ (LPt (pv 4 0)) 2 (BCs [pv 4 0; pv 6 0] cafter_P)
                 (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0))) [pv 0 0; pv 1 0]).
        -- done.
        -- apply Forall_cons. split; [|apply Forall_singleton].
           ++ apply (skn_in W _ (BCs [pv 2 0; pv 6 0] cafter_P) [pv 0 0; pv 1 0] (pv 0 0)); [inlist|by left|done].
           ++ apply (skn_in W _ (BCs [pv 2 0; pv 6 0] cafter_P) [pv 0 0; pv 1 0] (pv 1 0)); [inlist|by right; left|done].
        -- apply bcs_hold_env.
           intros f [-> | (w & [-> | [(s & ->) | [-> | ->]]])] _; cbn [fact_map fact_holds];
             rewrite ?wstep_inst, ?pwalk_inst; [exact Hch|apply (H3' w None)|apply (H3' w s)
             |apply (H3' w None)|apply (H3' w None)].
        -- split; [|done]. intros y Hy. mem_cases Hy; right; [exact Hch|].
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
              ** apply (skn_in W _ (BCs [psl 2 true 1; pv 4 0] cafter_P) [pv 0 0; pv 1 0] (pv 0 0)); [inlist|by left|done].
              ** apply (skn_in W _ (BCs [psl 2 true 1; pv 4 0] cafter_P) [pv 0 0; pv 1 0] (pv 1 0)); [inlist|by right; left|done].
              ** apply (skn_in W _ copy_C [pv 2 0; pv 3 0; pv 4 0] (pv 4 0)); [inlist|by right; right; left|done].
           ++ apply Forall_cons. split; [done|by apply Forall_singleton].
        -- tstep.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy|].
           exists (pv 4 0). split; [done|]. apply sle_refl, HW.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 4 0). split; [done|]. apply sle_refl, HW.
    + eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None
                (TProd (TSess (SSeq TreeD (SSeq TreeD sb)) (psl 0 true 1))
                       (TSess (SSeq TreeC (SSeq TreeC sa)) (psl 1 true 1))) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(copy_inst (psl 0 true 1) (psl 1 true 1) (pv 2 0) (SSeq TreeD sb) (SSeq TreeC sa)).
        apply (typed_force W _ _ _ _ _ _ 3 2 copy_C None copy_body [psl 0 true 1; psl 1 true 1; pv 2 0]
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
      * eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq TreeD (SSeq TreeD sb)) (psl 0 true 1))); [reflexivity| |tstep].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some (psl 1 true 0))
                  (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC sa))) (psl 1 true 0)))).
        -- tstep; [|tstep]. tstep.
        -- apply (KTSend _ _ _ 0 TUnit (SSeq TreeC (SSeq TreeC sa)) (psl 1 true 0)). cbn. set_solver.
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
    TreeC;Close, and the top-level point z, which no channel occupies,
    is the ceiling of both recursions. Let α and β be the points of a
    and b. a is created with the facts of C at α and z ([tca_C]),
    α·w ≺ z and α·w ≺ (α·w)[i] for every walk w and i. b is created
    with the zigzag of copy, α·w ≺ β·w ≺ (α·w)·s and β·w ≺ z for every
    walk w and step s ([tcb_C]). The zigzag derives α·w ≺ α·w′ along
    every walk between outer points, which the facts of a give
    ([tcb_ok]). The facts β·w ≺ (β·w)[i] that drain owes at b follow
    from the zigzag, β·w ≺ (α·w)[i] ≺ (β·w)[i]. *)

Definition tm_cons : expr :=
  LetU (Var 0) (App (Lam (App EClos (Var 0))) (App (App EForce (Var 5)) (Var 1))).

Definition tm_copier : expr :=
  LetU (Var 0) (App (Lam (LetP (Var 0) (LetU (App EClos (Var 1)) (App EClos (Var 0)))))
                    (App (App EForce (Var 6)) (Pair (Var 3) (Var 2)))).

Definition tm_prod : expr :=
  App EClos (App ESel1 (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 3)))))).

Definition tree_main : expr :=
  LetP (Pair copy drain) (let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam tm_cons)) (LetU (App ESpawn (Lam tm_copier)) tm_prod)))).

(** The creation constraint of a, over α = 0 with z = 1 outside. *)
Definition tca_C : bcs := BCs [pvar 0] send_P.

Lemma tca_ok peq plt : cc_ok peq plt tca_C.
Proof.
  apply (cc_ok_out _ _ tca_C wlt); [exact wlt_trans|exact wlt_irrefl|exact wlt_po| | |].
  - intros a b (f & (w & [-> | (i & ->)]) & _ & E); discriminate E.
  - intros a b (f & (w & [-> | (i & ->)]) & _ & E); cbn [fact_map] in E;
      rewrite ?wstep_inst, ?pwalk_inst in E; injection E as -> ->.
    + right; right. rewrite pwalk_root. split; cbn; done.
    + left. rewrite ?pt_slot_root, ?wstep_root, pwalk_root. split_and!; [cbn; done|cbn; done|].
      split; [rewrite pwalk_root; cbn; done|]. by exists [Some i].
  - intros u p q v (f & (w & [-> | (i & ->)]) & _ & E); cbn [fact_map] in E;
      rewrite ?wstep_inst, ?pwalk_inst in E; injection E as -> ->; rewrite pwalk_root; cbn; done.
Qed.

(** The creation constraint of b, over β = 0 with α = 1 and z = 2
    outside. *)
Definition tcb_P (g : fact) : Prop :=
  ∃ w, g = FLt (pwalk (pv 1 0) w) (pwalk (pv 0 0) w) ∨
       (∃ s, g = FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 1 0) w) s)) ∨
       g = FLt (pwalk (pv 0 0) w) (pv 2 0).
Definition tcb_C : bcs := BCs [pvar 0; pvar 1] tcb_P.

Lemma tcb_ok W Ψ : (BCs [pvar 1] send_P, [pvar 0]) ∈ Ψ → cc_ok (seqs W Ψ) (slt W Ψ) tcb_C.
Proof.
  intros Hg.
  set (TL := glt (cc_up (seqs W Ψ)) (cc_up (slt W Ψ))).
  assert (∀ u s, TL (pwalk (pv 1 0) u) (wstep (pwalk (pv 1 0) u) s)) as Hstep.
  { intros u [i|].
    - assert (slt W Ψ (pwalk (pv 0 0) u) (wstep (pwalk (pv 0 0) u) (Some i))) as H.
      { eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0] (FLt (pwalk (pv 0 0) u) (wstep (pwalk (pv 0 0) u) (Some i))));
          [done|exists u; right; by exists i|fscw|fmw]. }
      pose proof (glt_up (seqs W Ψ) _ _ _ H) as G. by rewrite wstep_inst, pwalk_inst in G.
    - apply glt_po. }
  assert (∀ v u, v ≠ [] → TL (pwalk (pv 1 0) u) (pwalk (pv 1 0) (u ++ v))) as Hch.
  { apply walk_chain; [intros ? ? ?; apply glt_trans|exact Hstep]. }
  assert (∀ w w', pwalk (pv 0 0) w = pwalk (pv 0 0) w' ∨ wlt (pwalk (pv 0 0) w) (pwalk (pv 0 0) w') →
            pwalk (pv 1 0) w' = pwalk (pv 1 0) w ∨ ∃ v, v ≠ [] ∧ pwalk (pv 1 0) w' = pwalk (pv 1 0) (w ++ v)) as Hrel.
  { intros w w' [E|[_ (v & Hv & E)]].
    - left. apply (f_equal (pt_inst (λ _, pv 1 0))) in E. rewrite !pwalk_inst in E. cbn in E. done.
    - right. exists v. split; [done|]. rewrite <-pwalk_app in E.
      apply (f_equal (pt_inst (λ _, pv 1 0))) in E. rewrite !pwalk_inst in E. cbn in E. done. }
  apply (cc_ok_out _ _ tcb_C wlt); [exact wlt_trans|exact wlt_irrefl|exact wlt_po| | |].
  - intros a b (f & (w & [-> | [(s & ->) | ->]]) & _ & E); discriminate E.
  - intros a b (f & (w & [-> | [(s & ->) | ->]]) & _ & E); cbn [fact_map] in E;
      rewrite ?wstep_inst, ?pwalk_inst in E; injection E as -> ->; right;
      rewrite ?pt_slot_root, ?wstep_root, ?pwalk_root; cbn; auto.
  - intros u p q v (f & (w & [-> | [(s & ->) | ->]]) & _ & E) (f' & (w' & [-> | [(s' & ->) | ->]]) & _ & E')
      Hu Hp Hq Hv Hpq; cbn [fact_map] in E, E'; rewrite ?wstep_inst, ?pwalk_inst in E;
      rewrite ?wstep_inst, ?pwalk_inst in E'; injection E as -> ->; injection E' as -> ->;
      change (pt_inst (pup 1 (plist [pvar 0; pvar 1])) (pv 0 0)) with (pv 0 0) in *;
      change (pt_inst (pup 1 (plist [pvar 0; pvar 1])) (pv 1 0)) with (pv 1 0) in *;
      change (pt_inst (pup 1 (plist [pvar 0; pvar 1])) (pv 2 0)) with (pv 2 0) in *;
      try (exfalso; apply Hu; by rewrite pwalk_root);
      try (exfalso; revert Hq; rewrite pwalk_root; done).
    + fold TL. destruct (Hrel w w' Hpq) as [E|(v & Hv' & E)]; rewrite E.
      * rewrite <-pwalk_snoc. apply Hch. by destruct w.
      * rewrite <-pwalk_snoc, <-app_assoc. apply Hch. by destruct v.
    + fold TL.
      assert (slt W Ψ (pwalk (pv 0 0) w) (pv 1 0)) as H.
      { eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0] (FLt (pwalk (pv 0 0) w) (pv 1 0)));
          [done|exists w; by left|fscw|fmw]. }
      pose proof (glt_up (seqs W Ψ) _ _ _ H) as G. by rewrite pwalk_inst in G.
Qed.

(** After both [new]s b is 0, a is 1 and z is 2. The producer acts on
    a at α, α[B], α[B]+1, (α[B]+1)[A] and its [A]. *)
Lemma tree_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) tree_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold tree_main.
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply drain_typed, HW|exact HWs|apply copy_typed, HW]. }
  cbn. apply (t_new_open W _ _ ∅ _ _ _ _ (SSeq TreeC SEnd) tca_C); [apply tca_ok|..].
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  apply (t_new_open W _ _ ∅ _ _ _ _ (SSeq TreeC SEnd) tcb_C); [apply tcb_ok; by right; left|..].
  { constructor; [eapply skn_inst; [by right; left|by left|done]|].
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  set (Ψ := [(top_C0, [pvar 2]); (BCs [pvar 2] send_P, [pvar 1]); (BCs [pvar 1; pvar 2] tcb_P, [pvar 0])]).
  assert (∀ w, slt W Ψ (pwalk (pv 1 0) w) (pwalk (pv 0 0) w)) as Hab.
  { intros w. eapply (sl_hyp W Ψ [pvar 1; pvar 2] tcb_P [pvar 0] (FLt (pwalk (pv 1 0) w) (pwalk (pv 0 0) w)));
      [inlist|exists w; by left|fscw|fmw]. }
  assert (∀ w s, slt W Ψ (pwalk (pv 0 0) w) (wstep (pwalk (pv 1 0) w) s)) as Hba.
  { intros w s. eapply (sl_hyp W Ψ [pvar 1; pvar 2] tcb_P [pvar 0] (FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 1 0) w) s)));
      [inlist|exists w; right; left; by exists s|fscw|fmw]. }
  assert (∀ w, slt W Ψ (pwalk (pv 0 0) w) (pv 2 0)) as Hbz.
  { intros w. eapply (sl_hyp W Ψ [pvar 1; pvar 2] tcb_P [pvar 0] (FLt (pwalk (pv 0 0) w) (pv 2 0)));
      [inlist|exists w; by right; right|fscw|fmw]. }
  assert (∀ w, slt W Ψ (pwalk (pv 1 0) w) (pv 2 0)) as Haz.
  { intros w. eapply (sl_hyp W Ψ [pvar 2] send_P [pvar 1] (FLt (pwalk (pv 0 0) w) (pv 1 0)));
      [inlist|exists w; by left|fscw|fmw]. }
  assert (∀ w i, slt W Ψ (pwalk (pv 1 0) w) (wstep (pwalk (pv 1 0) w) (Some i))) as Haa.
  { intros w i. eapply (sl_hyp W Ψ [pvar 2] send_P [pvar 1]
                          (FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))));
      [inlist|exists w; right; by exists i|fscw|fmw]. }
  assert (∀ w i, slt W Ψ (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))) as Hbb.
  { intros w i. eapply sl_trans; [apply (Hba w (Some i))|]. rewrite <-!pwalk_snoc. apply Hab. }
  cbn. tstep.
  { (* the consumer *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 2 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold tm_cons. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P) (TSess SEnd (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pv 2 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 2 0] after_P)
                  (TSess SEnd (pv 0 0)) _
                  (<[1:=Some (pv 3 0)]> (<[0:=Some (pv 3 0)]> ∅))
                  [(top_C0, [pvar 3]); (BCs [pvar 3] send_P, [pvar 2]); (BCs [pvar 2; pvar 3] tcb_P, [pvar 1]);
                   (BCs [pv 1 0; pv 3 0] after_P, [pv 0 0])]
                  [Some (TSess SEnd (pv 0 0)); None; None; None; None; None; None; None; None; None;
                   Some drain_ty; Some copy_ty]
                  (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 3 0). split; [done|]. right.
      eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
        [inlist|right; exists []; by left|fsc|reflexivity].
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq TreeD SEnd) (pv 0 0)) RD);
        [reflexivity| | |].
      + unfold RD. rewrite <-(drain_inst (pv 0 0) (pv 2 0) SEnd).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None drain_body [pv 0 0; pv 2 0] [SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & [-> | (i & ->)]) _; cbn [fact_map fact_holds];
            rewrite ?wstep_inst, ?pwalk_inst; [apply Hbz|apply Hbb].
        * constructor; [eapply skn_inst; [by right; right; left|by left|done]|].
          constructor; [eapply skn_inst; [by left|by left|done]|constructor].
        * apply Forall_singleton, hcontractive_end.
      + tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { (* the copier *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 2 0)) (Some (pv 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply (Hab [])]. }
    unfold tm_copier. cbn. tstep; [tstep|]. cbn.
    set (RC := TEx (LPt (pv 1 0)) 2 (BCs [pv 1 0; pv 2 0] cafter_P)
                 (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0)))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None RC); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RC _ (Some (pv 2 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pv 1 0)) 2 (BCs [pv 1 0; pv 2 0] cafter_P)
                  (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0))) _
                  (<[1:=Some (pv 4 0)]> (<[0:=Some (pv 4 0)]> ∅))
                  [(top_C0, [pvar 4]); (BCs [pvar 4] send_P, [pvar 3]); (BCs [pvar 3; pvar 4] tcb_P, [pvar 2]);
                   (BCs [pv 3 0; pv 4 0] cafter_P, [pv 0 0; pv 1 0])]
                  [Some (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0)));
                   None; None; None; None; None; None; None; None; None; Some drain_ty; Some copy_ty]
                  (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (Ψc := [(top_C0, [pvar 4]); (BCs [pvar 4] send_P, [pvar 3]); (BCs [pvar 3; pvar 4] tcb_P, [pvar 2]);
                  (BCs [pv 3 0; pv 4 0] cafter_P, [pv 0 0; pv 1 0])]).
      assert (slt W Ψc (pv 0 0) (pv 1 0) ∧ slt W Ψc (pv 0 0) (pv 4 0) ∧ slt W Ψc (pv 1 0) (pv 4 0))
        as (H01 & H0z & H1z).
      { split_and!.
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 0 0) (pv 1 0))); [inlist|right; exists []; by left|fsc|reflexivity].
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 0 0) (pv 3 0))); [inlist|right; exists []; by right; right; left|fsc|reflexivity].
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 1 0) (pv 3 0))); [inlist|right; exists []; by right; right; right|fsc|reflexivity]. }
      tstep; [tstep|]. cbn. tstep.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; exact H01|].
        exists (pv 4 0). split; [done|]. by right.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 0)) (TSess SEnd (pv 1 0))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 4 0). split; [done|]. by right.
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None
                (TProd (TSess (SSeq TreeD SEnd) (pv 1 0)) (TSess (SSeq TreeC SEnd) (pv 0 0))) RC);
        [reflexivity| | |].
      + unfold RC. rewrite <-(copy_inst (pv 1 0) (pv 0 0) (pv 2 0) SEnd SEnd).
        apply (typed_force W _ _ _ _ _ _ 3 2 copy_C None copy_body [pv 1 0; pv 0 0; pv 2 0] [SEnd; SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & [-> | [(s & ->) | [-> | ->]]]) _; cbn [fact_map fact_holds];
            rewrite ?wstep_inst, ?pwalk_inst; [apply Hab|apply Hba|apply Haz|apply Hbz].
        * constructor; [eapply skn_inst; [by right; left|by left|done]|].
          constructor; [eapply skn_inst; [by right; right; left|by left|done]|].
          constructor; [eapply skn_inst; [by left|by left|done]|constructor].
        * constructor; [apply hcontractive_end|constructor; [apply hcontractive_end|constructor]].
      + eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq TreeD SEnd) (pv 1 0))); [reflexivity|tstep|tstep].
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. apply sle_refl, HW. }
  (* the producer: α[B], α[B]+1, (α[B]+1)[A] and its [A] *)
  unfold tm_prod. cbn.
  set (p1 := pwalk (pv 1 0) [Some true]).
  set (p2 := pwalk (pv 1 0) [Some true; None]).
  set (p3 := pwalk (pv 1 0) [Some true; None; Some false]).
  set (p4 := pwalk (pv 1 0) [Some true; None; Some false; Some false]).
  eapply (tv_appk W HW _ _ _ _ KClos _ (Some p4) (TSess SEnd p4));
    [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip SEnd) p4)).
  { apply teq_steq. split; [done|apply skip_l, hcontractive_end]. }
  eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some p3)
            (TSess (SPlus (SSeq SSkip SEnd) (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) SEnd)) p3));
    [|apply KTSel1, (Haa [Some true; None; Some false] false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq TreeC SEnd)) p3)).
  { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply TreeC_seq].
    apply hcontractive_seq; [apply TreeC_hc|apply hcontractive_end]. }
  eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some p2)
            (TSess (SPlus (SSeq SSkip (SSeq TreeC SEnd))
                          (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) (SSeq TreeC SEnd))) p2));
    [|apply KTSel1, (Haa [Some true; None] false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TreeC (SSeq TreeC SEnd)) p2)).
  { apply teq_steq. split; [done|apply TreeC_seq]. }
  eapply (tv_appk W HW _ _ _ _ KSend _ (Some p1)
            (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC SEnd))) p1)));
    [|apply (KTSend _ _ _ 0 TUnit (SSeq TreeC (SSeq TreeC SEnd)) p1); cbn; set_solver
     |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  tstep; [|tstep].
  eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 1 0))
            (TSess (SPlus (SSeq SSkip SEnd) (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC SEnd)))) (pv 1 0)));
    [|apply KTSel2, (Haa [] true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  eapply t_conv; [|tstep]. apply teq_steq. split; [done|].
  eapply seq_trans; [apply TreeC_seq|]. apply seq_plus_cong; [apply seq_refl|apply node_snd, hcontractive_end].
Qed.

Theorem tree_deadlock_free : deadlock_free (∅, {[+ tree_main +]}).
Proof. apply (soundness_source 1 top_C0 _ TUnit (c0_acyclic_creation _ _ top_acyclic)); [constructor|apply tree_typed]. Qed.
