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
    channel a, copy from a to b, and drain on b.

    With end points a select at p continues at (p[i])‾ and a branch at
    p[i], and the gates compare a blocking point with the partner
    points of the other held ends. C, C′, D, D′ and the creation
    constraints state every fact between all polarities of its two
    points, which covers both ends without tracking which end walks
    where ([wpol], [pnorm]). *)

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
Abbreviation psl a i k := (Pt (NPayload (NVar a) 0 (bidx i)) k).

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

(** Points at a polarity: the name and the instances commute with it. *)
Lemma st_name_polar c x : pt_name (pt_polar c x) = pt_name x.
Proof. by destruct c. Qed.

Lemma st_root_polar c x : pt_root (pt_polar c x) = pt_root x.
Proof. by destruct c. Qed.

Ltac fscp := cbn [fact_scoped]; rewrite ?st_name_polar; fscw.
Ltac piwp := rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst; reflexivity.
Ltac fmwp := cbn [fact_map]; rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst; reflexivity.

(** A ≺ fact ι·w ≺ ζ or ι·w ≺ (ι·w)[i] of a hypothesis C = send_C,
    with the points at polarities c and c′. *)
Ltac hypwc c w := eapply (sl_hyp0 _ _ send_P _ (pt_polar c (pwalk (pv 0 0) w)) (pv 1 0));
  [inlist|exists w, c, true; by left|fscp|piwp|piwp].
Ltac hypbc c w i c' :=
  eapply (sl_hyp0 _ _ send_P _ (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i))));
    [inlist|exists w, c, c'; right; by exists i|fscp|piwp|piwp].
Ltac hypw w := hypwc true w.
Ltac hypb w i := hypbc true w i true.

(** The facts of a hypothesis C′ = after_C at the outer points env. *)
Ltac hypawc env xs c w :=
  eapply (sl_hyp _ _ env after_P xs (FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 2 0)));
    [inlist|right; exists w, c, true; by left|fscp|fmwp].
Ltac hypabc env xs c w i c' :=
  eapply (sl_hyp _ _ env after_P xs (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i)))));
    [inlist|right; exists w, c, c'; right; by exists i|fscp|fmwp].
Ltac hypaw env xs w := hypawc env xs true w.

(** Walks from a point at a polarity. A walk from x̄ ends at the walk
    from x, dual until its first choice step. *)
Fixpoint wpol (w : list (option bool)) : bool :=
  match w with [] => false | Some _ :: _ => true | None :: w' => wpol w' end.

Lemma pwalk_dual_eq x w : pwalk (pt_dual x) w = pt_polar (wpol w) (pwalk x w).
Proof.
  revert x. induction w as [|[i|] w IH]; intros x; simpl; [done| |].
  - by rewrite pt_payload_dual.
  - rewrite <-pt_dual_shift. apply IH.
Qed.

Lemma pwalk_polar_eq c x w : pwalk (pt_polar c x) w = pt_polar (orb c (wpol w)) (pwalk x w).
Proof. destruct c; [done|apply pwalk_dual_eq]. Qed.

Lemma polar_polar_eq c d y : pt_polar c (pt_polar d y) = pt_polar (eqb c d) y.
Proof. destruct c, d; simpl; try done. apply pt_dual_dual. Qed.

Lemma polar_dual_eq c y : pt_polar c (pt_dual y) = pt_polar (negb c) y.
Proof. destruct c; simpl; [done|apply pt_dual_dual]. Qed.

Lemma dual_polar_eq c y : pt_dual (pt_polar c y) = pt_polar (negb c) y.
Proof. destruct c; simpl; [done|apply pt_dual_dual]. Qed.

Lemma pt_inst_plist_pv xs a x : xs !! a = Some x → pt_inst (plist xs) (pv a 0) = x.
Proof. intros H. unfold pt_inst, plist. simpl. rewrite H. destruct x. unfold pt_shift. simpl. f_equal. lia. Qed.

Definition wspol (c : bool) (s : option bool) : bool := match s with Some _ => true | None => c end.

Lemma wstep_polar_eq c x s : wstep (pt_polar c x) s = pt_polar (wspol c s) (wstep x s).
Proof. destruct s; simpl; [by rewrite pt_polar_payload|by rewrite pt_polar_shift]. Qed.

Ltac pnorm := rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst;
  repeat (erewrite pt_inst_plist_pv; [|reflexivity]);
  rewrite ?pwalk_dual_eq, ?pwalk_polar_eq, ?wstep_polar_eq, ?polar_polar_eq, ?polar_dual_eq, ?dual_polar_eq.

(** A fact of a polarity-generic family at the polarities of the goal. *)
Ltac h0 t := first [apply (t true true)|apply (t true false)|apply (t false true)|apply (t false false)
  |eapply (proj1 (t _ _))|eapply (proj1 (proj2 (t _ _)))|eapply (proj1 (proj2 (proj2 (t _ true))))
  |eapply (proj2 (proj2 (proj2 (t _ true))))|eapply (proj1 (proj2 (proj2 (proj2 (t _ true)))))
  |eapply (proj2 (proj2 (proj2 (proj2 (t _ _)))))|eapply (t _ _)].
Ltac hypab env xs w i := hypabc env xs true w i true.

Lemma drain_typed W F : world_wf W → typed W ∅ [] ∅ [] F drain drain_ty.
Proof.
  intros HW. unfold drain, drain_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
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
    + apply KTBra; [hypbc true ([] : list (option bool)) false false|hypbc true ([] : list (option bool)) true false].
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hypw ([] : list (option bool)).
  - cbn. apply (t_pack W _ _ _ _ _ _ (LPt (pv 0 0)) 1 after_C (TSess s (pv 0 0)) [psl 0 false 0]).
    + done.
    + apply Forall_singleton. apply (skn_in W _ send_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done].
    + unfold after_C. apply bcs_hold_env. intros f [(c & c' & ->) | (w & c & c' & [-> | (i & ->)])] _;
        cbn [fact_map fact_holds]; rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst.
      * hypbc c ([] : list (option bool)) false c'.
      * hypwc c (Some false :: w).
      * hypbc c (Some false :: w) i c'.
    + split; [|done]. intros y Hy. mem_cases Hy. right. hypbc true ([] : list (option bool)) false false.
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
        assert (∀ c c', slt W Ψ2 (pt_polar c (pv 2 0)) (pt_polar c' (pv 0 0))) as Hch.
        { intros c c'. eapply sl_trans.
          { eapply (sl_hyp0 _ _ send_P _ (pt_polar c (pv 0 0)) (wstep (pv 0 0) (Some true)));
              [inlist|exists [], c, true; right; by exists true|destruct c; fscw|by destruct c|reflexivity]. }
          eapply sl_trans; [apply (slt_po W _ (psl 2 true 0) HW)|].
          eapply sl_trans.
          - eapply (sl_hyp W _ [psl 2 true 1; pv 3 0] after_P [pv 1 0] (FLt (pv 1 0) (pv 0 0)));
              [inlist|left; by exists true, true|fsc|reflexivity].
          - eapply (sl_hyp W _ [pv 1 0; pv 3 0] after_P [pv 0 0] (FLt (pv 1 0) (pt_polar c' (pv 0 0))));
              [inlist|left; by exists true, c'|destruct c'; fsc|by destruct c']. }
        apply (t_pack W _ _ _ _ _ _ (LPt (pv 2 0)) 1 (BCs [pv 2 0; pv 3 0] after_P) (TSess s (pv 0 0)) [pv 0 0]).
        -- done.
        -- apply Forall_singleton.
           apply (skn_in W _ (BCs [pv 1 0; pv 3 0] after_P) [pv 0 0] (pv 0 0)); [inlist|by left|done].
        -- apply bcs_hold_env. intros f [(c & c' & ->) | (w & c & c' & [-> | (i & ->)])] _;
             cbn [fact_map fact_holds]; rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst; [apply Hch| |].
           ++ hypawc [pv 1 0; pv 3 0] [pv 0 0] c w.
           ++ hypabc [pv 1 0; pv 3 0] [pv 0 0] c w i c'.
        -- split; [|done]. intros y Hy. mem_cases Hy. right. apply (Hch true false).
        -- cbn. tstep.
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq TreeD s) (pv 0 0)) R2);
          [reflexivity| | |].
        -- unfold R2. rewrite <-(drain_inst (pv 0 0) (pv 2 0) s).
           apply (typed_force W _ _ _ _ _ _ 2 1 send_C None drain_body [pv 0 0; pv 2 0] [s]);
             [done|done| | |done| |apply ubs_none|tstep].
           ++ apply bcs_hold_intro. intros g (w & c & c' & [-> | (i & ->)]) _;
                cbn [fact_map fact_holds]; rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst.
              ** hypawc [psl 1 true 1; pv 2 0] [pv 0 0] c w.
              ** hypabc [psl 1 true 1; pv 2 0] [pv 0 0] c w i c'.
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
        -- apply bcs_hold_self; [by left|vb_list|]. intros g (w & c & c' & [-> | (i & ->)]) _;
             exists (Some true :: None :: w), c, c'; [left|right; exists i]; fmwp.
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
    where a choice continues. With end points every fact holds between
    all polarities of its two points (see SendTreeType.v). *)
Definition copy_P (g : fact) : Prop :=
  ∃ w c c', g = FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (pwalk (pv 1 0) w)) ∨
       (∃ s, g = FLt (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) s))) ∨
       g = FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 2 0) ∨ g = FLt (pt_polar c (pwalk (pv 1 0) w)) (pv 2 0).
Definition copy_C : bcs := BCs [] copy_P.

(** D′ under the binder of κ′ = 0 and ι′ = 1, with κ and ζ as 2 and 3. *)
Definition cafter_P (g : fact) : Prop :=
  (∃ c c', g = FLt (pt_polar c (pv 2 0)) (pt_polar c' (pv 0 0))) ∨
  ∃ w c c', g = FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (pwalk (pv 1 0) w)) ∨
       (∃ s, g = FLt (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) s))) ∨
       g = FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 3 0) ∨ g = FLt (pt_polar c (pwalk (pv 1 0) w)) (pv 3 0).
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
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  intros ss Hss Hhc. destruct ss as [|sb [|sa [|]]]; try discriminate Hss.
  apply Forall_cons in Hhc as [Hb Hhc]. rewrite Forall_singleton in Hhc. rename Hhc into Ha.
  fold copy_ty.
  change (lenv_pinst (pshift 3) [Some copy_ty]) with [Some (pinst_ty (pshift 3) copy_ty)].
  rewrite (pinst_closed _ copy_ty) by apply copy_ty_pscoped.
  cbn. fold TreeD. change (bcs_inst (pshift 3) copy_C) with copy_C.
  assert (∀ Ψ w s c c', (copy_C, [pv 0 0; pv 1 0; pv 2 0]) ∈ Ψ →
    slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (pwalk (pv 1 0) w)) ∧
    slt W Ψ (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) s)) ∧
    slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pv 2 0) ∧ slt W Ψ (pt_polar c (pwalk (pv 1 0) w)) (pv 2 0)) as Hc.
  { intros Ψ w s c c' Hg. split_and!.
    - eapply (sl_hyp0 W Ψ copy_P [pv 0 0; pv 1 0; pv 2 0] (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (pwalk (pv 1 0) w)));
        [done|exists w, c, c'; by left|fscp|piwp|piwp].
    - eapply (sl_hyp0 W Ψ copy_P [pv 0 0; pv 1 0; pv 2 0] (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) s)));
        [done|exists w, c, c'; right; left; by exists s|fscp|piwp|piwp].
    - eapply (sl_hyp0 W Ψ copy_P [pv 0 0; pv 1 0; pv 2 0] (pt_polar c (pwalk (pv 0 0) w)) (pv 2 0));
        [done|exists w, c, c'; by right; right; left|fscp|piwp|piwp].
    - eapply (sl_hyp0 W Ψ copy_P [pv 0 0; pv 1 0; pv 2 0] (pt_polar c (pwalk (pv 1 0) w)) (pv 2 0));
        [done|exists w, c, c'; by right; right; right|fscp|piwp|piwp]. }
  pose proof (λ w s c c', Hc [(copy_C, [pv 0 0; pv 1 0; pv 2 0])] w s c c' ltac:(by left)) as H0.
  (* the facts a choice owes, from the zigzag: κ ≺ ι ≺ κ[i] ≺ ι[i] *)
  set (Ψ0 := [(copy_C, [pv 0 0; pv 1 0; pv 2 0])]).
  assert (∀ i c c', slt W Ψ0 (pt_polar c (pv 0 0)) (pt_polar c' (wstep (pv 0 0) (Some i)))) as Hκb.
  { intros i c c'. eapply sl_trans; [exact (proj1 (H0 [] None c true))|exact (proj1 (proj2 (H0 [] (Some i) true c')))]. }
  assert (∀ i c c', slt W Ψ0 (pt_polar c (pv 1 0)) (pt_polar c' (wstep (pv 1 0) (Some i)))) as Hιb.
  { intros i c c'. eapply sl_trans; [exact (proj1 (proj2 (H0 [] (Some i) c true)))|exact (proj1 (H0 [Some i] None true c'))]. }
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 0))
              (TSess (SWith (SSeq SSkip sb) (SSeq (SSeq (SRcv 0 TUnit) (SSeq TreeD TreeD)) sb)) (pv 0 0))).
    + eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TreeD_seq].
    + apply KTBra; [h0 (Hκb false)|h0 (Hκb true)].
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy; h0 (H0 [] None)|].
      exists (pv 2 0). split; [done|]. right. h0 (H0 [] None).
  - (* leaf *)
    cbn. apply (t_pack W _ _ _ _ _ _ (LPt (pv 0 0)) 2 cafter_C
                 (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0))) [psl 0 false 0; pt_dual (psl 1 false 0)]).
    + done.
    + apply Forall_cons. split; [|apply Forall_singleton].
      * apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 0 0)); [by left|by left|done].
      * apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 1 0)); [by left|by right; left|done].
    + unfold cafter_C. apply bcs_hold_env.
      intros f [(c & c' & ->) | (w & c & c' & [-> | [(s & ->) | [-> | ->]]])] _; cbn [fact_map fact_holds];
        pnorm.
      * h0 (Hκb false).
      * h0 (H0 (Some false :: w) None).
      * h0 (H0 (Some false :: w) s).
      * h0 (H0 (Some false :: w) None).
      * h0 (H0 (Some false :: w) None).
    + split; [|done]. intros y Hy. mem_cases Hy; right; [h0 (Hκb false)|].
      apply (sl_trans _ _ _ (pv 1 0)); [exact (proj1 (H0 [] None true true))|h0 (Hιb false)].
    + cbn. apply (t_conv W _ _ _ _ _ _ (TProd (TSess (SSeq SSkip sb) (psl 0 false 0))
                                                (TSess (SSeq SSkip sa) (pt_dual (psl 1 false 0))))).
      { apply teq_steq. split; split; [done|by apply skip_l|done|by apply skip_l]. }
      eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq SSkip sb) (psl 0 false 0))); [reflexivity| |tstep].
      eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (pv 1 0))
                (TSess (SPlus (SSeq SSkip sa) (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) sa)) (pv 1 0))).
      * eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply TreeC_seq].
      * apply KTSel1. h0 (Hιb false).
      * done.
      * apply ubs_intro; [intros y Hy; mem_cases Hy; h0 (H0 [] (Some false))|].
        exists (pv 2 0). split; [done|]. right. h0 (H0 [] None).
  - (* node *)
    cbn. tstep.
    { set (S2c := SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC sa))).
      eapply (tv_pair W HW _ _ _ _ _ _ (TSess S2c (pt_dual (psl 1 true 0)))); [reflexivity| |].
      - eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (psl 0 true 0))
                  (TSess (SSeq (SRcv 0 TUnit) (SSeq TreeD (SSeq TreeD sb))) (psl 0 true 0))).
        + eapply t_conv; [|tstep]. apply teq_steq. split; [done|by apply node_rcv].
        + apply KTRecv.
        + kscope.
        + apply ubs_intro; [intros y Hy; mem_cases Hy; h0 (H0 [Some true] None)|].
          exists (pv 2 0). split; [done|]. right. h0 (H0 [Some true] None).
      - eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 1 0)) (TSess (SPlus (SSeq SSkip sa) S2c) (pv 1 0))).
        + eapply t_conv; [|tstep]. apply teq_steq. split; [done|].
          eapply seq_trans; [apply TreeC_seq|]. apply seq_plus_cong; [apply seq_refl|by apply node_snd].
        + apply KTSel2. h0 (Hιb true).
        + done.
        + apply ubs_intro; [intros y Hy; mem_cases Hy; h0 (H0 [] (Some true))|].
          exists (pv 2 0). split; [done|]. right. h0 (H0 [] None). }
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
      assert (∀ Ψ w s c c', (BCs [psl 2 true 1; pv 4 0] cafter_P, [pv 0 0; pv 1 0]) ∈ Ψ →
        slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (pwalk (pv 1 0) w)) ∧
        slt W Ψ (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) s)) ∧
        slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pv 4 0) ∧ slt W Ψ (pt_polar c (pwalk (pv 1 0) w)) (pv 4 0) ∧
        slt W Ψ (pt_polar c (psl 2 true 1)) (pt_polar c' (pv 0 0))) as H1.
      { intros Ψ w s c c' Hg. split_and!.
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (pwalk (pv 1 0) w))));
            [exact Hg|right; exists w, c, c'; by left|fscp|fmwp].
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) s))));
            [exact Hg|right; exists w, c, c'; right; left; by exists s|fscp|fmwp].
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 3 0)));
            [exact Hg|right; exists w, c, c'; by right; right; left|fscp|fmwp].
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pt_polar c (pwalk (pv 1 0) w)) (pv 3 0)));
            [exact Hg|right; exists w, c, c'; by right; right; right|fscp|fmwp].
        - eapply (sl_hyp W Ψ _ cafter_P _ (FLt (pt_polar c (pv 2 0)) (pt_polar c' (pv 0 0))));
            [exact Hg|left; by exists c, c'|destruct c, c'; fsc|by destruct c, c']. }
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
        assert (∀ w s c c', (BCs [pv 2 0; pv 6 0] cafter_P, [pv 0 0; pv 1 0]) ∈ Ψ2 →
          slt W Ψ2 (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (pwalk (pv 1 0) w)) ∧
          slt W Ψ2 (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) s)) ∧
          slt W Ψ2 (pt_polar c (pwalk (pv 0 0) w)) (pv 6 0) ∧ slt W Ψ2 (pt_polar c (pwalk (pv 1 0) w)) (pv 6 0) ∧
          slt W Ψ2 (pt_polar c (pv 2 0)) (pt_polar c' (pv 0 0))) as H3.
        { intros w s c c' Hg. split_and!.
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (pwalk (pv 1 0) w))));
              [exact Hg|right; exists w, c, c'; by left|fscp|fmwp].
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) s))));
              [exact Hg|right; exists w, c, c'; right; left; by exists s|fscp|fmwp].
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 3 0)));
              [exact Hg|right; exists w, c, c'; by right; right; left|fscp|fmwp].
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pt_polar c (pwalk (pv 1 0) w)) (pv 3 0)));
              [exact Hg|right; exists w, c, c'; by right; right; right|fscp|fmwp].
          - eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pt_polar c (pv 2 0)) (pt_polar c' (pv 0 0))));
              [exact Hg|left; by exists c, c'|destruct c, c'; fsc|by destruct c, c']. }
        pose proof (λ w s c c', H3 w s c c' ltac:(inlist)) as H3'. clear H3.
        assert (∀ c c', slt W Ψ2 (pt_polar c (pv 4 0)) (pt_polar c' (pv 0 0))) as Hch.
        { intros c c'. eapply sl_trans.
          { eapply sl_trans.
            - eapply (sl_hyp0 W Ψ2 copy_P [pv 4 0; pv 5 0; pv 6 0] (pt_polar c (pv 0 0)) (pv 1 0));
                [inlist|exists [], c, true; by left|destruct c; fsc|by destruct c|reflexivity].
            - eapply (sl_hyp0 W Ψ2 copy_P [pv 4 0; pv 5 0; pv 6 0] (pv 1 0) (wstep (pv 0 0) (Some true)));
                [inlist|exists [], true, true; right; left; by exists (Some true)|fscw|reflexivity|reflexivity]. }
          eapply sl_trans; [apply (slt_po W _ (psl 4 true 0) HW)|].
          apply (sl_trans _ _ _ (pv 2 0)); [|apply (H3' [] None true c')].
          eapply (sl_hyp W Ψ2 _ cafter_P _ (FLt (pv 2 0) (pv 0 0))); [inlist|left; by exists true, true|fsc|reflexivity]. }
        apply (t_pack W _ _ _ _ _ _ (LPt (pv 4 0)) 2 (BCs [pv 4 0; pv 6 0] cafter_P)
                 (TProd (TSess sb (pv 0 0)) (TSess sa (pv 1 0))) [pv 0 0; pv 1 0]).
        -- done.
        -- apply Forall_cons. split; [|apply Forall_singleton].
           ++ apply (skn_in W _ (BCs [pv 2 0; pv 6 0] cafter_P) [pv 0 0; pv 1 0] (pv 0 0)); [inlist|by left|done].
           ++ apply (skn_in W _ (BCs [pv 2 0; pv 6 0] cafter_P) [pv 0 0; pv 1 0] (pv 1 0)); [inlist|by right; left|done].
        -- apply bcs_hold_env.
           intros f [(c & c' & ->) | (w & c & c' & [-> | [(s & ->) | [-> | ->]]])] _; cbn [fact_map fact_holds];
             pnorm; [apply Hch|h0 (H3' w None)|h0 (H3' w s)|h0 (H3' w None)|h0 (H3' w None)].
        -- split; [|done]. intros y Hy. mem_cases Hy; right; [apply (Hch true false)|].
           apply (sl_trans _ _ _ (pv 0 0)); [apply (Hch true true)|apply (H3' [] None true false)].
        -- cbn. tstep.
      * eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 4 0)) None
                  (TProd (TSess (SSeq TreeD sb) (pv 0 0)) (TSess (SSeq TreeC sa) (pv 1 0))) R2);
          [reflexivity| | |].
        -- unfold R2. rewrite <-(copy_inst (pv 0 0) (pv 1 0) (pv 4 0) sb sa).
           apply (typed_force W _ _ _ _ _ _ 3 2 copy_C None copy_body [pv 0 0; pv 1 0; pv 4 0] [sb; sa]);
             [done|done| | |done| |apply ubs_none|tstep].
           ++ apply bcs_hold_intro.
              intros g (w & c & c' & [-> | [(s & ->) | [-> | ->]]]) _; cbn [fact_map fact_holds];
                pnorm;
                [apply (H1 Ψ1 w None c c')|apply (H1 Ψ1 w s c c')|apply (H1 Ψ1 w None c c')|apply (H1 Ψ1 w None c c')]; inlist.
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
                       (TSess (SSeq TreeC (SSeq TreeC sa)) (pt_dual (psl 1 true 1)))) R1); [reflexivity| | |].
      * unfold R1. rewrite <-(copy_inst (psl 0 true 1) (pt_dual (psl 1 true 1)) (pv 2 0) (SSeq TreeD sb) (SSeq TreeC sa)).
        apply (typed_force W _ _ _ _ _ _ 3 2 copy_C None copy_body [psl 0 true 1; pt_dual (psl 1 true 1); pv 2 0]
                 [SSeq TreeD sb; SSeq TreeC sa]); [done|done| | |done| |apply ubs_none|tstep].
        -- apply bcs_hold_self; [by left|vb_list|].
           intros g (w & c & c' & [-> | [(s & ->) | [-> | ->]]]) _; cbn [fact_map]; pnorm;
             [eexists (Some true :: None :: w), _, _; left; reflexivity
             |eexists (Some true :: None :: w), _, _; right; left; exists s; reflexivity
             |eexists (Some true :: None :: w), _, c'; right; right; left; reflexivity
             |eexists (Some true :: None :: w), _, c'; right; right; right; reflexivity].
        -- apply Forall_cons. split; [|apply Forall_cons; split; [|apply Forall_singleton]].
           ++ apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 0 0)); [by left|by left|done].
           ++ apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 1 0)); [by left|by right; left|done].
           ++ apply (skn_in W _ copy_C [pv 0 0; pv 1 0; pv 2 0] (pv 2 0)); [by left|by right; right; left|done].
        -- apply Forall_cons. split; [|apply Forall_singleton];
             apply hcontractive_seq; auto using TreeD_hc, TreeC_hc.
      * eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq TreeD (SSeq TreeD sb)) (psl 0 true 1))); [reflexivity| |tstep].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pt_dual (psl 1 true 0)))
                  (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC sa))) (pt_dual (psl 1 true 0))))).
        -- tstep; [|tstep]. tstep.
        -- apply (KTSend _ _ _ 0 TUnit (SSeq TreeC (SSeq TreeC sa)) (pt_dual (psl 1 true 0))). cbn. set_solver.
        -- kscope.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy; h0 (H0 [Some true] None)|].
           exists (pv 2 0). split; [done|]. right. h0 (H0 [Some true] None).
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
    from the zigzag, β·w ≺ (α·w)[i] ≺ (β·w)[i]. The producer holds a
    at α, copy holds a′ at ᾱ and b at β, drain holds b′ at β̄, and all
    facts hold at all polarities. *)

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
  apply (cc_ok_out _ _ tca_C wlt); [exact wlt_trans|exact wlt_irrefl|exact wlt_po|exact wlt_dpo| | |].
  - intros a b (f & (w & c & c' & [-> | (i & ->)]) & _ & E); discriminate E.
  - intros a b (f & (w & c & c' & [-> | (i & ->)]) & _ & E); cbn [fact_map] in E;
      rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst in E; injection E as -> ->.
    + right; right. rewrite st_root_polar, pwalk_root. split; cbn; done.
    + left. rewrite !st_root_polar, ?pt_payload_root, ?wstep_root, pwalk_root. split_and!; [cbn; done|cbn; done|].
      split; [rewrite st_root_polar, pwalk_root; cbn; done|]. exists [Some i], c'. split; [done|].
      simpl. by rewrite pt_polar_payload.
  - intros u p q v (f & (w & c & c' & [-> | (i & ->)]) & _ & E); cbn [fact_map] in E;
      rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst in E; injection E as -> ->;
      rewrite st_root_polar, pwalk_root; cbn; done.
Qed.

(** The creation constraint of b, over β = 0 with α = 1 and z = 2
    outside. *)
Definition tcb_P (g : fact) : Prop :=
  ∃ w c c', g = FLt (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (pwalk (pv 0 0) w)) ∨
       (∃ s, g = FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 1 0) w) s))) ∨
       g = FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 2 0).
Definition tcb_C : bcs := BCs [pvar 0; pvar 1] tcb_P.

Lemma pwalk_pol x w : pt_pol x = true → pt_pol (pwalk x w) = true.
Proof. revert x. induction w as [|[i|] w IH]; intros x Hx; simpl; [done| |]; apply IH; done. Qed.

Lemma pwalk_nones x k : pwalk x (repeat None k) = pt_shift k x.
Proof.
  revert x. induction k as [|k IH]; intros x; simpl; [by rewrite pt_shift_0|].
  rewrite IH. destruct x. unfold pt_shift. simpl. f_equal. lia.
Qed.

Lemma st_off_polar c x : pt_off (pt_polar c x) = pt_off x.
Proof. by destruct c. Qed.

(** Program order along offsets, between any polarities. *)
Lemma glt_ofs_any E L x c c' k : 0 < k → glt E L (pt_polar c x) (pt_polar c' (pt_shift k x)).
Proof.
  intros Hk. destruct x as [n b o]. destruct c, c'; unfold pt_polar, pt_dual, pt_shift; simpl.
  - apply glt_ofs_pol. lia.
  - apply glt_ofs_dual. lia.
  - rewrite <-(negb_involutive b) at 2. apply glt_ofs_dual. lia.
  - apply glt_ofs_pol. lia.
Qed.

(** The zigzag of b enters at the points of b from α and leaves to the
    points of α and to z. A point of b at or above another one along
    offsets sits at the same walk, k successors later, so the leaving
    fact lands on α at that walk k successors later, and the facts of a
    and program order give the fact between the outer points. *)
Lemma tcb_ok W Ψ : (BCs [pvar 1] send_P, [pvar 0]) ∈ Ψ → cc_ok (seqs W Ψ) (slt W Ψ) tcb_C.
Proof.
  intros Hg.
  set (TL := glt (cc_up (seqs W Ψ)) (cc_up (slt W Ψ))).
  assert (∀ u c c' i, TL (pt_polar c (pwalk (pv 1 0) u)) (pt_polar c' (wstep (pwalk (pv 1 0) u) (Some i)))) as HA.
  { intros u c c' i.
    assert (slt W Ψ (pt_polar c (pwalk (pv 0 0) u)) (pt_polar c' (wstep (pwalk (pv 0 0) u) (Some i)))) as H.
    { eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0]
                (FLt (pt_polar c (pwalk (pv 0 0) u)) (pt_polar c' (wstep (pwalk (pv 0 0) u) (Some i)))));
        [done|exists u, c, c'; right; by exists i|fscp|fmwp]. }
    pose proof (glt_up (seqs W Ψ) _ _ _ H) as G. by rewrite !st_inst_polar, wstep_inst, pwalk_inst in G. }
  assert (∀ u c, TL (pt_polar c (pwalk (pv 1 0) u)) (pv 2 0)) as HZ.
  { intros u c.
    assert (slt W Ψ (pt_polar c (pwalk (pv 0 0) u)) (pv 1 0)) as H.
    { eapply (sl_hyp W Ψ [pvar 1] send_P [pvar 0] (FLt (pt_polar c (pwalk (pv 0 0) u)) (pv 1 0)));
        [done|exists u, c, true; by left|fscp|fmwp]. }
    pose proof (glt_up (seqs W Ψ) _ _ _ H) as G. by rewrite st_inst_polar, pwalk_inst in G. }
  assert (∀ w w' c d, pt_polar c (pwalk (pv 0 0) w) = pt_polar d (pwalk (pv 0 0) w') ∨
                       olt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar d (pwalk (pv 0 0) w')) →
            ∃ k, pwalk (pv 1 0) w' = pt_shift k (pwalk (pv 1 0) w)) as Hrel.
  { intros w w' c d H.
    assert (pt_name (pwalk (pv 0 0) w) = pt_name (pwalk (pv 0 0) w') ∧
            pt_off (pwalk (pv 0 0) w) ≤ pt_off (pwalk (pv 0 0) w')) as [En Eo].
    { destruct H as [E|[En Eo]].
      - pose proof (f_equal pt_name E) as En. pose proof (f_equal pt_off E) as Eo.
        rewrite !st_name_polar in En. rewrite !st_off_polar in Eo. split; [done|lia].
      - rewrite !st_name_polar in En. rewrite !st_off_polar in Eo. split; [done|lia]. }
    exists (pt_off (pwalk (pv 0 0) w') - pt_off (pwalk (pv 0 0) w)).
    assert (pwalk (pv 0 0) w' = pt_shift (pt_off (pwalk (pv 0 0) w') - pt_off (pwalk (pv 0 0) w)) (pwalk (pv 0 0) w)) as E.
    { pose proof (pwalk_pol (pv 0 0) w eq_refl) as P. pose proof (pwalk_pol (pv 0 0) w' eq_refl) as P'.
      destruct (pwalk (pv 0 0) w) as [n b o], (pwalk (pv 0 0) w') as [n' b' o'].
      unfold pt_shift. simpl in *. subst. f_equal. lia. }
    apply (f_equal (pt_inst (λ _, pv 1 0))) in E. rewrite pt_inst_shift, !pwalk_inst in E. exact E. }
  apply (cc_ok_out _ _ tcb_C olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po|intros x _; apply olt_dpo| | |].
  - intros a b (f & (w & c & c' & [-> | [(s & ->) | ->]]) & _ & E); discriminate E.
  - intros a b (f & (w & c & c' & [-> | [(s & ->) | ->]]) & _ & E); cbn [fact_map] in E;
      rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst in E; injection E as -> ->; right;
      rewrite ?st_root_polar, ?pt_payload_root, ?wstep_root, ?pwalk_root; cbn; auto.
  - intros u p q v (f & (w & c & c' & [-> | [(s & ->) | ->]]) & _ & E) (f' & (w' & d & d' & [-> | [(s' & ->) | ->]]) & _ & E')
      Hu Hp Hq Hv Hpq; cbn [fact_map] in E, E'; rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst in E;
      rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst in E'; injection E as -> ->; injection E' as -> ->;
      change (pt_inst (pup 1 (plist [pvar 0; pvar 1])) (pv 0 0)) with (pv 0 0) in *;
      change (pt_inst (pup 1 (plist [pvar 0; pvar 1])) (pv 1 0)) with (pv 1 0) in *;
      change (pt_inst (pup 1 (plist [pvar 0; pvar 1])) (pv 2 0)) with (pv 2 0) in *;
      try (exfalso; apply Hu; by rewrite st_root_polar, pwalk_root);
      try (exfalso; revert Hq; rewrite st_root_polar, pwalk_root; done).
    + fold TL. destruct (Hrel w w' c' d Hpq) as [k E]. rewrite E.
      destruct s' as [i|].
      * destruct k as [|k].
        -- rewrite pt_shift_0. apply HA.
        -- eapply glt_trans; [apply (glt_ofs_any _ _ _ c true (S k)); lia|].
           rewrite <-pwalk_nones, <-pwalk_app. apply HA.
      * cbn [wstep]. replace (pt_shift 1 (pt_shift k (pwalk (pv 1 0) w))) with (pt_shift (S k) (pwalk (pv 1 0) w)).
        2:{ destruct (pwalk (pv 1 0) w). unfold pt_shift. simpl. f_equal. lia. }
        apply glt_ofs_any. lia.
    + fold TL. apply HZ.
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
  assert (∀ w c c', slt W Ψ (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (pwalk (pv 0 0) w))) as Hab.
  { intros w c c'. eapply (sl_hyp W Ψ [pvar 1; pvar 2] tcb_P [pvar 0]
                             (FLt (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (pwalk (pv 0 0) w))));
      [inlist|exists w, c, c'; by left|fscp|fmwp]. }
  assert (∀ w s c c', slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 1 0) w) s))) as Hba.
  { intros w s c c'. eapply (sl_hyp W Ψ [pvar 1; pvar 2] tcb_P [pvar 0]
                               (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 1 0) w) s))));
      [inlist|exists w, c, c'; right; left; by exists s|fscp|fmwp]. }
  assert (∀ w c, slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pv 2 0)) as Hbz.
  { intros w c. eapply (sl_hyp W Ψ [pvar 1; pvar 2] tcb_P [pvar 0] (FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 2 0)));
      [inlist|exists w, c, true; by right; right|fscp|fmwp]. }
  assert (∀ w c, slt W Ψ (pt_polar c (pwalk (pv 1 0) w)) (pv 2 0)) as Haz.
  { intros w c. eapply (sl_hyp W Ψ [pvar 2] send_P [pvar 1] (FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 1 0)));
      [inlist|exists w, c, true; by left|fscp|fmwp]. }
  assert (∀ w i c c', slt W Ψ (pt_polar c (pwalk (pv 1 0) w)) (pt_polar c' (wstep (pwalk (pv 1 0) w) (Some i)))) as Haa.
  { intros w i c c'. eapply (sl_hyp W Ψ [pvar 2] send_P [pvar 1]
                          (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i)))));
      [inlist|exists w, c, c'; right; by exists i|fscp|fmwp]. }
  assert (∀ w i c c', slt W Ψ (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i)))) as Hbb.
  { intros w i c c'. eapply sl_trans; [apply (Hba w (Some i) c true)|]. rewrite <-!pwalk_snoc. apply Hab. }
  cbn. tstep.
  { (* the consumer *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 2 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold tm_cons. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pt_dual (pv 0 0))) 1 (BCs [pt_dual (pv 0 0); pv 2 0] after_P) (TSess SEnd (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pv 2 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pt_dual (pv 0 0))) 1 (BCs [pt_dual (pv 0 0); pv 2 0] after_P)
                  (TSess SEnd (pv 0 0)) _
                  (<[1:=Some (pv 3 0)]> (<[0:=Some (pv 3 0)]> ∅))
                  [(top_C0, [pvar 3]); (BCs [pvar 3] send_P, [pvar 2]); (BCs [pvar 2; pvar 3] tcb_P, [pvar 1]);
                   (BCs [pt_dual (pv 1 0); pv 3 0] after_P, [pv 0 0])]
                  [Some (TSess SEnd (pv 0 0)); None; None; None; None; None; None; None; None; None;
                   Some drain_ty; Some copy_ty]
                  (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 3 0). split; [done|]. right.
      eapply (sl_hyp W _ [pt_dual (pv 1 0); pv 3 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
        [inlist|right; exists [], true, true; by left|fsc|reflexivity].
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None (TSess (SSeq TreeD SEnd) (pt_dual (pv 0 0))) RD);
        [reflexivity| | |].
      + unfold RD. rewrite <-(drain_inst (pt_dual (pv 0 0)) (pv 2 0) SEnd).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None drain_body [pt_dual (pv 0 0); pv 2 0] [SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & c & c' & [-> | (i & ->)]) _; cbn [fact_map fact_holds];
            pnorm; [eapply Hbz|eapply Hbb].
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
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply (Hab [] true false)]. }
    unfold tm_copier. cbn. tstep; [tstep|]. cbn.
    set (RC := TEx (LPt (pt_dual (pv 1 0))) 2 (BCs [pt_dual (pv 1 0); pv 2 0] cafter_P)
                 (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0)))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None RC); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RC _ (Some (pv 2 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (pt_dual (pv 1 0))) 2 (BCs [pt_dual (pv 1 0); pv 2 0] cafter_P)
                  (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0))) _
                  (<[1:=Some (pv 4 0)]> (<[0:=Some (pv 4 0)]> ∅))
                  [(top_C0, [pvar 4]); (BCs [pvar 4] send_P, [pvar 3]); (BCs [pvar 3; pvar 4] tcb_P, [pvar 2]);
                   (BCs [pt_dual (pv 3 0); pv 4 0] cafter_P, [pv 0 0; pv 1 0])]
                  [Some (TProd (TSess SEnd (pv 0 0)) (TSess SEnd (pv 1 0)));
                   None; None; None; None; None; None; None; None; None; Some drain_ty; Some copy_ty]
                  (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (Ψc := [(top_C0, [pvar 4]); (BCs [pvar 4] send_P, [pvar 3]); (BCs [pvar 3; pvar 4] tcb_P, [pvar 2]);
                  (BCs [pt_dual (pv 3 0); pv 4 0] cafter_P, [pv 0 0; pv 1 0])]).
      assert (slt W Ψc (pv 0 0) (pt_dual (pv 1 0)) ∧ slt W Ψc (pv 0 0) (pv 4 0) ∧ slt W Ψc (pv 1 0) (pv 4 0))
        as (H01 & H0z & H1z).
      { split_and!.
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 0 0) (pt_dual (pv 1 0))));
            [inlist|right; exists [], true, false; by left|fsc|reflexivity].
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 0 0) (pv 3 0)));
            [inlist|right; exists [], true, true; by right; right; left|fsc|reflexivity].
        - eapply (sl_hyp W _ _ cafter_P _ (FLt (pv 1 0) (pv 3 0)));
            [inlist|right; exists [], true, true; by right; right; right|fsc|reflexivity]. }
      tstep; [tstep|]. cbn. tstep.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; exact H01|].
        exists (pv 4 0). split; [done|]. by right.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 0)) (TSess SEnd (pv 1 0))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 4 0). split; [done|]. by right.
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 2 0)) None
                (TProd (TSess (SSeq TreeD SEnd) (pt_dual (pv 1 0))) (TSess (SSeq TreeC SEnd) (pv 0 0))) RC);
        [reflexivity| | |].
      + unfold RC. rewrite <-(copy_inst (pt_dual (pv 1 0)) (pv 0 0) (pv 2 0) SEnd SEnd).
        apply (typed_force W _ _ _ _ _ _ 3 2 copy_C None copy_body [pt_dual (pv 1 0); pv 0 0; pv 2 0] [SEnd; SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & c & c' & [-> | [(s & ->) | [-> | ->]]]) _; cbn [fact_map fact_holds];
            pnorm; [eapply Hab|eapply Hba|eapply Haz|eapply Hbz].
        * constructor; [eapply skn_inst; [by right; left|by left|done]|].
          constructor; [eapply skn_inst; [by right; right; left|by left|done]|].
          constructor; [eapply skn_inst; [by left|by left|done]|constructor].
        * constructor; [apply hcontractive_end|constructor; [apply hcontractive_end|constructor]].
      + eapply (tv_pair W HW _ _ _ _ _ _ (TSess (SSeq TreeD SEnd) (pt_dual (pv 1 0)))); [reflexivity|tstep|tstep].
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. apply sle_refl, HW. }
  (* the producer: α[B], α[B]+1, (α[B]+1)[A] and its [A] *)
  unfold tm_prod. cbn.
  set (p1 := pt_dual (pwalk (pv 1 0) [Some true])).
  set (p2 := pt_dual (pwalk (pv 1 0) [Some true; None])).
  set (p3 := pt_dual (pwalk (pv 1 0) [Some true; None; Some false])).
  set (p4 := pt_dual (pwalk (pv 1 0) [Some true; None; Some false; Some false])).
  eapply (tv_appk W HW _ _ _ _ KClos _ (Some p4) (TSess SEnd p4));
    [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip SEnd) p4)).
  { apply teq_steq. split; [done|apply skip_l, hcontractive_end]. }
  eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some p3)
            (TSess (SPlus (SSeq SSkip SEnd) (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) SEnd)) p3));
    [|apply KTSel1, (Haa [Some true; None; Some false] false false true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq SSkip (SSeq TreeC SEnd)) p3)).
  { apply teq_steq. split; [done|]. eapply seq_trans; [apply skip_l|apply TreeC_seq].
    apply hcontractive_seq; [apply TreeC_hc|apply hcontractive_end]. }
  eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some p2)
            (TSess (SPlus (SSeq SSkip (SSeq TreeC SEnd))
                          (SSeq (SSeq (SSnd 0 TUnit) (SSeq TreeC TreeC)) (SSeq TreeC SEnd))) p2));
    [|apply KTSel1, (Haa [Some true; None] false false true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess (SSeq TreeC (SSeq TreeC SEnd)) p2)).
  { apply teq_steq. split; [done|apply TreeC_seq]. }
  eapply (tv_appk W HW _ _ _ _ KSend _ (Some p1)
            (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC SEnd))) p1)));
    [|apply (KTSend _ _ _ 0 TUnit (SSeq TreeC (SSeq TreeC SEnd)) p1); cbn; set_solver
     |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  tstep; [|tstep].
  eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 1 0))
            (TSess (SPlus (SSeq SSkip SEnd) (SSeq (SSnd 0 TUnit) (SSeq TreeC (SSeq TreeC SEnd)))) (pv 1 0)));
    [|apply KTSel2, (Haa [] true true true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  eapply t_conv; [|tstep]. apply teq_steq. split; [done|].
  eapply seq_trans; [apply TreeC_seq|]. apply seq_plus_cong; [apply seq_refl|apply node_snd, hcontractive_end].
Qed.

Theorem tree_deadlock_free : deadlock_free (∅, {[+ tree_main +]}).
Proof. apply (soundness_source 1 top_C0 _ TUnit (c0_acyclic_creation _ _ top_acyclic)); [constructor|apply tree_typed]. Qed.
