(** * A loop over a µ body that mentions a session variable

      loop : □(∀κ ζ a. C. ∗ ⊸ ((µβ. &(a, ?∗;β))@κ ⊸^ζ ∃κ′≽κ. C′. a@κ′))
      loop c = case branch c of
                 Done c → c
                 More c → let (_, c) = recv c in loop c
      lp_go  = let (x, y) = new in
               spawn (λu. close (open (loop y)));
               close (select₁ (send ⟨∗, select₂ x⟩))

    The µ body mentions the session variable a of the box. The box body
    is typed at every hereditarily contractive instance s of a, where
    the channel has type µβ. &(s↑, ?∗;β) with s↑ = sren S s. Unrolling
    substitutes the µ for β and leaves s↑ to the fusion lemma of
    types/SinstFusion.v, which turns it back into s ([unroll_up]). C and
    C′ are the constraints of treeSum (TreeSum.v), the facts of every
    walk from κ below the ceiling ζ and below the points of its
    choices. A Done at κ packs the channel at κ[0], and a More at κ
    receives at κ[1], calls loop at κ[1]+1, opens the result and packs
    it again at κ.

    This is lp_main of mordido-perez.md (section "Gaps checked against
    the core") with a := Close and a loop of one More. Their type
    µβ.∀^S ι.&^ι{Done: a, More: ?^{ι+1}Unit;β} has the priority
    abstraction ∀^S ι inside the µ. The core has no priorities inside
    session types, so the abstraction becomes the points of the walk
    and the facts of C. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.TreeSum types.SinstFusion.

Set Default Proof Using "All".

(** µβ. &(a, ?∗;β), with β = 0 and a = 1 under the µ. *)
Definition LpD : sty := SMu (SWith (SVar 1) (SSeq (SRcv 0 TUnit) (SVar 0))).

(** The instance at s. *)
Definition LpI (s : sty) : sty := SMu (SWith (sren S s) (SSeq (SRcv 0 TUnit) (SVar 0))).

(** The client end µβ. ⊕(Close, !∗;β) at a := Close. *)
Definition LpC : sty := SMu (SPlus SEnd (SSeq (SSnd 0 TUnit) (SVar 0))).

Lemma LpD_inst s : sinst (slist [s]) LpD = LpI s.
Proof. reflexivity. Qed.

Lemma dual_LpC : dual LpC = LpI SEnd.
Proof. reflexivity. Qed.

Lemma LpI_contractive s : contractive (LpI s).
Proof. exact I. Qed.

(** The unfolding needs the fusion lemma at the free variable. *)
Lemma LpI_unroll s : seq (LpI s) (SWith s (SSeq (SRcv 0 TUnit) (LpI s))).
Proof.
  eapply seq_trans; [apply seq_mu, LpI_contractive|].
  unfold unroll. cbn [sinst sinst_ty]. rewrite unroll_up. apply seq_refl.
Qed.

Lemma LpC_unroll : seq LpC (SPlus SEnd (SSeq (SSnd 0 TUnit) LpC)).
Proof. by apply seq_unf. Qed.

(** ** loop *)

Definition lp_body : ty := TLolli (Some (pv 1 0)) None (TSess LpD (pv 0 0)) send_after.

Definition lp_ty : ty := TBox 2 1 send_C (TLolli None None TUnit lp_body).

Definition lp : expr :=
  EBox (Lam (Case (App EBra (Var 0))
    (Var 0)
    (LetP (App ERecv (Var 0)) (LetU (Var 1)
      (App (Lam (Var 0)) (App (App EForce (Var 4)) (Var 0))))))).

Lemma lp_ty_pscoped : pscoped 0 lp_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma lp_inst x z s :
  sinst_ty (slist [s]) (ty_inst [x; z] lp_body) =
  TLolli (Some z) None (TSess (LpI s) x)
    (TEx (LPt x) 1 (BCs [x; z] after_P) (TSess s (pv 0 0))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma lp_typed W F : world_wf W → typed W ∅ [] ∅ [] F lp lp_ty.
Proof.
  intros HW. unfold lp, lp_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  intros ss Hss Hhc. destruct ss as [|s [|]]; try discriminate Hss.
  rewrite Forall_singleton in Hhc. fold lp_ty.
  change (lenv_pinst (pshift 2) [Some lp_ty]) with [Some (pinst_ty (pshift 2) lp_ty)].
  rewrite (pinst_closed _ lp_ty) by apply lp_ty_pscoped.
  change (sinst_ty (slist [s]) lp_body) with
    (TLolli (Some (pv 1 0)) None (TSess (LpI s) (pv 0 0))
       (TEx (LPt (pv 0 0)) 1 after_C (TSess s (pv 0 0)))).
  change (bcs_inst (pshift 2) send_C) with send_C. cbn [hyps_inst app].
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. cstep.
  - eapply (tv_appk W HW _ _ _ _ KBra _ (Some (pv 0 0))
              (TSess (SWith s (SSeq (SRcv 0 TUnit) (LpI s))) (pv 0 0))).
    + eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply LpI_unroll].
    + apply KTBra; [hypb ([] : list (option bool)) false|hypb ([] : list (option bool)) true].
    + done.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hypw ([] : list (option bool)).
  - (* Done *)
    cbn. apply (t_pack W _ _ _ _ _ _ (LPt (pv 0 0)) 1 after_C (TSess s (pv 0 0)) [psl 0 false 0]).
    + done.
    + apply Forall_singleton. apply (skn_in W _ send_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done].
    + unfold after_C. apply bcs_hold_env. intros f [-> | (w & [-> | (i & ->)])] _;
        cbn [fact_map fact_holds]; rewrite ?wstep_inst, ?pwalk_inst.
      * hypb ([] : list (option bool)) false.
      * hypw (Some false :: w).
      * hypb (Some false :: w) i.
    + split; [|done]. intros y Hy. mem_cases Hy. right. hypb ([] : list (option bool)) false.
    + cbn. tstep.
  - (* More *)
    cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (psl 0 true 0))
                (TSess (SSeq (SRcv 0 TUnit) (LpI s)) (psl 0 true 0))).
      - tstep.
      - apply KTRecv.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. right. hypw [Some true]. }
    cbn. tstep; [tstep|]. cbn.
    set (R1 := TEx (LPt (psl 0 true 1)) 1 (BCs [psl 0 true 1; pv 1 0] after_P) (TSess s (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None R1); [reflexivity| | |].
    + eapply (tv_lam W HW _ _ _ _ _ R1 _ (Some (pv 1 0)) None 2); [set_solver|cbn; set_solver|].
      cbn. apply (tv_open W _ _ _ _ _ 0 (LPt (psl 0 true 1)) 1 (BCs [psl 0 true 1; pv 1 0] after_P)
                  (TSess s (pv 0 0)) _
                  (<[2:=Some (pv 2 0)]> (<[1:=Some (pv 2 0)]> (<[0:=None]> ∅)))
                  [(send_C, [pv 1 0; pv 2 0]); (BCs [psl 1 true 1; pv 2 0] after_P, [pv 0 0])]
                  [Some (TSess s (pv 0 0)); None; None; None; None; Some lp_ty]
                  (∅, Some (FVar 2))
                  (TEx (LPt (pv 1 0)) 1 (BCs [pv 1 0; pv 2 0] after_P) (TSess s (pv 0 0))));
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      set (Ψ2 := [(send_C, [pv 1 0; pv 2 0]); (BCs [psl 1 true 1; pv 2 0] after_P, [pv 0 0])]).
      assert (slt W Ψ2 (pv 1 0) (pv 0 0)) as Hch.
      { eapply sl_trans.
        { eapply (sl_hyp0 _ _ send_P _ (pv 0 0) (wstep (pv 0 0) (Some true)));
            [inlist|exists []; right; by exists true|fscw|reflexivity|reflexivity]. }
        eapply sl_trans; [apply (slt_po W _ (psl 1 true 0) HW)|].
        eapply (sl_hyp W _ [psl 1 true 1; pv 2 0] after_P [pv 0 0] (FLt (pv 1 0) (pv 0 0)));
          [inlist|by left|fsc|reflexivity]. }
      apply (t_pack W _ _ _ _ _ _ (LPt (pv 1 0)) 1 (BCs [pv 1 0; pv 2 0] after_P) (TSess s (pv 0 0)) [pv 0 0]).
      * done.
      * apply Forall_singleton.
        apply (skn_in W _ (BCs [psl 1 true 1; pv 2 0] after_P) [pv 0 0] (pv 0 0)); [inlist|by left|done].
      * apply bcs_hold_env. intros f [-> | (w & [-> | (i & ->)])] _;
          cbn [fact_map fact_holds]; rewrite ?wstep_inst, ?pwalk_inst.
        -- exact Hch.
        -- hypaw [psl 1 true 1; pv 2 0] [pv 0 0] w.
        -- hypab [psl 1 true 1; pv 2 0] [pv 0 0] w i.
      * split; [|done]. intros y Hy. mem_cases Hy. right. exact Hch.
      * cbn. tstep.
    + eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None (TSess (LpI s) (psl 0 true 1)) R1);
        [reflexivity| | |].
      * unfold R1. rewrite <-(lp_inst (psl 0 true 1) (pv 1 0) s).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None lp_body [psl 0 true 1; pv 1 0] [s]);
          [done|done| | |done| |apply ubs_none|tstep].
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

(** ** The closed program lp_go

    The client selects More, sends ∗, selects Done and closes. Both
    ends live at the point α of c, created with the facts of C at α and
    z ([tca_C] of TreeCopy.v). *)

Definition lp_srv : expr :=
  LetU (Var 0) (App (Lam (App EClos (Var 0))) (App (App EForce (Var 3)) (Var 1))).

Definition lp_cli : expr := App EClos (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 1))))).

Definition lp_go : expr :=
  LetP (Pair lp lp) (let_new_pair (LetU (App ESpawn (Lam lp_srv)) lp_cli)).

(** The client's walk: select₂, send, select₁. *)
Definition lp_cw : list (option bool) := [Some true; None; Some false].
Definition lpp (k : nat) : point := pwalk (pv 0 0) (take k lp_cw).

Lemma lp_go_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) lp_go TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold lp_go.
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply lp_typed, HW|exact HWs|apply lp_typed, HW]. }
  cbn. apply (t_new_open W _ _ ∅ _ _ _ _ LpC tca_C); [apply tca_ok|..].
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
  { (* the loop *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    unfold lp_srv. cbn. tstep; [tstep|]. cbn.
    set (RD := TEx (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 1 0] after_P) (TSess SEnd (pv 0 0))).
    eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None RD); [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ RD _ (Some (pv 1 0)) None 1); [set_solver|cbn; set_solver|].
      cbn. eapply (tv_open W _ _ _ _ _ 0 (LPt (pv 0 0)) 1 (BCs [pv 0 0; pv 1 0] after_P)
                  (TSess SEnd (pv 0 0)) _
                  (<[1:=Some (pv 2 0)]> (<[0:=Some (pv 2 0)]> ∅))
                  [(top_C0, [pvar 2]); (BCs [pvar 2] send_P, [pvar 1]); (BCs [pv 1 0; pv 2 0] after_P, [pv 0 0])]
                  _ (∅, Some (FVar 1)) TUnit);
        [reflexivity|intros []|reflexivity|reflexivity|reflexivity|apply sf_pinst_empty|reflexivity|].
      eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 0)) (TSess SEnd (pv 0 0))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 0). split; [done|]. right.
      eapply (sl_hyp W _ [pv 1 0; pv 2 0] after_P [pv 0 0] (FLt (pv 0 0) (pv 2 0)));
        [inlist|right; exists []; by left|fsc|reflexivity].
    - eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 1 0)) None (TSess (LpI SEnd) (pv 0 0)) RD);
        [reflexivity| | |].
      + unfold RD. rewrite <-(lp_inst (pv 0 0) (pv 1 0) SEnd).
        apply (typed_force W _ _ _ _ _ _ 2 1 send_C None lp_body [pv 0 0; pv 1 0] [SEnd]);
          [done|done| | |done| |apply ubs_none|tstep].
        * apply bcs_hold_intro. intros g (w & [-> | (i & ->)]) _; cbn [fact_map fact_holds];
            rewrite ?wstep_inst, ?pwalk_inst; [apply Haz|apply Haa].
        * constructor; [eapply skn_inst; [by right; left|by left|done]|].
          constructor; [eapply skn_inst; [by left|by left|done]|constructor].
        * apply Forall_singleton, hcontractive_end.
      + rewrite <-dual_LpC. tstep.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 0). split; [done|]. apply sle_refl, HW.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  (* the client *)
  unfold lp_cli. cbn.
  eapply (tv_appk W HW _ _ _ _ KClos _ (Some (lpp 3)) (TSess SEnd (lpp 3)));
    [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  eapply (tv_appk W HW _ _ _ _ KSel1 _ (Some (lpp 2)) (TSess (SPlus SEnd (SSeq (SSnd 0 TUnit) LpC)) (lpp 2)));
    [|apply KTSel1, (Haa (take 2 lp_cw) false)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  apply (t_conv W _ _ _ _ _ _ (TSess LpC (lpp 2))).
  { apply teq_steq. split; [done|apply LpC_unroll]. }
  eapply (tv_appk W HW _ _ _ _ KSend _ (Some (lpp 1))
            (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) LpC) (lpp 1))));
    [|apply (KTSend _ _ _ 0 TUnit LpC (lpp 1)); cbn; set_solver
     |kscope|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  tstep; [|tstep].
  eapply (tv_appk W HW _ _ _ _ KSel2 _ (Some (pv 0 0)) (TSess (SPlus SEnd (SSeq (SSnd 0 TUnit) LpC)) (pv 0 0)));
    [|apply KTSel2, (Haa [] true)|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  eapply t_conv; [|tstep]. apply teq_steq. split; [done|apply LpC_unroll].
Qed.

Theorem lp_deadlock_free : deadlock_free (∅, {[+ lp_go +]}).
Proof.
  apply (soundness_source 1 top_C0 _ TUnit (c0_acyclic_creation _ _ top_acyclic));
    [constructor|apply lp_go_typed].
Qed.
