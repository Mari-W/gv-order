(** * A branch on data whose live side alternates (docs/extensions/data-dependent-worlds.md §3)

    The case node of db_main (examples/DataBranch.v) runs once, so one
    of its branches is dead, and an unsatisfiable fact on the dead side
    of the bit types it. Here the case node runs once per round, and
    both branches are live in alternate rounds.

      K = !(f = λp. let (t, q) = p in let (c, d) = q in
              case t of
                inl u ⇒ let () = u in
                        spawn (λv. let () = v in
                          (force f) ⟨inr ∗, ⟨send ⟨∗, c⟩, send ⟨∗, d⟩⟩⟩)
              | inr u ⇒ let () = u in
                        spawn (λv. let () = v in
                          let (d, w) = ⟨send ⟨∗, d⟩, ∗⟩ in let () = w in
                          (force f) ⟨inl ∗, ⟨send ⟨∗, c⟩, d⟩⟩))
      R = !(f = λc. let (u, c) = recv c in let () = u in
              spawn (λv. let () = v in (force f) c))
      alt_main = let (k, r) = ⟨K, R⟩ in let (c, c′) = new ∗ in let (d, d′) = new ∗ in
                 spawn ((force r) c′); spawn ((force r) d′); (force k) ⟨inl ∗, ⟨c, d⟩⟩

    Round j of K sends on c at ι+j and on d at κ+j, c first when j is
    even and d first when j is odd. The state t carries the order of
    every later round as a fact relative to the instance of K.

      t : ∃{altA(ι, κ)}.∗ ⊕ ∃{altB(ι, κ)}.∗

    altA is the alternating pattern that starts with c, altB the one
    that starts with d. Each branch opens its side, sends, and packs the
    other side at (ι+1, κ+1), which the opened facts give ([altB_next],
    [altA_next]). The box constraint of K is empty. main creates d under
    the pattern relative to c and packs the first state.

    [alt_typed] is the derivation, [alt_deadlock_free] follows from
    [soundness]. The construction carries a pattern whose futures,
    relative to the round, take two values. Section 3 of the design note
    conjectures that a pattern with infinitely many such futures has no
    derivation. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import examples.LitTools.
Set Default Proof Using "All".

Definition altA (g : fact) : Prop := ∃ n,
  g = FLt (pv 0 (2*n)) (pv 1 (2*n)) ∨ g = FLt (pv 1 (2*n)) (pv 0 (2*n+1)) ∨
  g = FLt (pv 1 (2*n+1)) (pv 0 (2*n+1)) ∨ g = FLt (pv 0 (2*n+1)) (pv 1 (2*n+2)).
Definition altB (g : fact) : Prop := ∃ n,
  g = FLt (pv 1 (2*n)) (pv 0 (2*n)) ∨ g = FLt (pv 0 (2*n)) (pv 1 (2*n+1)) ∨
  g = FLt (pv 0 (2*n+1)) (pv 1 (2*n+1)) ∨ g = FLt (pv 1 (2*n+1)) (pv 0 (2*n+2)).

Definition alt_T : ty :=
  TSum (TEx LNone 0 (BCs [pvar 0; pvar 1] altA) TUnit) (TEx LNone 0 (BCs [pvar 0; pvar 1] altB) TUnit).

Definition alt_K_body : ty :=
  TLolli None None (TProd alt_T (TProd (TSess Sb (pv 0 0)) (TSess Sb (pv 1 0)))) TUnit.
Definition alt_KC : bcs := BCs [] (λ _, False).
Definition alt_K_ty : ty := TBox 2 0 alt_KC (TLolli None None TUnit alt_K_body).

(** K = !(f = λp. let (t, q) = p in let (c, d) = q in
         case t of
           inl u ⇒ let () = u in spawn (λv. let () = v in (force f) ⟨inr ∗, ⟨send ⟨∗, c⟩, send ⟨∗, d⟩⟩⟩)
         | inr u ⇒ let () = u in spawn (λv. let () = v in
                     let (d, w) = ⟨send ⟨∗, d⟩, ∗⟩ in let () = w in (force f) ⟨inl ∗, ⟨send ⟨∗, c⟩, d⟩⟩)) *)
Definition alt_send (c : expr) : expr := App ESend (Pair EUnit c).

Definition alt_inl : expr :=
  LetU (Var 0) (App ESpawn (Lam (LetU (Var 0)
    (App (App EForce (Var 7)) (Pair (Inj2 EUnit) (Pair (alt_send (Var 3)) (alt_send (Var 2)))))))).

Definition alt_inr : expr :=
  LetU (Var 0) (App ESpawn (Lam (LetU (Var 0)
    (LetP (Pair (alt_send (Var 2)) EUnit) (LetU (Var 0)
      (App (App EForce (Var 9)) (Pair (Inj1 EUnit) (Pair (alt_send (Var 5)) (Var 1))))))))).

Definition alt_K : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Var 0) (Case (Var 3) alt_inl alt_inr)))).

Lemma alt_plist_nil x : pt_inst (plist []) x = x.
Proof. rewrite <-(pt_inst_pvar x) at 2. apply pt_inst_ext. intros a. unfold plist. simpl. f_equal. lia. Qed.

(** A ≺ fact of a hypothesis with no ι and outer points env. *)
Lemma alt_hyp_env_lt W Ψ env F f x y :
  (BCs env F, []) ∈ Ψ → F f → fact_scoped (length env) f →
  fact_map (pt_inst (pup 0 (plist env))) f = FLt x y → slt W Ψ x y.
Proof.
  intros Hg Hf Hs E. apply sl_h. exists (BCs env F), []. split; [done|].
  exists (FLt x y). split; [exists f; split_and!; [done|exact Hs|simpl; by rewrite E]|].
  simpl. by rewrite !alt_plist_nil.
Qed.

Lemma alt_sf_pinst_o σ o : sf_pinst σ (∅, o) = ((∅ : gset point), o).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

Lemma alt_fhyps_ins2 σ : fhyps_pinst σ (<[1:=None]> (<[0:=None]> ∅)) = <[1:=None]> (<[0:=None]> ∅).
Proof. unfold fhyps_pinst. by rewrite !fmap_insert, fmap_empty. Qed.

Ltac alt_envpt := unfold pt_inst, pup, plist, pt_shift; cbn; repeat (rewrite decide_False by lia); cbn; f_equal; (f_equal; lia).

(** The pattern from the next round, read from the opened pattern of this round. *)
Lemma altB_next W Ψ :
  (BCs [pvar 0; pvar 1] altA, []) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) (BCs [pv 0 1; pv 1 1] altB) [].
Proof.
  intros Hg g (f & Hf & Hs & ->).
  destruct Hf as (n & [->|[->|[->| ->]]]); cbn [fact_map fact_holds]; rewrite !alt_plist_nil.
  - eapply (alt_hyp_env_lt W Ψ _ altA (FLt (pv 1 (2*n+1)) (pv 0 (2*n+1)))); [done| |cbn; lia|alt_envpt].
    exists n. right; right; left. done.
  - eapply (alt_hyp_env_lt W Ψ _ altA (FLt (pv 0 (2*n+1)) (pv 1 (2*n+2)))); [done| |cbn; lia|alt_envpt].
    exists n. right; right; right. done.
  - eapply (alt_hyp_env_lt W Ψ _ altA (FLt (pv 0 (2*S n)) (pv 1 (2*S n)))); [done| |cbn; lia|alt_envpt].
    exists (S n). left. done.
  - eapply (alt_hyp_env_lt W Ψ _ altA (FLt (pv 1 (2*S n)) (pv 0 (2*S n+1)))); [done| |cbn; lia|alt_envpt].
    exists (S n). right; left. done.
Qed.

Lemma altA_next W Ψ :
  (BCs [pvar 0; pvar 1] altB, []) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) (BCs [pv 0 1; pv 1 1] altA) [].
Proof.
  intros Hg g (f & Hf & Hs & ->).
  destruct Hf as (n & [->|[->|[->| ->]]]); cbn [fact_map fact_holds]; rewrite !alt_plist_nil.
  - eapply (alt_hyp_env_lt W Ψ _ altB (FLt (pv 0 (2*n+1)) (pv 1 (2*n+1)))); [done| |cbn; lia|alt_envpt].
    exists n. right; right; left. done.
  - eapply (alt_hyp_env_lt W Ψ _ altB (FLt (pv 1 (2*n+1)) (pv 0 (2*n+2)))); [done| |cbn; lia|alt_envpt].
    exists n. right; right; right. done.
  - eapply (alt_hyp_env_lt W Ψ _ altB (FLt (pv 1 (2*S n)) (pv 0 (2*S n)))); [done| |cbn; lia|alt_envpt].
    exists (S n). left. done.
  - eapply (alt_hyp_env_lt W Ψ _ altB (FLt (pv 0 (2*S n)) (pv 1 (2*S n+1)))); [done| |cbn; lia|alt_envpt].
    exists (S n). right; left. done.
Qed.

Lemma alt_K_ty_scoped : pscoped 0 alt_K_ty.
Proof.
  cbn. repeat split; repeat (apply Forall_cons; split); try apply Forall_nil;
    try (intros ? Hv; injection Hv; lia).
  all: done.
Qed.

Lemma alt_K_typed W F : world_wf W → typed W ∅ [] ∅ [] F alt_K alt_K_ty.
Proof.
  intros HW. unfold alt_K, alt_K_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  change (lenv_pinst (pshift 2) [Some (TBox 2 0 alt_KC (TLolli None None TUnit alt_K_body))])
    with [Some (pinst_ty (pshift 2) alt_K_ty)].
  rewrite (pinst_closed _ alt_K_ty alt_K_ty_scoped).
  change (bcs_inst (pshift 2) alt_KC) with alt_KC. cbn. unfold alt_K_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ None None 1); [set_solver|cbn; set_solver|].
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ alt_T (TProd (TSess Sb (pv 0 0)) (TSess Sb (pv 1 0))));
    [reflexivity|tstep|].
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ (TSess Sb (pv 0 0)) (TSess Sb (pv 1 0)));
    [reflexivity|tstep|].
  cbn. eapply (tv_case W _ _ _ _ _ _ _ _ _ TUnit); [exact HW|reflexivity|tstep| |].
  - unfold alt_inl. cbn.
    apply (t_open W _ _ _ _ _ _ 0 LNone 0 (BCs [pvar 0; pvar 1] altA) TUnit TUnit);
      [done|intros Hu; exact Hu|].
    replace (hyps_inst (pshift 0) [(alt_KC, [pvar 0; pvar 1])]) with [(alt_KC, [pvar 0; pvar 1])]
      by reflexivity.
    change (bcs_inst (pshift 0) (BCs [pvar 0; pvar 1] altA)) with (BCs [pvar 0; pvar 1] altA).
    rewrite fhyps_pinst_empty, alt_fhyps_ins2, tenv_pinst_empty, alt_sf_pinst_o.
    change (pinst_ty (pshift 0) TUnit) with TUnit.
    unfold lenv_pinst. cbn [fmap list_fmap option_fmap option_map].
    rewrite (pinst_closed _ alt_K_ty alt_K_ty_scoped).
    change (pinst_ty (pshift 0) (TEx LNone 0 (BCs [pvar 0; pvar 1] altA) TUnit))
      with (TEx LNone 0 (BCs [pvar 0; pvar 1] altA) TUnit).
    change (pinst_ty (pshift 0) (TSess Sb (pv 1 0))) with (TSess Sb (pv 1 0)).
    change (pinst_ty (pshift 0) (TSess Sb (pv 0 0))) with (TSess Sb (pv 0 0)).
    cbn [insert list_insert].
    set (Ψ := [(alt_KC, [pvar 0; pvar 1])] ++ [(BCs [pvar 0; pvar 1] altA, ids 0)]).
    assert ((BCs [pvar 0; pvar 1] altA, []) ∈ Ψ) as Hg by (apply elem_of_app; right; by left).
    assert (slt W Ψ (pv 0 0) (pv 1 0)) as Hik.
    { eapply (alt_hyp_env_lt W Ψ _ altA (FLt (pv 0 0) (pv 1 0))); [done| |cbn; lia|alt_envpt].
      exists 0. by left. }
    assert (slt W Ψ (pv 1 0) (pv 0 1)) as Hki1.
    { eapply (alt_hyp_env_lt W Ψ _ altA (FLt (pv 1 0) (pv 0 1))); [done| |cbn; lia|alt_envpt].
      exists 0. by right; left. }
    tstep; [tstep|]. cbn.
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 0)) (Some (pv 0 0)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; exact Hik]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    + apply (typed_force0 W _ _ _ _ _ _ 2 alt_KC None alt_K_body [pv 0 1; pv 1 1]);
        [done|done| | |apply ubs_none|tstep].
      * apply bcs_hold_intro. intros g [].
      * apply (skn_ids2 W _ alt_KC); [by left|done|done].
    + match goal with |- typed _ _ _ _ _ _ _ ?T => change T with
        (TProd (TSum (TEx LNone 0 (BCs [pv 0 1; pv 1 1] altA) TUnit)
                     (TEx LNone 0 (BCs [pv 0 1; pv 1 1] altB) TUnit))
               (TProd (TSess Sb (pv 0 1)) (TSess Sb (pv 1 1)))) end.
      cbn [opt_heads fmap option_fmap option_map sf_union].
      tstep.
      * tstep.
        -- eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0))
                     (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) (pv 1 0)))).
           ++ tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
           ++ apply (KTSend _ _ _ 0 TUnit Sb (pv 1 0)). cbn. set_solver.
           ++ kscope.
           ++ apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hki1|].
              exists (pv 1 0). split; [done|]. apply sle_refl, HW.
        -- eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
                     (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) (pv 0 0)))).
           ++ tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
           ++ apply (KTSend _ _ _ 0 TUnit Sb (pv 0 0)). cbn. set_solver.
           ++ kscope.
           ++ apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hik|].
              exists (pv 1 0). split; [done|]. right. exact Hik.
      * apply t_inj2. apply (t_pack W _ _ _ _ _ _ LNone 0 (BCs [pv 0 1; pv 1 1] altB) TUnit []).
        -- done.
        -- constructor.
        -- apply altB_next. by right; left.
        -- by split.
        -- tstep.
    + apply ubs_none.
  - unfold alt_inr. cbn.
    apply (t_open W _ _ _ _ _ _ 0 LNone 0 (BCs [pvar 0; pvar 1] altB) TUnit TUnit);
      [done|intros Hu; exact Hu|].
    replace (hyps_inst (pshift 0) [(alt_KC, [pvar 0; pvar 1])]) with [(alt_KC, [pvar 0; pvar 1])]
      by reflexivity.
    change (bcs_inst (pshift 0) (BCs [pvar 0; pvar 1] altB)) with (BCs [pvar 0; pvar 1] altB).
    rewrite fhyps_pinst_empty, alt_fhyps_ins2, tenv_pinst_empty, alt_sf_pinst_o.
    change (pinst_ty (pshift 0) TUnit) with TUnit.
    unfold lenv_pinst. cbn [fmap list_fmap option_fmap option_map].
    rewrite (pinst_closed _ alt_K_ty alt_K_ty_scoped).
    change (pinst_ty (pshift 0) (TEx LNone 0 (BCs [pvar 0; pvar 1] altB) TUnit))
      with (TEx LNone 0 (BCs [pvar 0; pvar 1] altB) TUnit).
    change (pinst_ty (pshift 0) (TSess Sb (pv 1 0))) with (TSess Sb (pv 1 0)).
    change (pinst_ty (pshift 0) (TSess Sb (pv 0 0))) with (TSess Sb (pv 0 0)).
    cbn [insert list_insert].
    set (Ψ := [(alt_KC, [pvar 0; pvar 1])] ++ [(BCs [pvar 0; pvar 1] altB, ids 0)]).
    assert ((BCs [pvar 0; pvar 1] altB, []) ∈ Ψ) as Hg by (apply elem_of_app; right; by left).
    assert (slt W Ψ (pv 1 0) (pv 0 0)) as Hki.
    { eapply (alt_hyp_env_lt W Ψ _ altB (FLt (pv 1 0) (pv 0 0))); [done| |cbn; lia|alt_envpt].
      exists 0. by left. }
    assert (slt W Ψ (pv 0 0) (pv 1 1)) as Hik1.
    { eapply (alt_hyp_env_lt W Ψ _ altB (FLt (pv 0 0) (pv 1 1))); [done| |cbn; lia|alt_envpt].
      exists 0. by right; left. }
    tstep; [tstep|]. cbn.
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 0)) (Some (pv 1 0)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; exact Hki]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_letp W HW _ _ _ _ _ _ (TSess Sb (pv 1 1)) TUnit); [reflexivity| |].
    { tstep; [tstep|].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0))
                (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) (pv 1 0)))).
      - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      - apply (KTSend _ _ _ 0 TUnit Sb (pv 1 0)). cbn. set_solver.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hki|].
        exists (pv 0 0). split; [done|]. right. exact Hki. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    + apply (typed_force0 W _ _ _ _ _ _ 2 alt_KC None alt_K_body [pv 0 1; pv 1 1]);
        [done|done| | |apply ubs_none|tstep].
      * apply bcs_hold_intro. intros g [].
      * apply (skn_ids2 W _ alt_KC); [by left|done|done].
    + match goal with |- typed _ _ _ _ _ _ _ ?T => change T with
        (TProd (TSum (TEx LNone 0 (BCs [pv 0 1; pv 1 1] altA) TUnit)
                     (TEx LNone 0 (BCs [pv 0 1; pv 1 1] altB) TUnit))
               (TProd (TSess Sb (pv 0 1)) (TSess Sb (pv 1 1)))) end.
      cbn [opt_heads fmap option_fmap option_map sf_union].
      tstep.
      * tstep; [tstep|].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
                  (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) (pv 0 0)))).
        -- tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
        -- apply (KTSend _ _ _ 0 TUnit Sb (pv 0 0)). cbn. set_solver.
        -- kscope.
        -- apply ubs_intro; [intros y Hy; mem_cases Hy; exact Hik1|].
           exists (pv 0 0). split; [done|]. apply sle_refl, HW.
      * apply t_inj1. apply (t_pack W _ _ _ _ _ _ LNone 0 (BCs [pv 0 1; pv 1 1] altA) TUnit []).
        -- done.
        -- constructor.
        -- apply altA_next. by right; left.
        -- by split.
        -- tstep.
    + apply ubs_none.
Qed.

(** R = !(f = λc. let (u, c) = recv c in let () = u in spawn (λv. let () = v in (force f) c)) *)
Definition alt_R_body : ty := TLolli (Some (pv 0 0)) None (TSess Sa (pv 0 0)) TUnit.
Definition alt_RC : bcs := BCs [] (λ _, False).
Definition alt_R_ty : ty := TBox 1 0 alt_RC (TLolli None None TUnit alt_R_body).

Definition alt_R : expr :=
  EBox (Lam (LetP (App ERecv (Var 0)) (LetU (Var 1)
    (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 4)) (Var 1)))))))).

Lemma alt_R_ty_scoped : pscoped 0 alt_R_ty.
Proof. cbn. repeat split; try apply Forall_nil; try (intros ? Hv; injection Hv; lia); done. Qed.

Lemma alt_R_typed W F : world_wf W → typed W ∅ [] ∅ [] F alt_R alt_R_ty.
Proof.
  intros HW. unfold alt_R, alt_R_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  change (lenv_pinst (pshift 1) [Some (TBox 1 0 alt_RC (TLolli None None TUnit alt_R_body))])
    with [Some (pinst_ty (pshift 1) alt_R_ty)].
  rewrite (pinst_closed _ alt_R_ty alt_R_ty_scoped).
  change (bcs_inst (pshift 1) alt_RC) with alt_RC. cbn. unfold alt_R_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ TUnit (TSess Sa (pv 0 1))); [reflexivity| |].
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SSeq (SRcv 0 TUnit) Sa) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn. tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pv 0 1)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 1 alt_RC None alt_R_body [pv 0 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g [].
    + constructor; [eapply skn_inst; [by left|by left|done]|constructor].
  - cbn. tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW.
Qed.

Definition alt_Cd_facts (g : fact) : Prop := ∃ n,
  g = FLt (pv 1 (2*n)) (pv 0 (2*n)) ∨ g = FLt (pv 0 (2*n)) (pv 1 (2*n+1)) ∨
  g = FLt (pv 0 (2*n+1)) (pv 1 (2*n+1)) ∨ g = FLt (pv 1 (2*n+1)) (pv 0 (2*n+2)).
Definition alt_Cd : bcs := BCs [pvar 0] alt_Cd_facts.

Lemma alt_hyp_fresh_lt W Ψ C x u v a b :
  (C, [x]) ∈ Ψ → bc_facts C (FLt u v) → fact_scoped (S (length (bc_env C))) (FLt u v) →
  pt_inst (plist (x :: bc_env C)) u = a → pt_inst (plist (x :: bc_env C)) v = b → slt W Ψ a b.
Proof. intros ? ? ? <- <-. by apply slt_hyp_fresh. Qed.

Ltac alt_ptnorm := unfold pt_inst, pup, plist, pt_shift; cbn; repeat (rewrite decide_False by lia); cbn; f_equal; lia.

Definition alt_main : expr :=
  LetP (Pair alt_K alt_R) (let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 5)) (Var 3)))))
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 5)) (Var 1)))))
      (App (App EForce (Var 5)) (Pair (Inj1 EUnit) (Pair (Var 3) (Var 1)))))))).

Lemma alt_typed : styped ∅ [] [] (∅, None) alt_main TUnit.
Proof.
  apply styped_Wpo. pose proof (proj1 Wpo_nil_strict') as HW.
  set (W := Wpo []) in *. unfold alt_main.
  tstep.
  { tstep; [apply alt_R_typed, HW|apply alt_K_typed, HW]. }
  cbn.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ Sb [] []); [constructor|set_solver|].
  fresh_clean.
  refine (t_newfresh_open W _ _ ∅ _ _ _ _ Sb alt_Cd _ _ _ _).
  { intros f (n & [-> |[-> |[-> | ->]]]) Hs.
    - left. eexists _, _. split; [done|]. split_and!; [exists n; by left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [exists n; by right; left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [exists n; by right; right; left|done|done|done].
    - left. eexists _, _. split; [done|]. split_and!; [exists n; by right; right; right|done|done|done]. }
  { constructor; [|constructor]. eapply skn_inst; [by left|by left|done]. }
  { intros u p q v (Hf & _ & Hp & Hu) (Hf' & _ & Hq & Hv) [_ Hpq]%ple_inv.
    destruct Hf as (n & [E|[E|[E|E]]]); injection E as -> ->;
      try (exfalso; by apply Hu); try (cbn in Hp; discriminate).
    all: destruct Hf' as (m & [E|[E|[E|E]]]); injection E as -> ->;
      try (exfalso; by apply Hv); try (cbn in Hq; discriminate).
    all: cbn in Hpq; unfold fresh_outer; cbn; apply sl_w, wf_lt_same; [done|done|cbn; lia]. }
  fresh_clean.
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  set (Ψ := [(bcs_inst (pshift 1) (bcs_inst (pshift 1) (fresh_bcs [] [])), [pvar 1]);
             (bcs_inst (pshift 1) alt_Cd, [pvar 0])]).
  match goal with |- typed _ _ _ _ [Some ?A; Some ?B; None; None; Some ?A'; Some ?B'; None; None; Some ?D; Some ?E] _ _ _ =>
    change A with (TSess Sa (pvar 0)); change B with (TSess Sb (pvar 0));
    change A' with (TSess Sa (pvar 1)); change B' with (TSess Sb (pvar 1));
    change D with alt_R_ty; change E with alt_K_ty end.
  assert (bcs_hold (seqs W Ψ) (slt W Ψ) (BCs [pvar 1; pvar 0] altA) []) as HFA.
  { intros g (f & Hf & Hs & ->).
    destruct Hf as (n & [->|[->|[->| ->]]]); cbn [fact_map fact_holds]; rewrite !alt_plist_nil.
    - eapply (alt_hyp_fresh_lt W Ψ (bcs_inst (pshift 1) alt_Cd) (pvar 0) (pv 1 (2*n)) (pv 0 (2*n)));
        [by right; left|exists n; by left|cbn; lia|alt_ptnorm|alt_ptnorm].
    - eapply (alt_hyp_fresh_lt W Ψ (bcs_inst (pshift 1) alt_Cd) (pvar 0) (pv 0 (2*n)) (pv 1 (2*n+1)));
        [by right; left|exists n; by right; left|cbn; lia|alt_ptnorm|alt_ptnorm].
    - eapply (alt_hyp_fresh_lt W Ψ (bcs_inst (pshift 1) alt_Cd) (pvar 0) (pv 0 (2*n+1)) (pv 1 (2*n+1)));
        [by right; left|exists n; by right; right; left|cbn; lia|alt_ptnorm|alt_ptnorm].
    - eapply (alt_hyp_fresh_lt W Ψ (bcs_inst (pshift 1) alt_Cd) (pvar 0) (pv 1 (2*n+1)) (pv 0 (2*n+2)));
        [by right; left|exists n; by right; right; right|cbn; lia|alt_ptnorm|alt_ptnorm]. }
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 1)) (Some (pvar 1)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 alt_RC None alt_R_body [pvar 1]);
        [done|done| | |apply ubs_none|tstep].
      + apply bcs_hold_intro. intros g [].
      + constructor; [eapply skn_inst; [by left|by left|done]|constructor].
    - cbn. tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pvar 1). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 1 alt_RC None alt_R_body [pvar 0]);
        [done|done| | |apply ubs_none|tstep].
      + apply bcs_hold_intro. intros g [].
      + constructor; [eapply skn_inst; [by right; left|by left|done]|constructor].
    - cbn. tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pvar 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 alt_KC None alt_K_body [pvar 1; pvar 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g [].
    + constructor; [eapply skn_inst; [by left|by left|done]|].
      constructor; [eapply skn_inst; [by right; left|by left|done]|constructor].
  - match goal with |- typed _ _ _ _ _ _ _ ?T => change T with
      (TProd (TSum (TEx LNone 0 (BCs [pvar 1; pvar 0] altA) TUnit)
                   (TEx LNone 0 (BCs [pvar 1; pvar 0] altB) TUnit))
             (TProd (TSess Sb (pvar 1)) (TSess Sb (pvar 0)))) end.
    cbn [opt_heads fmap option_fmap option_map sf_union].
    tstep.
    + tstep; [tstep|tstep].
    + apply t_inj1. apply (t_pack W _ _ _ _ _ _ LNone 0 (BCs [pvar 1; pvar 0] altA) TUnit []).
      * done.
      * constructor.
      * exact HFA.
      * by split.
      * tstep.
  - apply ubs_none.
Qed.

Lemma alt_deadlock_free : deadlock_free (∅, {[+ alt_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply alt_typed].
Qed.

