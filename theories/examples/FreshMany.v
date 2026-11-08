(** * Example: a channel that acts several times between two points

    many : □(∀ι κ. {ι ≺ κ}. ∗ ⊸ Close@ι ⊗ Close@κ ⊸^κ ∗)
    many = !(f = λp. let (c, e) = p in
                     let q = new ∗ in let (d, d′) = q in
                     let () = spawn (λu. let () = u in
                                         let (v, d′) = recv d′ in let () = v in
                                         recvclose d′) in
                     let () = close c in
                     let () = close (send ⟨∗, send ⟨∗, d⟩⟩) in close e)

    d acts at δ, δ+1 and δ+2 while the thread holds e at κ, and close c
    at ι holds d at δ. The general E-NewFresh creates d with the
    infinite constraint {ι ≺ δ} ∪ {δ+k ≺ κ ∣ k ∈ ℕ}. Betweenness asks
    ι ≺ κ for the facts ι ≺ δ and δ+k ≺ κ, because δ+k lies after δ in
    program order, and the box hypothesis gives it (sharp edges 93).
    The list form L ≺ ι ≺ H could not state δ+1 ≺ κ. E-Open on q opens
    the existential result of new (sharp edges 99).

    With end points the thread keeps d at δ and the partner acts on d′
    at δ̄. close c asks ι ≺ δ̄ and the sends ask δ+k ≺ κ̄ besides
    δ+k ≺ κ. The fact ι ≺ δ̄ meets δ+k ≺ κ and δ+k ≺ κ̄ in betweenness
    through δ̄ ≺ δ+1, and the box constraint {ι ≺ κ, ι ≺ κ̄} of
    FreshBetween.v gives both.

    Under the constant world (sharp edges 172) d is created with new@δ
    at the field point δ = ι[0], and the box type [fm_ty] states the
    facts of δ, all infinitely many of them ([fmx_C]). main states them
    for its top-level points ([fm_Ψ]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshBetween.

Set Default Proof Using "All".

(** !∗.!∗.Close *)
Definition Sdd : sty := SSeq (SSnd 0 TUnit) (SSeq (SSnd 0 TUnit) SEnd).

Definition fm_box : expr :=
  EBox (Lam (LetP (Var 0) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0)
                       (LetP (App ERecv (Var 1)) (LetU (Var 1) (recvclose (Var 0)))))))
    (LetU (App EClos (Var 3))
    (LetU (App EClos (App ESend (Pair EUnit (App ESend (Pair EUnit (Var 1))))))
          (App EClos (Var 2)))))))).

(** Under the constant world (sharp edges 172) d is created with new@δ
    at the field point δ = ι[0], as in FreshBetween.v. The box
    constraint states the facts of δ, infinitely many:
    {ι ≺ κ, ι ≺ κ̄, ι ≺ δ̄} ∪ {δ+k ≺ κ, δ+k ≺ κ̄ ∣ k ∈ ℕ}. *)
Abbreviation fmd k := (Pt (NPayload (NVar 0) 0 0) k).

Definition fmx_P (g : fact) : Prop :=
  g = FLt (pvar 0) (pvar 1) ∨ g = FLt (pvar 0) (pt_dual (pvar 1)) ∨ g = FLt (pvar 0) (pt_dual (fmd 0)) ∨
  ∃ k, g = FLt (fmd k) (pvar 1) ∨ g = FLt (fmd k) (pt_dual (pvar 1)).
Definition fmx_C : bcs := BCs [] fmx_P.

Definition fm_ty : ty := TBox 2 0 fmx_C (TLolli None None TUnit fb_body).

Lemma fm_typed W F : strict W → typed W ∅ [] ∅ [] F fm_box fm_ty.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold fm_box, fm_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pvar 1)) None 1); [set_solver|cbn; set_solver|].
  eapply t_weak; [apply lwk_cons, lwk_drop; [done|constructor]|].
  cbn. tstep; [tstep|]. cbn.
  change (bcs_inst (pshift 2) fmx_C) with fmx_C.
  apply (t_new_at W _ _ _ _ _ _ _ Sdd (fmd 0) HWs);
    [eapply (skn_in W _ _ [pvar 0; pvar 1] (pvar 0)); [by left|by left|done]|].
  cbn.
  set (Ψ := [(fmx_C, [pvar 0; pvar 1])]).
  assert (slt W Ψ (pvar 0) (pt_dual (fmd 0))) as Hιδ.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (pt_dual (fmd 0))); [by left|by right; right; left|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ k, slt W Ψ (fmd k) (pvar 1)) as Hδκ.
  { intros k. eapply (sl_hyp0 _ _ _ _ (fmd k) (pvar 1));
      [by left|right; right; right; exists k; by left|cbn; lia|reflexivity|reflexivity]. }
  assert (∀ k, slt W Ψ (fmd k) (pt_dual (pvar 1))) as Hδκ'.
  { intros k. eapply (sl_hyp0 _ _ _ _ (fmd k) (pt_dual (pvar 1)));
      [by left|right; right; right; exists k; by right|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (pvar 0) (pvar 1)) as Hικ.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (pvar 1)); [by left|by left|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (pvar 0) (pt_dual (pvar 1))) as Hικ'.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (pt_dual (pvar 1))); [by left|by right; left|cbn; lia|reflexivity|reflexivity]. }
  set (δ0 := fmd 0). set (δ1 := fmd 1). set (δ2 := fmd 2).
  tstep.
  { (* the partner receives twice and closes *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual δ2)) (Some δ0) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { tstep; [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual δ2). split; [by rewrite lookup_insert_eq|right].
      apply sl_w. apply (wf_lt_po_n W (pt_dual δ0) 1 HW). }
    cbn. tstep; [tstep|]. cbn. unfold recvclose. tstep.
    { tstep; [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual δ2). split; [by rewrite lookup_insert_eq|right]. apply (slt_po W _ (pt_dual δ1) HW). }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual δ2). split; [by rewrite lookup_insert_eq|apply sle_refl, HW]. }
  cbn. tstep.
  { (* close c at ι, holding d at δ and e at κ *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
    exists (pvar 1). split; [done|by right]. }
  cbn. tstep.
  { (* close (send ⟨∗, send ⟨∗, d⟩⟩) at δ, δ+1 and δ+2, holding e at κ *)
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some δ2) (TSess SEnd δ2) TUnit);
      [|apply KTClos|done|].
    - eapply (tv_appk W HW _ _ _ _ KSend _ (Some δ1)
                (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) δ1)) (TSess SEnd δ2));
        [|apply (KTSend _ _ _ 0 TUnit SEnd δ1); cbn; set_solver|kscope|].
      + tstep; [|tstep].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some δ0)
                  (TProd TUnit (TSess Sdd δ0)) (TSess (SSeq (SSnd 0 TUnit) SEnd) δ1));
          [|apply (KTSend _ _ _ 0 TUnit (SSeq (SSnd 0 TUnit) SEnd) δ0); cbn; set_solver|kscope|].
        * tstep; [tstep|tstep].
        * apply ubs_intro; [intros y Hy; mem_cases Hy; apply (Hδκ' 0)|].
          exists (pvar 1). split; [done|right; apply (Hδκ 0)].
      + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (Hδκ' 1)|].
        exists (pvar 1). split; [done|right; apply (Hδκ 1)].
    - apply ubs_intro; [intros y Hy; mem_cases Hy; apply (Hδκ' 2)|].
      exists (pvar 1). split; [done|right; apply (Hδκ 2)]. }
  (* close e at κ *)
  tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|].
  exists (pvar 1). split; [done|apply sle_refl, HW].
Qed.

(** ** The closed program, as in FreshBetween.v with the box [fm_box] *)

Definition fm_main : expr :=
  LetP (Pair fm_box EUnit) (LetU (Var 0)
    (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
        (App (App EForce (Var 5)) (Pair (Var 3) (Var 1)))))))).

(** main under its top-level points γ and ε ([fm_Ψ], sharp edges 172).
    γ is created with γ ≺ (γ[0])‾ ([fbg_C] of FreshBetween.v), ε with
    γ ≺ ε at all polarities and γ[0]+k ≺ ε, ε̄ for every k. e is bound
    by the encoded let of new (sharp edges 99). *)
Definition fm_main_ex : expr :=
  LetP (Pair fm_box EUnit) (LetU (Var 0)
    (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
        (App (App EForce (Var 5)) (Pair (Var 3) (Var 1)))))))).

(** The creation constraint of ε = 0, with γ = 1 outside. *)
Definition fme_P (g : fact) : Prop :=
  (∃ b c, g = FLt (pt_polar b (pvar 1)) (pt_polar c (pvar 0))) ∨
  ∃ k c, g = FLt (Pt (NPayload (NVar 1) 0 0) k) (pt_polar c (pvar 0)).
Definition fme_C : bcs := BCs [pvar 0] fme_P.

Definition fm_Ψ : hyps :=
  hyps_inst (pshift 1) (hyps_inst (pshift 1) [] ++ [(bcs_inst (pshift 1) fbg_C, ids 1)]) ++
    [(bcs_inst (pshift 1) fme_C, ids 1)].

Lemma fm_created : created (Wpo []) fm_Ψ.
Proof.
  apply created_fresh; [apply created_snoc; [constructor|apply fbg_ok|constructor]| | |].
  - intros f [(b & c & ->)|(k & c & ->)] Hs; left; eexists _, _; (split; [done|]).
    + split_and!; [left; by exists b, c|done|by destruct c|by destruct b].
    + split_and!; [right; by exists k, c|done|by destruct c|done].
  - cbn. constructor; [|constructor].
    right. exists (bcs_inst (pshift 1) fbg_C), [pvar 0], (pvar 0). split_and!; [by left|by left|done].
  - intros u p q v _ (Hf & _ & Hq & Hv) _.
    destruct Hf as [(b & c & E)|(k & c & E)]; injection E as -> ->; [by destruct b|done].
Qed.

Lemma fm_main_typed_fresh : styped ∅ fm_Ψ [] (∅, None) fm_main_ex TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  set (W := Wpo []) in *. unfold fm_main_ex, fm_Ψ.
  tstep.
  { tstep; [tstep|apply typed_hyps_nil; [exact HWs|apply fm_typed, HWs]]. }
  cbn. tstep; [tstep|]. cbn.
  new_top HWs SEnd (pvar 1). new_top HWs SEnd (pvar 0).
  cbn.
  match goal with |- typed _ _ ?Q _ _ _ _ _ => set (Ψ := Q) end.
  assert ((bcs_inst (pshift 1) fme_C, [pvar 0]) ∈ Ψ) as Hin by (by right; left).
  assert (∀ b c, slt W Ψ (pt_polar b (pvar 1)) (pt_polar c (pvar 0))) as Hγε.
  { intros b c. pose proof (slt_hyp_fresh W Ψ _ (pvar 0) (pt_polar b (pvar 1)) (pt_polar c (pvar 0)) Hin)
      as H. destruct b, c; apply H; first [left; eexists _, _; reflexivity|cbn; lia]. }
  assert (∀ k, slt W Ψ (Pt (NPayload (NVar 1) 0 0) k) (pvar 0)) as Hdε.
  { intros k. pose proof (slt_hyp_fresh W Ψ _ (pvar 0) (Pt (NPayload (NVar 1) 0 0) k) (pvar 0) Hin) as H.
    apply H; [right; exists k, true; reflexivity|cbn; lia]. }
  assert (∀ k, slt W Ψ (Pt (NPayload (NVar 1) 0 0) k) (pt_dual (pvar 0))) as Hdε'.
  { intros k. pose proof (slt_hyp_fresh W Ψ _ (pvar 0) (Pt (NPayload (NVar 1) 0 0) k) (pt_dual (pvar 0)) Hin)
      as H. apply H; [right; exists k, false; reflexivity|cbn; lia]. }
  assert (slt W Ψ (pvar 1) (pt_dual (Pt (NPayload (NVar 1) 0 0) 0))) as Hγd.
  { eapply (sl_hyp0 _ _ fbg_P [pvar 1] (pvar 0) (pt_dual fbd)); [by left|done|cbn; lia|reflexivity|reflexivity]. }
  pose proof (Hγε true true) as Hγε1. pose proof (Hγε true false) as Hγε2. cbn [pt_polar] in *.
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pvar 1))) (Some (pvar 1)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (pvar 1)). split; [done|apply sle_refl, HW]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pvar 0))) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (pvar 0)). split; [done|apply sle_refl, HW]. }
  cbn. eapply (tv_app W HW _ _ _ _ _ _ (Some (pvar 0)) None
                 (TProd (TSess SEnd (pvar 1)) (TSess SEnd (pvar 0))) TUnit); [reflexivity| | |].
  - change (TLolli (Some (pvar 0)) None (TProd (TSess SEnd (pvar 1)) (TSess SEnd (pvar 0))) TUnit)
      with (ty_inst [pvar 1; pvar 0] fb_body).
    apply (typed_force0 W _ _ _ _ _ _ 2 fmx_C None fb_body [pvar 1; pvar 0]); [done|done| | |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g [-> |[-> |[-> |(k & [-> | ->])]]] _; cbn;
        [exact Hγε1|exact Hγε2|exact Hγd|apply Hdε|apply Hdε'].
    + constructor; [|constructor; [|constructor]].
      * right. eexists _, [pvar 1], (pvar 1). split_and!; [by left|by left|done].
      * right. eexists _, [pvar 0], (pvar 0). split_and!; [by right; left|by left|done].
  - cbn. tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The empty world. *)
Lemma fm_deadlock_free_empty : deadlock_free (∅, {[+ fm_main_ex +]}).
Proof.
  apply (soundness_created_s fm_Ψ _ TUnit fm_created); [constructor|apply fm_main_typed_fresh].
Qed.

(** [fm_main] is the program [fm_main_ex], so it types in the empty
    world too (sharp edges 105). *)
Lemma fm_deadlock_free : deadlock_free (∅, {[+ fm_main +]}).
Proof.
  apply (soundness_created_s fm_Ψ _ TUnit fm_created); [constructor|apply fm_main_typed_fresh].
Qed.
