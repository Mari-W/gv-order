(** * Example: a fresh channel that acts several times between two points

    many : □(∀ι κ. {ι ≺ κ}. ∗ ⊸^⊥_⊤ Close@ι ⊗ Close@κ ⊸^κ_⊤ ∗)
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
    the existential result of new (sharp edges 99). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshBetween.

Set Default Proof Using "All".

(** !∗.!∗.Close *)
Definition Sdd : sty := SSnd 0 TUnit (SSnd 0 TUnit SEnd).

Definition fm_box : expr :=
  EBox (Lam (LetP (Var 0) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0)
                       (LetP (App ERecv (Var 1)) (LetU (Var 1) (recvclose (Var 0)))))))
    (LetU (App EClos (Var 3))
    (LetU (App EClos (App ESend (Pair EUnit (App ESend (Pair EUnit (Var 1))))))
          (App EClos (Var 2)))))))).

(** The constraint, in the context of the rule: the variable 0 is δ,
    the variables 1 and 2 are the outer points ι and κ. *)
Definition fm_facts (g : fact) : Prop :=
  g = FLt (pvar 1) (pvar 0) ∨ ∃ k, g = FLt (Pt (NVar 0) k) (pvar 2).

Definition fm_C : bcs := BCs [pvar 0; pvar 1] fm_facts.

Lemma fm_typed W F : world_wf W → typed W ∅ [] ∅ [] F fm_box fb_ty.
Proof.
  intros HW. unfold fm_box, fb_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pvar 1)) None 1); [set_solver|cbn; set_solver|].
  eapply t_wk; [apply lwk_cons, lwk_drop; [done|constructor]|].
  cbn. tstep; [tstep|]. cbn.
  refine (t_newfresh_open W _ _ ∅ _ _ _ _ Sdd fm_C _ _ _ _).
  { intros f [->|[k ->]] Hs.
    - left. eexists _, _. split; [done|]. split_and!; [by left|done|done|done].
    - right. eexists _, _. split; [done|]. split_and!; [right; by exists k|done|done|done]. }
  { apply (skn_ids2 W _ fb_C); [by left|done|done]. }
  { intros u p q v (Hf & _ & Hp & _) (Hf' & _ & _ & Hv) _.
    destruct Hf as [E|[k E]]; injection E as -> ->; [|done].
    destruct Hf' as [E|[k E]]; injection E as -> ->; [done|].
    cbn. hyp0 (pvar 0) (pvar 1). }
  rewrite tenv_pinst_empty, sf_pinst_fresh. cbn.
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  change (pt_inst (pshift 1) (pvar 1)) with (pvar 2).
  change (bcs_inst (pshift 1) (bcs_inst (pshift 2) fb_C)) with fb_C.
  set (Φ := fhyps_pinst (pshift 1) (<[1:=Some (pvar 1)]> (<[0:=None]> (fhyps_pinst (pshift 2) ∅)))).
  assert (Φ !! 1 = Some (Some (pvar 2))) as HΦ
    by (unfold Φ, fhyps_pinst; by rewrite lookup_fmap, lookup_insert_eq).
  set (C' := bcs_inst (pshift 1) fm_C).
  set (Ψ := [(fb_C, [pvar 1; pvar 2]); (C', [pvar 0])]).
  assert (slt W Ψ (pvar 1) (pvar 0)) as Hιδ.
  { apply (slt_hyp_fresh W Ψ C' (pvar 0) (pvar 1) (pvar 0)); [by right; left|by left|cbn; lia]. }
  assert (∀ k, slt W Ψ (Pt (NVar 0) k) (pvar 2)) as Hδκ.
  { intros k. apply (slt_hyp_fresh W Ψ C' (pvar 0) (Pt (NVar 0) k) (pvar 2));
      [by right; left|right; by exists k|cbn; lia]. }
  assert (slt W Ψ (pvar 1) (pvar 2)) as Hικ by hyp0 (pvar 0) (pvar 1).
  set (δ1 := Pt (NVar 0) 1). set (δ2 := Pt (NVar 0) 2).
  tstep.
  { (* the partner receives twice and closes *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some δ2) (Some (pvar 0)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { tstep; [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists δ2. split; [by rewrite lookup_insert_eq|right].
      apply sl_w. apply (wf_lt_po_n W (pvar 0) 1 HW). }
    cbn. tstep; [tstep|]. cbn. unfold recvclose. tstep.
    { tstep; [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists δ2. split; [by rewrite lookup_insert_eq|right]. apply (slt_po W _ δ1 HW). }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists δ2. split; [by rewrite lookup_insert_eq|apply sle_refl, HW]. }
  cbn. tstep.
  { (* close c at ι, holding d at δ and e at κ *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
    exists (pvar 2). split; [done|by right]. }
  cbn. tstep.
  { (* close (send ⟨∗, send ⟨∗, d⟩⟩) at δ, δ+1 and δ+2, holding e at κ *)
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some δ2) (TSess SEnd δ2) TUnit);
      [|apply KTClos|done|].
    - eapply (tv_appk W HW _ _ _ _ KSend _ (Some δ1)
                (TProd TUnit (TSess (SSnd 0 TUnit SEnd) δ1)) (TSess SEnd δ2));
        [|apply (KTSend _ _ _ 0 TUnit SEnd δ1); cbn; set_solver|kscope|].
      + tstep; [|tstep].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pvar 0))
                  (TProd TUnit (TSess Sdd (pvar 0))) (TSess (SSnd 0 TUnit SEnd) δ1));
          [|apply (KTSend _ _ _ 0 TUnit (SSnd 0 TUnit SEnd) (pvar 0)); cbn; set_solver|kscope|].
        * tstep; [tstep|tstep].
        * apply ubs_intro; [intros y Hy; mem_cases Hy; apply (Hδκ 0)|].
          exists (pvar 2). split; [done|right; apply (Hδκ 0)].
      + apply ubs_intro; [intros y Hy; mem_cases Hy; apply (Hδκ 1)|].
        exists (pvar 2). split; [done|right; apply (Hδκ 1)].
    - apply ubs_intro; [intros y Hy; mem_cases Hy; apply (Hδκ 2)|].
      exists (pvar 2). split; [done|right; apply (Hδκ 2)]. }
  (* close e at κ *)
  tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|].
  exists (pvar 2). split; [done|apply sle_refl, HW].
Qed.

(** ** The closed program, as in FreshBetween.v with the box [fm_box] *)

Definition fm_main : expr :=
  LetP (Pair fm_box EUnit) (LetU (Var 0)
    (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
        (App (App EForce (Var 5)) (Pair (Var 3) (Var 1)))))))).

(** main in the empty world, e bound by the encoded let of new (sharp
    edges 99). *)
Definition fm_main_ex : expr :=
  LetP (Pair fm_box EUnit) (LetU (Var 0)
    (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
        (App (App EForce (Var 5)) (Pair (Var 3) (Var 1)))))))).

Lemma fm_main_typed_fresh : styped ∅ [] [] (∅, None) fm_main_ex TUnit.
Proof.
  apply styped_Wpo. pose proof (proj1 Wpo_nil_strict') as HW.
  set (W := Wpo []) in *. unfold fm_main_ex.
  tstep.
  { tstep; [tstep|apply fm_typed, HW]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [] []); [constructor|set_solver|].
  assert (∀ σ, sf_pinst σ (∅, None) = ((∅ : gset point), (None : option fslot))) as Hsf
    by (intros σ; unfold sf_pinst; simpl; by rewrite set_map_empty).
  rewrite tenv_pinst_empty, Hsf. cbn.
  match goal with |- typed _ _ _ _ (_ :: _ :: _ :: _ :: _ :: Some ?T :: []) _ _ _ => change T with fb_ty end.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [pvar 0] []).
  { constructor; [|constructor]. right. exists (bcs_inst (pshift 1) (fresh_bcs [] [])), [pvar 0], (pvar 0).
    split_and!; [by left|by left|done]. }
  { intros l h _ Hh. by apply elem_of_nil in Hh. }
  rewrite tenv_pinst_empty, Hsf. cbn.
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  match goal with |- typed _ _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: Some ?T :: []) _ _ _ =>
    change T with fb_ty end.
  replace (fhyps_pinst (pshift 1) (fhyps_pinst (pshift 1) ∅)) with (∅ : fhyps)
    by (unfold fhyps_pinst; by rewrite !fmap_empty).
  set (Ψ := [(bcs_inst (pshift 1) (bcs_inst (pshift 1) (fresh_bcs [] [])), [pvar 1]);
             (bcs_inst (pshift 1) (fresh_bcs [pvar 0] []), [pvar 0])]).
  assert (slt W Ψ (pvar 1) (pvar 0)) as Hγε.
  { apply (slt_fresh_l W Ψ (pshift 1) [pvar 0] [] (pvar 0) (pvar 0)); [by right; left|by left]. }
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 1)) (Some (pvar 1)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pvar 1). split; [done|apply sle_refl, HW]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pvar 0). split; [done|apply sle_refl, HW]. }
  cbn. eapply (tv_app W HW _ _ _ _ _ _ (Some (pvar 0)) None
                 (TProd (TSess SEnd (pvar 1)) (TSess SEnd (pvar 0))) TUnit); [reflexivity| | |].
  - change (TLolli (Some (pvar 0)) None (TProd (TSess SEnd (pvar 1)) (TSess SEnd (pvar 0))) TUnit)
      with (ty_inst [pvar 1; pvar 0] fb_body).
    apply (typed_force W _ _ _ _ _ _ 2 fb_C None fb_body [pvar 1; pvar 0]); [done|done| | |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g -> _. exact Hγε.
    + constructor; [|constructor; [|constructor]].
      * right. eexists _, [pvar 1], (pvar 1). split_and!; [by left|by left|done].
      * right. eexists _, [pvar 0], (pvar 0). split_and!; [by right; left|by left|done].
  - cbn. tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The empty world. *)
Lemma fm_deadlock_free_empty : deadlock_free (∅, {[+ fm_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply fm_main_typed_fresh].
Qed.

(** [fm_main] is the program [fm_main_ex], so it types in the empty
    world too (sharp edges 105). *)
Lemma fm_deadlock_free : deadlock_free (∅, {[+ fm_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply fm_main_typed_fresh].
Qed.
