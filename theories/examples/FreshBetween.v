(** * Example: a channel created between two box arguments (E-NewFresh)

    between : □(∀ι κ. {ι ≺ κ}. ∗ ⊸^⊥_⊤ Close@ι ⊗ Close@κ ⊸^κ_⊤ ∗)
    between = !(f = λp. let (c, e) = p in
                        let q = new ∗ in let (d, d′) = q in
                        let () = spawn (λu. let () = u in close d′) in
                        let () = close c in let () = close d in close e)

    close c blocks at ι while the thread holds d and e, close d blocks
    at the point δ of d while it holds e. So δ needs ι ≺ δ ≺ κ. No
    point built from ι and κ lies there. ι + 1 ≺ κ does not follow from
    ι ≺ κ, and a carried root of ι or κ is unrelated to both. E-NewFresh
    creates d at a fresh point δ with ι ≺ δ ≺ κ, which betweenness
    allows because the box hypothesis gives ι ≺ κ (sharp edges 90).
    new returns ∃δ. C. Close@δ ⊗ Close@δ, and E-Open on q opens it
    (sharp edges 99).

    main creates c at (0, 0) and e at (1, 0) in the world with
    (0, 0) ≺ (1, 0), spawns the partners that close the other ends,
    and calls the box on c and e. [fb_deadlock_free] gets deadlock
    freedom from [soundness]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition fb_C : bcs := BCs [] (λ g, g = FLt (pvar 0) (pvar 1)).

Definition fb_body : ty :=
  TLolli (Some (pvar 1)) None (TProd (TSess SEnd (pvar 0)) (TSess SEnd (pvar 1))) TUnit.

Definition fb_ty : ty := TBox 2 fb_C (TLolli None None TUnit fb_body).

Definition fb_box : expr :=
  EBox (Lam (LetP (Var 0) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
    (LetU (App EClos (Var 3))
    (LetU (App EClos (Var 1))
          (App EClos (Var 2)))))))).

Lemma fb_typed W F : world_wf W → typed W ∅ [] ∅ [] F fb_box fb_ty.
Proof.
  intros HW. unfold fb_box, fb_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pvar 1)) None 1); [set_solver|cbn; set_solver|].
  eapply t_wk; [apply lwk_cons, lwk_drop; [done|constructor]|].
  cbn. tstep; [tstep|]. cbn.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [pvar 0] [pvar 1]).
  { apply (skn_ids2 W _ fb_C); [by left|done|done]. }
  { intros l h Hl Hh. apply list_elem_of_singleton in Hl as ->.
    apply list_elem_of_singleton in Hh as ->. hyp0 (pvar 0) (pvar 1). }
  rewrite tenv_pinst_empty, sf_pinst_fresh. cbn.
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  change (pt_inst (pshift 1) (pvar 1)) with (pvar 2).
  change (bcs_inst (pshift 1) (bcs_inst (pshift 2) fb_C)) with fb_C.
  set (Φ := fhyps_pinst (pshift 1) (<[1:=Some (pvar 1)]> (<[0:=None]> (fhyps_pinst (pshift 2) ∅)))).
  assert (Φ !! 1 = Some (Some (pvar 2))) as HΦ
    by (unfold Φ, fhyps_pinst; by rewrite lookup_fmap, lookup_insert_eq).
  set (Ψ := [(fb_C, [pvar 1; pvar 2]); (bcs_inst (pshift 1) (fresh_bcs [pvar 0] [pvar 1]), [pvar 0])]).
  (* the three facts: ι ≺ δ, δ ≺ κ, ι ≺ κ *)
  assert (slt W Ψ (pvar 1) (pvar 0)) as Hιδ.
  { apply (slt_fresh_l W Ψ (pshift 1) [pvar 0] [pvar 1] (pvar 0) (pvar 0));
      [by right; left|by left]. }
  assert (slt W Ψ (pvar 0) (pvar 2)) as Hδκ.
  { apply (slt_fresh_r W Ψ (pshift 1) [pvar 0] [pvar 1] (pvar 0) (pvar 1));
      [by right; left|by left]. }
  assert (slt W Ψ (pvar 1) (pvar 2)) as Hικ by hyp0 (pvar 0) (pvar 1).
  tstep.
  { (* spawn (λu. let () = u in close d′) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pvar 0)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pvar 0). split; [by rewrite lookup_insert_eq|apply sle_refl, HW]. }
  cbn. tstep.
  { (* close c at ι, holding d at δ and e at κ *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
    exists (pvar 2). split; [done|by right]. }
  cbn. tstep.
  { (* close d at δ, holding e at κ *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
    exists (pvar 2). split; [done|by right]. }
  (* close e at κ *)
  tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|].
  exists (pvar 2). split; [done|apply sle_refl, HW].
Qed.

(** ** No known point lies between ι and κ

    Without E-NewFresh, new creates d at a point x of the body's context
    (E-Const asks x known and gives d the type Close@x). The body then
    needs ι ≺ x for close c and x ≺ κ for close d. The fact theory of
    the box body derives neither for any x. Its ≡ relates point
    variables by equality only, and its ≺ is program order on each name
    plus ι ≺ κ, closed under transitivity. The relation [fb_R] below
    contains every derived fact and has no x between ι and κ. *)

Definition fb_isvar (x : point) : bool := match pt_root x with NVar _ => true | _ => false end.

Definition fb_A (x y : point) : Prop :=
  (pt_name x = pt_name y ∧ pt_off x < pt_off y) ∨ (x = pvar 0 ∧ pt_name y = NVar 1).

Definition fb_R (x y : point) : Prop :=
  if fb_isvar x && fb_isvar y then fb_A x y else fb_isvar x = false ∧ fb_isvar y = false.

Lemma fb_isvar_const W x : world_wf W → pt_root x ∈ w_names W → fb_isvar x = false.
Proof. intros HW Hx. unfold fb_isvar. by destruct (wf_names_const _ HW _ Hx) as [a ->]. Qed.

Lemma fb_isvar_name x y : pt_name x = pt_name y → fb_isvar x = fb_isvar y.
Proof. intros E. unfold fb_isvar, pt_root. by rewrite E. Qed.

Lemma fb_A_trans x y z : fb_A x y → fb_A y z → fb_A x z.
Proof.
  intros [[H1 H2]|[-> H1]] [[H3 H4]|[-> H3]].
  - left. split; [congruence|lia].
  - exfalso. simpl in H2. lia.
  - right. split; [done|congruence].
  - by simpl in H1.
Qed.

Lemma fb_between_underivable W x : world_wf W →
  ¬ (slt W [(fb_C, ids 2)] (pvar 0) x ∧ slt W [(fb_C, ids 2)] x (pvar 1)).
Proof.
  intros HW [H1 H2].
  assert (∀ x y, slt W [(fb_C, ids 2)] x y → fb_R x y) as HR.
  { intros x0 y0 Hxy. change (match NP x0, NP y0 with NP x, NP y => fb_R x y | _, _ => True end).
    refine (proj2 (fl_map (FCtx W [(fb_C, ids 2)] ∅)
      (λ x y, x = y ∨ (fb_isvar x = false ∧ fb_isvar y = false))
      (λ a b, match a, b with NP x, NP y => fb_R x y | _, _ => True end) id id
      _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ Hxy); clear Hxy H1 H2; unfold id; simpl.
    - intros x1 y1 H0. destruct (wf_eq_supp _ HW _ _ H0) as [->|[Hx Hy]]; [by left|right].
      split; by apply (fb_isvar_const W).
    - intros x1 y1 (C & xs & Hg & g0 & Hg0 & E). apply list_elem_of_singleton in Hg.
      injection Hg as -> ->. apply bcs_open_nil in Hg0 as [-> _]. discriminate.
    - by left.
    - intros x1 y1 [->|[? ?]]; [by left|by right].
    - intros x1 y1 z1 [->|[? ?]] [->|[? ?]]; [by left|by right|by right|by right].
    - intros x1 y1 [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x1 y1 i [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x1 y1 Hxy. unfold fb_R. destruct (wf_lt_supp _ HW _ _ Hxy) as [[Hn Ho]|[Hx Hy]].
      + rewrite (fb_isvar_name x1 y1 Hn). destruct (fb_isvar y1); simpl; [left; by split|done].
      + rewrite (fb_isvar_const W x1), (fb_isvar_const W y1); done.
    - intros x1 y1 (C & xs & Hg & g0 & Hg0 & E). apply list_elem_of_singleton in Hg.
      injection Hg as -> ->. apply bcs_open_nil in Hg0 as [-> _].
      cbn in E. injection E as -> ->. unfold fb_R. simpl. right. by split.
    - intros φ u Hu. by rewrite lookup_empty in Hu.
    - intros x1 x' [y1|] HQ H0; [|done]. destruct HQ as [->|[Hx Hx']]; [done|].
      revert H0. unfold fb_R. rewrite Hx, Hx'. cbn. tauto.
    - intros [x1|] y1 y' H0 HQ; [|done]. destruct HQ as [<-|[Hy' Hy]]; [done|].
      revert H0. unfold fb_R. rewrite Hy, Hy', !andb_false_r. cbn. tauto.
    - intros [x1|] y1 [z1|]; try done. unfold fb_R.
      destruct (fb_isvar x1), (fb_isvar y1), (fb_isvar z1); simpl;
        intuition (try discriminate; eauto using fb_A_trans). }
  apply HR in H1, H2. unfold fb_R in H1, H2. simpl in H1.
  destruct (fb_isvar x) eqn:Hx; simpl in H1, H2; [|by destruct H1].
  destruct H1 as [[Hn Ho]|[_ Hn]], H2 as [[Hn' Ho']|[-> Hn']]; simpl in *.
  - congruence.
  - lia.
  - lia.
  - discriminate.
Qed.

(** ** The closed program

      main = let (f, u) = ⟨between, ∗⟩ in let () = u in
             let (c, c′) = new ∗ in let (e, e′) = new ∗ in
             let () = spawn (λu. let () = u in close c′) in
             let () = spawn (λu. let () = u in close e′) in
             (force f) ⟨c, e⟩

    c lives at (0, 0) and e at (1, 0). The world orders them, so force
    meets the box constraint at ((0, 0), (1, 0)). *)

Definition fb_main : expr :=
  LetP (Pair fb_box EUnit) (LetU (Var 0)
    (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
        (App (App EForce (Var 5)) (Pair (Var 3) (Var 1)))))))).

Lemma fb_main_typed W : strict W → pt_known W (pc 0 0) → pt_known W (pc 1 0) →
  w_lt W (pc 0 0) (pc 1 0) → typed W ∅ [] ∅ [] (∅, None) fb_main TUnit.
Proof.
  intros HWs Ha Hb Hab. pose proof (proj1 HWs) as HW. unfold fb_main.
  tstep.
  { tstep; [tstep|apply fb_typed, HW]. }
  cbn. tstep; [tstep|]. cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (pc 0 0) HWs (or_introl Ha)).
  cbn. apply (t_new_at W _ _ _ _ _ _ _ SEnd (pc 1 0) HWs (or_introl Hb)).
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pc 0 0). split; [done|apply sle_refl, HW]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pc 1 0). split; [done|apply sle_refl, HW]. }
  cbn. eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 1 0)) None
                 (TProd (TSess SEnd (pc 0 0)) (TSess SEnd (pc 1 0))) TUnit); [reflexivity| | |].
  - change (TLolli (Some (pc 1 0)) None (TProd (TSess SEnd (pc 0 0)) (TSess SEnd (pc 1 0))) TUnit)
      with (ty_inst [pc 0 0; pc 1 0] fb_body).
    apply (typed_force W _ _ _ _ _ _ 2 fb_C None fb_body [pc 0 0; pc 1 0]); [done|done| | |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g -> _. cbn. by apply sl_w.
    + constructor; [by left|constructor; [by left|constructor]].
  - cbn. tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Definition Wfb : world := Wfacts [0; 1] [(pc 0 0, pc 1 0)].

Lemma Wfb_strict : strict Wfb.
Proof.
  apply (Wfacts_strict _ _ (λ _, 1) (λ a, 10 * a) (λ _ _ _, 0)); [lia| |].
  - repeat constructor; cbn; set_solver.
  - repeat constructor; cbn; lia.
Qed.

Lemma fb_deadlock_free : deadlock_free (∅, {[+ fb_main +]}).
Proof.
  apply (soundness Wfb _ TUnit Wfb_strict).
  apply ptyped_closed; [constructor|]. apply fb_main_typed; [apply Wfb_strict| | |].
  - apply Wfacts_known. set_solver.
  - apply Wfacts_known. set_solver.
  - apply Wfacts_lt. set_solver.
Qed.

(** ** The same program in the empty world

    E-NewFresh also types the two top-level news of main: c at a fresh
    point γ with no facts (L and H empty), e at a fresh point ε with
    γ ≺ ε (L = [γ], H empty, betweenness holds vacuously). Then main
    needs no constant and no fact, and the world of [soundness] is
    empty. e is bound by the encoded let of new (sharp edges 99). *)

Definition fb_main_ex : expr :=
  LetP (Pair fb_box EUnit) (LetU (Var 0)
    (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
        (App (App EForce (Var 5)) (Pair (Var 3) (Var 1)))))))).

Lemma fb_main_typed_fresh W : world_wf W → typed W ∅ [] ∅ [] (∅, None) fb_main_ex TUnit.
Proof.
  intros HW. unfold fb_main_ex.
  tstep.
  { tstep; [tstep|apply fb_typed, HW]. }
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

(** The empty world: no constant, no fact. *)
Lemma fb_deadlock_free_empty : deadlock_free (∅, {[+ fb_main_ex +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply fb_main_typed_fresh, Wpo_strict.
Qed.
