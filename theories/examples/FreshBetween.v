(** * Example: a channel created between two box arguments

    between : □(∀ι κ. {ι ≺ κ}. ∗ ⊸ Close@ι ⊗ Close@κ ⊸^κ ∗)
    between = !(f = λp. let (c, e) = p in
                        let q = new ∗ in let (d, d′) = q in
                        let () = spawn (λu. let () = u in close d′) in
                        let () = close c in let () = close d in close e)

    close c blocks at ι while the thread holds d and e, close d blocks
    at the point δ of d while it holds e. So δ needs ι ≺ δ ≺ κ. No
    point built from ι and κ lies there. ι + 1 ≺ κ does not follow from
    ι ≺ κ, and a point ι[i] or κ[i] is unrelated to both. E-NewFresh
    creates d at a fresh point δ with ι ≺ δ ≺ κ, which betweenness
    allows because the box hypothesis gives ι ≺ κ (sharp edges 90).
    new returns ∃δ. C. Close@δ ⊗ Close@δ, and E-Open on q opens it
    (sharp edges 99).

    With end points the thread keeps d at δ and the thunk closes d′ at
    δ̄. The gates compare blocking points with partner points: close c
    asks ι ≺ δ̄ and ι ≺ κ̄, close d asks δ ≺ κ̄, and the upper point κ
    asks ι ≺ κ and δ ≺ κ. The box constraint is {ι ≺ κ, ι ≺ κ̄}, and
    the fresh constraint {ι ≺ δ̄, δ ≺ κ, δ ≺ κ̄} relates no lower and
    upper fact of one polarity, so betweenness holds vacuously.

    Under the constant world (sharp edges 172) no fresh point exists.
    d is created with new@δ at the field point δ = ι[0], and the box
    constraint grows to {ι ≺ κ, ι ≺ κ̄, ι ≺ δ̄, δ ≺ κ, δ ≺ κ̄} ([fbx_C]).
    The caller states these facts for its own points. main creates c
    and e at its top-level points γ and ε ([fb_Ψ]) and gets deadlock
    freedom from [soundness_created_s]. [fb_between_underivable] still
    shows that the old constraint {ι ≺ κ, ι ≺ κ̄} has no point between
    ι and κ.

    Under syntactic points (sharp edges 173) the box takes the point ι
    as a parameter π : pt(ι) and creates d by new (π[0]). main creates c
    and e at the constants 1 and 0 and passes the literal γ. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools.

Set Default Proof Using "All".

Definition fb_C : bcs := BCs [] (λ g, g = FLt (pvar 0) (pvar 1) ∨ g = FLt (pvar 0) (pt_dual (pvar 1))).

(** Under the constant world (sharp edges 172) d is created with new@δ
    at the field point δ = ι[0] of the first box variable. The box
    constraint states the facts of δ that the fresh constraint used to
    give, and the caller proves them in its own context. *)
Abbreviation fbd := (Pt (NPayload (NVar 0) 0 0) 0).

Definition fbx_P (g : fact) : Prop :=
  g = FLt (pvar 0) (pvar 1) ∨ g = FLt (pvar 0) (pt_dual (pvar 1)) ∨ g = FLt (pvar 0) (pt_dual fbd) ∨
  g = FLt fbd (pvar 1) ∨ g = FLt fbd (pt_dual (pvar 1)).
Definition fbx_C : bcs := BCs [] fbx_P.

(** Under syntactic points the box takes the point ι as a parameter and
    creates d by new (π[0]) ([KPay 0], sharp edges 173). *)
Definition fb_body : ty :=
  TLolli None None (TPt (pvar 0))
    (TLolli (Some (pvar 1)) None (TProd (TSess SEnd (pvar 0)) (TSess SEnd (pvar 1))) TUnit).

Definition fb_ty : ty := TBox 2 0 fbx_C (TLolli None None TUnit fb_body).

Definition fb_box : expr :=
  EBox (Lam (Lam (LetP (Var 0) (let_new_pair_at (App (Konst (KPay 0)) (Var 3))
    (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
    (LetU (App EClos (Var 3))
    (LetU (App EClos (Var 1))
          (App EClos (Var 2))))))))).

Lemma fb_typed W F : strict W → typed W ∅ [] ∅ [] F fb_box fb_ty.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold fb_box, fb_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ None None 1); [set_solver|cbn; set_solver|].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ (Some (pvar 1)) None 2); [set_solver|cbn; set_solver|].
  eapply t_weak; [apply lwk_cons, lwk_cons, lwk_drop; [done|constructor]|].
  cbn. tstep; [tstep|]. cbn.
  change (bcs_inst (pshift 2) fbx_C) with fbx_C.
  unfold let_new_pair_at. apply (t_new_v W _ _ _ _ _ _ _ SEnd fbd _ HWs).
  { intros F'. cbn. eapply (tv_appk W HW _ _ _ _ (KPay 0) _ None (TPt (pvar 0)));
      [tstep|apply KTPay; eapply (skn_in W _ _ [pvar 0; pvar 1] (pvar 0)); [by left|by left|done]
      |done|apply ubs_none]. }
  { eapply (skn_in W _ _ [pvar 0; pvar 1] (pvar 0)); [by left|by left|done]. }
  cbn.
  set (Ψ := [(fbx_C, [pvar 0; pvar 1])]).
  (* the facts: ι ≺ δ̄, δ ≺ κ, δ ≺ κ̄, ι ≺ κ, ι ≺ κ̄ *)
  assert (slt W Ψ (pvar 0) (pt_dual fbd)) as Hιδ.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (pt_dual fbd)); [by left|by right; right; left|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ fbd (pvar 1)) as Hδκ.
  { eapply (sl_hyp0 _ _ _ _ fbd (pvar 1)); [by left|by right; right; right; left|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ fbd (pt_dual (pvar 1))) as Hδκ'.
  { eapply (sl_hyp0 _ _ _ _ fbd (pt_dual (pvar 1))); [by left|by right; right; right; right|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (pvar 0) (pvar 1)) as Hικ.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (pvar 1)); [by left|by left|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (pvar 0) (pt_dual (pvar 1))) as Hικ'.
  { eapply (sl_hyp0 _ _ _ _ (pvar 0) (pt_dual (pvar 1))); [by left|by right; left|cbn; lia|reflexivity|reflexivity]. }
  tstep.
  { (* spawn (λu. let () = u in close d′) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual fbd)) (Some fbd) 3); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual fbd). split; [by rewrite lookup_insert_eq|apply sle_refl, HW]. }
  cbn. tstep.
  { (* close c at ι, holding d at δ and e at κ *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
    exists (pvar 1). split; [done|by right]. }
  cbn. tstep.
  { (* close d at δ, holding e at κ *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
    exists (pvar 1). split; [done|by right]. }
  (* close e at κ *)
  tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|].
  exists (pvar 1). split; [done|apply sle_refl, HW].
Qed.

(** ** No known point lies between ι and κ

    Without E-NewFresh, new creates d at a point x of the body's context
    (E-Const asks x known and gives d the type Close@x). The body then
    needs ι ≺ x for close c and x ≺ κ for close d. The fact theory of
    the box body derives neither for any x. Its ≡ relates point
    variables by equality only, and its ≺ is program order on each name
    plus ι ≺ κ, closed under transitivity. The relation [fb_R] below
    contains every derived fact and has no x between ι and κ. With end
    points the constraint also has ι ≺ κ̄ and program order has
    x ≺ x̄+1, and [fb_R] still contains both. *)

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
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ Hxy); clear Hxy H1 H2; unfold id; simpl.
    - intros x1 y1 H0. destruct (wf_eq_supp _ HW _ _ H0) as [->|[Hx Hy]]; [by left|right].
      split; by apply (fb_isvar_const W).
    - by left.
    - intros x1 y1 [->|[? ?]]; [by left|by right].
    - intros x1 y1 z1 [->|[? ?]] [->|[? ?]]; [by left|by right|by right|by right].
    - intros x1 y1 [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x1 y1 i [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x1 y1 Hxy. unfold fb_R. destruct (wf_lt_supp _ HW _ _ Hxy) as [[Hn Ho]%ppo_pofs|[Hx Hy]].
      + rewrite (fb_isvar_name x1 y1 Hn). destruct (fb_isvar y1); simpl; [left; by split|done].
      + rewrite (fb_isvar_const W x1), (fb_isvar_const W y1); done.
    - intros x1 y1 (C & xs & Hg & g0 & Hg0 & E). apply list_elem_of_singleton in Hg.
      injection Hg as -> ->. apply bcs_open_nil in Hg0 as [[-> | ->] _];
        cbn in E; injection E as -> ->; unfold fb_R; simpl; right; by split.
    - intros φ u Hu. by rewrite lookup_empty in Hu.
    - intros x1 x' [y1|] HQ H0; [|done]. destruct HQ as [->|[Hx Hx']]; [done|].
      revert H0. unfold fb_R. rewrite Hx, Hx'. cbn. tauto.
    - intros [x1|] y1 y' H0 HQ; [|done]. destruct HQ as [<-|[Hy' Hy]]; [done|].
      revert H0. unfold fb_R. rewrite Hy, Hy', !andb_false_r. cbn. tauto.
    - intros [x1|] y1 [z1|]; try done. unfold fb_R.
      destruct (fb_isvar x1), (fb_isvar y1), (fb_isvar z1); simpl;
        intuition (try discriminate; eauto using fb_A_trans).
    - intros x1. unfold fb_R. rewrite <-(fb_isvar_name x1 (pt_shift 1 x1)) by done.
      destruct (fb_isvar x1); simpl; [|done].
      left. unfold pt_shift. simpl. split; [done|lia].
    - intros x1 y1 [->|[Hx Hy]]; [by left|right].
      rewrite <-(fb_isvar_name x1 (pt_dual x1)), <-(fb_isvar_name y1 (pt_dual y1)) by done. by split.
    - intros x1. unfold fb_R. rewrite <-(fb_isvar_name x1 (pt_shift 1 (pt_dual x1))) by done.
      destruct (fb_isvar x1); simpl; [|done].
      left. unfold pt_shift. simpl. split; [done|lia]. }
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
    (let_new_pair_at (EPt (pconst 1)) (let_new_pair_at (EPt (pconst 0))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
        (App (App (App EForce (Var 5)) (EPt (pconst 1))) (Pair (Var 3) (Var 1)))))))).



(** ** The program under its top-level points

    Under the constant world the two top-level news of main create c at
    the point γ and e at the point ε of the program's hypotheses
    ([fb_Ψ], sharp edges 172). γ is created with the fact γ ≺ (γ[0])‾,
    and ε with γ ≺ ε and γ[0] ≺ ε at both polarities of each. These are
    the facts of the box constraint at the instance (γ, ε), so main
    meets it. e is bound by the encoded let of new (sharp edges 99). *)

Definition fb_main_ex : expr :=
  LetP (Pair fb_box EUnit) (LetU (Var 0)
    (let_new_pair_at (EPt (pconst 1)) (let_new_pair_at (EPt (pconst 0))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
        (App (App (App EForce (Var 5)) (EPt (pconst 1))) (Pair (Var 3) (Var 1)))))))).

(** The creation constraint of γ: γ ≺ (γ[0])‾. *)
Definition fbg_P (g : fact) : Prop := g = FLt (pvar 0) (pt_dual fbd).
Definition fbg_C : bcs := BCs [] fbg_P.

Lemma fbg_ok peq plt : cc_ok peq plt fbg_C.
Proof.
  set (r := λ x : point, 2 * pt_off x + match pt_name x with NPayload _ _ _ => 1 | _ => 0 end).
  apply (cc_ok_inner peq plt fbg_P (λ x y, r x < r y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [q pb o] _. unfold r, pt_shift. simpl. lia.
  - intros g -> _. eexists _, _. split; [done|]. unfold r. cbn. lia.
  - intros [q pb o] _. unfold r, pt_shift, pt_dual. simpl. lia.
Qed.

(** The facts of ε: γ and γ[0] below ε and ε̄. *)
Abbreviation fbdc := (Pt (NPayload (NConst 1) 0 0) 0).

Definition fb_L : list (point * bool) :=
  [(pconst 1, true); (pconst 1, false); (fbdc, true); (fbdc, false)].

Definition fb_Ψ : hyps :=
  ([] ++ [(fbg_C, [pconst 1])]) ++ [(freshp_bcs fb_L [], [pconst 0])].

Lemma fb_created : created (Wpo []) fb_Ψ.
Proof.
  apply created_p; [apply created_snoc; [constructor|apply fbg_ok|constructor|fresh_const]| | |fresh_const].
  - cbn. repeat (apply Forall_cons; split;
      [right; exists fbg_C, [pconst 1], (pconst 1); split_and!; [by left|by left|done]|]).
    by apply Forall_nil.
  - intros l h b _ Hh. by apply elem_of_nil in Hh.
Qed.

Lemma fb_main_typed_fresh : styped ∅ fb_Ψ [] (∅, None) fb_main_ex TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  set (W := Wpo []) in *. unfold fb_main_ex, let_new_pair_at, fb_Ψ.
  tstep.
  { tstep; [tstep|apply typed_hyps_nil; [exact HWs|apply fb_typed, HWs]]. }
  cbn. tstep; [tstep|]. cbn.
  new_top HWs SEnd (pconst 1). new_top HWs SEnd (pconst 0).
  cbn.
  set (L := fb_L).
  match goal with |- typed _ _ ?Q _ _ _ _ _ => set (Ψ := Q) end.
  assert (∀ l b, (l, b) ∈ L → slt W Ψ l (pt_polar b (pconst 0))) as HL.
  { intros l b Hl. by apply (slt_freshp_l W Ψ L [] (pconst 0)); [right; left|]. }
  assert (slt W Ψ (pconst 1) (pconst 0)) as Hγε by (apply (HL (pconst 1) true); set_solver).
  assert (slt W Ψ (pconst 1) (pt_dual (pconst 0))) as Hγε' by (apply (HL (pconst 1) false); set_solver).
  assert (slt W Ψ (Pt (NPayload (NConst 1) 0 0) 0) (pconst 0)) as Hdε by (apply (HL fbdc true); set_solver).
  assert (slt W Ψ (Pt (NPayload (NConst 1) 0 0) 0) (pt_dual (pconst 0))) as Hdε'
    by (apply (HL fbdc false); set_solver).
  assert (slt W Ψ (pconst 1) (pt_dual (Pt (NPayload (NConst 1) 0 0) 0))) as Hγd.
  { eapply (sl_hyp0 _ _ fbg_P [pconst 1] (pvar 0) (pt_dual fbd)); [by left|done|cbn; lia|reflexivity|reflexivity]. }
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pconst 1))) (Some (pconst 1)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (pconst 1)). split; [done|apply sle_refl, HW]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pconst 0))) (Some (pconst 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (pconst 0)). split; [done|apply sle_refl, HW]. }
  cbn. eapply (tv_app W HW _ _ _ _ _ _ (Some (pconst 0)) None
                 (TProd (TSess SEnd (pconst 1)) (TSess SEnd (pconst 0))) TUnit); [reflexivity| | |].
  - eapply (tv_app W HW _ _ _ _ _ _ None None (TPt (pconst 1))); [reflexivity| | |apply ubs_none].
    + change (TLolli None None (TPt (pconst 1))
                (TLolli (Some (pconst 0)) None (TProd (TSess SEnd (pconst 1)) (TSess SEnd (pconst 0))) TUnit))
        with (ty_inst [pconst 1; pconst 0] fb_body).
      apply (typed_force0 W _ _ _ _ _ _ 2 fbx_C None fb_body [pconst 1; pconst 0]); [done|done| | |apply ubs_none|tstep].
      * apply bcs_hold_intro. intros g [-> |[-> |[-> |[-> | ->]]]] _; cbn;
          [exact Hγε|exact Hγε'|exact Hγd|exact Hdε|exact Hdε'].
      * constructor; [|constructor; [|constructor]].
        -- right. eexists _, [pconst 1], (pconst 1). split_and!; [by left|by left|done].
        -- right. eexists _, [pconst 0], (pconst 0). split_and!; [by right; left|by left|done].
    + tstep. right. eexists _, [pconst 1], (pconst 1). split_and!; [by left|by left|done].
  - cbn. tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The empty world: no constant, no fact. *)
Lemma fb_deadlock_free_empty : deadlock_free (∅, {[+ fb_main_ex +]}).
Proof. apply (soundness_created_s fb_Ψ _ TUnit fb_created); [constructor|apply fb_main_typed_fresh]. Qed.

(** [fb_main] is the program [fb_main_ex], so it types in the empty
    world too (sharp edges 105). *)
Lemma fb_deadlock_free : deadlock_free (∅, {[+ fb_main +]}).
Proof. apply (soundness_created_s fb_Ψ _ TUnit fb_created); [constructor|apply fb_main_typed_fresh]. Qed.
