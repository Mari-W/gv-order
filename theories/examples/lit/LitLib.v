(** * Tools for the literature examples of examples/lit/

    Two things the files of this directory share.

    [soundness_source_nil] reads a whole-program derivation in the
    empty context through [soundness_source], with no top-level point
    and the empty constraint C₀ = ∅. The older literature files reach
    deadlock freedom through [soundness] at the world [Wpo []]. Both
    routes end in the same theorem.

    [all_recv_stuck] says that a configuration whose every thread can
    only take receive steps makes no τ step. The rejected programs of
    this directory reach such a configuration, so they are not deadlock
    free and [soundness_source] rules out a derivation. This is the
    argument of examples/cfst/CfstDeadlock.v, stated once for any number
    of threads. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

(** ** The empty top-level constraint *)

Definition nil_C0 : bcs := BCs [] (λ _, False).

Lemma nil_C0_acyclic : c0_acyclic 0 nil_C0.
Proof. apply (c0_acyclic_rank 0 _ (vrank 1)); [apply vrank_shift|by intros ? ? []|apply vrank_dual]. Qed.

Lemma typed_hyps_wk_lit W Ψ F e T : strict W → typed W ∅ [] ∅ [] F e T → typed W ∅ Ψ ∅ [] F e T.
Proof.
  intros HW H. pose proof (typed_pinst W _ _ _ _ _ _ _ HW H pvar Ψ) as H'.
  rewrite fhyps_pinst_empty, tenv_pinst_empty, sf_pinst_pvar, pinst_ty_pvar in H'.
  apply H'. intros C xs Hm. by apply elem_of_nil in Hm.
Qed.

Lemma styped_nil_hyps e T :
  styped ∅ [] [] (∅, None) e T → styped ∅ [(nil_C0, [])] [] (∅, None) e T.
Proof.
  intros H. apply styped_Wpo. apply typed_hyps_wk_lit; [apply Wpo_nil_strict'|].
  by apply styped_typed.
Qed.

Theorem soundness_source_nil t T :
  prim T → styped ∅ [] [] (∅, None) t T → deadlock_free (∅, {[+ t +]}).
Proof.
  intros HT Ht. apply (soundness_source 0 nil_C0 t T (c0_acyclic_creation _ _ nil_C0_acyclic) HT).
  by apply styped_nil_hyps.
Qed.

(** ** Program order between the two ends of one root

    With end points the two ends of a channel sit at x and x̄, and the
    gates compare a blocking point with the partner points of the other
    held ends. ι+j ≺ ι+k and ι+j ≺ ῑ+k hold for j < k at either polarity
    of ι+j. *)
Lemma pp_slt_po W Ψ a b b' j k : world_wf W → j < k → slt W Ψ (MkPt a b j) (MkPt a b' k).
Proof.
  intros HW H.
  assert (∀ m d d', slt W Ψ (MkPt a d m) (MkPt a d' (S m))) as Hs.
  { intros m [] [];
      [pose proof (slt_po W Ψ (MkPt a true m) HW) as G|pose proof (sl_dpo W Ψ (MkPt a true m)) as G
      |pose proof (sl_dpo W Ψ (MkPt a false m)) as G|pose proof (slt_po W Ψ (MkPt a false m) HW) as G];
      unfold pt_shift, pt_dual in G; simpl in G; rewrite Nat.add_1_r in G; exact G. }
  revert b'. induction H as [|k _ IH]; intros b'; [apply Hs|].
  eapply sl_trans; [apply (IH true)|apply Hs].
Qed.

Lemma pp_sle_po W Ψ a b b' j k : world_wf W → j < k ∨ (j = k ∧ b = b') → sle W Ψ (MkPt a b j) (MkPt a b' k).
Proof. intros HW [H|[-> ->]]; [right; by apply pp_slt_po|apply sle_refl, HW]. Qed.

Ltac pp_future HW := intros ? Hy; mem_cases Hy; (apply pp_slt_po; [exact HW|cbn; lia]).
Ltac pp_fvar HW u := exists u; split; [done|apply pp_sle_po; [exact HW|cbn; first [left; lia|right; split; [lia|done]]]].
Ltac pp_lb HW := intros ? Hy; mem_cases Hy; (apply pp_sle_po; [exact HW|cbn; first [left; lia|right; split; [lia|done]]]).
Ltac pp_gate HW u := apply ubs_intro; [pp_future HW|pp_fvar HW u].
Ltac pp_gate0 HW := apply ubs_intro; [pp_future HW|done].

(** ** Configurations where every thread waits on a send or a receive

    [blocked_on e k c] says that every step of e is a send on c (k =
    true) or a receive on c (k = false). A configuration whose threads
    are listed with such an offer, and where two threads that offer on
    one channel offer in one direction, makes no τ step. *)

Definition blocked_on (e : expr) (k : bool) (c : chan) : Prop :=
  ∀ α e', tstep e α e' → ∃ v, α = LSess (if k then SSend c v else SRecv c v).

Lemma blocked_recv c : blocked_on (App ERecv (Chan c)) false c.
Proof.
  intros α e' H. apply tstep_app_inv in H as [(? & H & _)|[(_ & ? & H & _)|(_ & _ & H)]].
  - exfalso. by eapply val_no_tstep.
  - exfalso. by eapply val_no_tstep.
  - inversion H; subst. by eexists.
Qed.

Lemma blocked_send v c : is_val v → blocked_on (App ESend (Pair v (Chan c))) true c.
Proof.
  intros Hv α e' H. apply tstep_app_inv in H as [(? & H & _)|[(_ & ? & H & _)|(_ & _ & H)]].
  - exfalso. by eapply val_no_tstep.
  - exfalso. eapply val_no_tstep; [exact H|]. simpl. by apply andb_True.
  - inversion H; subst. by eexists.
Qed.

Lemma blocked_frame f e k c :
  frame_val f → is_val e = false → blocked_on e k c → blocked_on (fill_frame f e) k c.
Proof.
  intros Hf Hv Hb α E' H. apply tstep_fill_inv in H as (e' & H & _); [|done|intros Hc; rewrite Hv in Hc; exact Hc].
  by eapply Hb.
Qed.

Lemma blocked_letp e e2 k c : is_val e = false → blocked_on e k c → blocked_on (LetP e e2) k c.
Proof. apply (blocked_frame (FLetP e2)). done. Qed.
Lemma blocked_letu e e2 k c : is_val e = false → blocked_on e k c → blocked_on (LetU e e2) k c.
Proof. apply (blocked_frame (FLetU e2)). done. Qed.
Lemma blocked_appl e e2 k c : is_val e = false → blocked_on e k c → blocked_on (App e e2) k c.
Proof. apply (blocked_frame (FAppL e2)). done. Qed.
Lemma blocked_appr v e k c : is_val v → is_val e = false → blocked_on e k c → blocked_on (App v e) k c.
Proof. intros Hv. by apply (blocked_frame (FAppR v)). Qed.
Lemma blocked_pairl e e2 k c : is_val e = false → blocked_on e k c → blocked_on (Pair e e2) k c.
Proof. apply (blocked_frame (FPairL e2)). done. Qed.
Lemma blocked_pairr v e k c : is_val v → is_val e = false → blocked_on e k c → blocked_on (Pair v e) k c.
Proof. intros Hv. by apply (blocked_frame (FPairR v)). Qed.

(** Peel evaluation frames down to the blocking send or receive. *)
Ltac blocked :=
  repeat first
    [ apply blocked_recv
    | apply blocked_send; done
    | apply blocked_letp; [done|]
    | apply blocked_letu; [done|]
    | apply blocked_appr; [done|done|]
    | apply blocked_appl; [done|]
    | apply blocked_pairr; [done|done|]
    | apply blocked_pairl; [done|] ].

Lemma offers_stuck C (L : list (expr * (bool * chan))) p' :
  Forall (λ t, blocked_on t.1 t.2.1 t.2.2) L →
  (∀ t u, t ∈ L → u ∈ L → t.2.2 = u.2.2 → t.2.1 = u.2.1) →
  ¬ preduction (C, list_to_set_disj (fst <$> L)) p'.
Proof.
  intros HB HD H.
  assert (∀ e α e', e ∈ (list_to_set_disj (fst <$> L) : gmultiset expr) → tstep e α e' →
            ∃ (k : bool) (c : chan) (v : expr), (e, (k, c)) ∈ L ∧ α = LSess (if k then SSend c v else SRecv c v)) as HS.
  { intros e α e' He Ht. apply elem_of_list_to_set_disj, list_elem_of_fmap in He as ([e0 [k c]] & -> & Hin).
    rewrite Forall_forall in HB. destruct (HB _ Hin _ _ Ht) as [v ->]. by exists k, c, v. }
  inversion H; subst;
    repeat match goal with
    | Hm : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _, Ht : tstep ?e _ _, Hu : tstep ?f _ _ |- _ =>
        let He := fresh in let Hf := fresh in
        assert (e ∈ (list_to_set_disj (fst <$> L) : gmultiset expr)) as He by (rewrite <-Hm; multiset_solver);
        assert (f ∈ (list_to_set_disj (fst <$> L) : gmultiset expr)) as Hf by (rewrite <-Hm; multiset_solver);
        clear Hm;
        destruct (HS _ _ _ He Ht) as (k1 & c1 & v1 & Hi1 & E1);
        destruct (HS _ _ _ Hf Hu) as (k2 & c2 & v2 & Hi2 & E2)
    | Hm : _ ⊎ {[+ ?e +]} = _, Ht : tstep ?e _ _ |- _ =>
        let He := fresh in
        assert (e ∈ (list_to_set_disj (fst <$> L) : gmultiset expr)) as He by (rewrite <-Hm; multiset_solver);
        clear Hm;
        destruct (HS _ _ _ He Ht) as (k1 & c1 & v1 & Hi1 & E1)
    end;
    try (destruct k1; discriminate).
  (* the message: a send meets a receive on one channel *)
  destruct k1, k2; try discriminate. injection E1 as <- <-. injection E2 as <- <-.
  by pose proof (HD _ _ Hi1 Hi2 eq_refl).
Qed.

(** A configuration with a restricted channel is not terminated. *)
Lemma not_terminated_chan C E : C ≠ ∅ → ¬ terminated (C, E).
Proof. intros HC (v & E' & Heq & _). injection Heq as -> _. done. Qed.

(** A reachable configuration that is stuck and not terminated refutes
    deadlock freedom. *)
Lemma not_df_of_stuck p p' :
  pred_star p p' → ¬ terminated p' → (∀ p'', ¬ preduction p' p'') → ¬ deadlock_free p.
Proof.
  intros Hp Ht Hs Hdf. destruct (Hdf p' Hp) as [?|[p'' ?]]; [by apply Ht|by eapply Hs].
Qed.

Ltac pbeta_lit := eapply rtc_l; [apply PStepBeta|].

(** ** Running a program by hand *)

Lemma ms_swap (E : gmultiset expr) a b : E ⊎ {[+ a +]} ⊎ {[+ b +]} = E ⊎ {[+ b +]} ⊎ {[+ a +]}.
Proof. multiset_solver. Qed.

Lemma ms_one_lit (e : expr) : ({[+ e +]} : gmultiset expr) = ∅ ⊎ {[+ e +]}.
Proof. multiset_solver. Qed.

(** One step of a thread under evaluation frames, by the head rule. *)
Ltac tsh :=
  first
    [ apply TStepHead; solve [ apply HeadApp; done | apply HeadLetU | apply HeadLetP; done
                             | apply HeadSpawn; done | apply HeadNew
                             | apply HeadCase1; done | apply HeadCase2; done | apply HeadForce ]
    | apply TStepLetU; tsh | apply TStepLetP; tsh
    | apply TStepAppR; [done|tsh] | apply TStepAppL; tsh
    | apply TStepPairR; [done|tsh] | apply TStepPairL; tsh ].

(** Normalize the last thread and the one before it. *)
Ltac norml :=
  try match goal with |- rtc _ (_, _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]}) _ =>
    let e' := eval cbn in e in change e with e' end;
  try match goal with |- rtc _ (_, _ ⊎ {[+ ?e +]}) _ =>
    let e' := eval cbn in e in change e with e' end.

(** A β step of the last thread. *)
Ltac pb := eapply rtc_l; [apply PStepBeta; tsh|]; norml.

(** A [new] of the last thread with the channel name s, while no other
    thread exists. *)
Ltac pnew s :=
  eapply rtc_l;
  [apply (PStepNew _ _ _ s%string); [tsh|set_solver|unfold echans; rewrite gmultiset_elements_empty; set_solver|cbn; set_solver]|];
  norml.

(** A spawn of the last thread. *)
Ltac psp := eapply rtc_l; [apply PStepSpawn; tsh|]; norml.

Lemma offers_stuck_l C (L : list (expr * (bool * chan))) E p' :
  Forall (λ t, blocked_on t.1 t.2.1 t.2.2) L →
  E = list_to_set_disj (fst <$> L) →
  (∀ t u, t ∈ L → u ∈ L → t.2.2 = u.2.2 → t.2.1 = u.2.1) →
  ¬ preduction (C, E) p'.
Proof. intros HB ->. by apply offers_stuck. Qed.

(** The threads of a multiset written ∅ ⊎ {[+ e₁ +]} ⊎ … ⊎ {[+ eₙ +]},
    each paired with an offer left open. *)
Ltac mk_offers E :=
  lazymatch E with
  | ∅ => open_constr:(@nil (expr * (bool * chan)))
  | ?E' ⊎ {[+ ?x +]} =>
      let L := mk_offers E' in open_constr:((x, (_ : bool, _ : chan)) :: L)
  end.

(** Close a goal ¬ preduction (C, E) p by the offers of the threads. *)
Ltac stuck :=
  lazymatch goal with
  | |- ¬ preduction (_, ?E) _ =>
      let L := mk_offers E in
      apply (offers_stuck_l _ L);
      [ repeat (apply Forall_cons; split; [cbn; blocked|]); by apply Forall_nil
      | cbn [fmap list_fmap fst]; rewrite ?list_to_set_disj_cons, list_to_set_disj_nil; multiset_solver
      | intros t u Ht Hu; rewrite !elem_of_cons, elem_of_nil in Ht, Hu;
        repeat match goal with H : _ ∨ _ |- _ => destruct H as [H|H] end;
        try contradiction; subst; cbn; intros Etu; first [reflexivity|discriminate Etu] ]
  end.
