(** * factory: a box that yields a fresh session per request

    [fac] creates every session at one top-level point variable a.
    [faca] is the same body under □∀ι and creates the session at the
    point variable ι. No well-formed world knows a point variable
    ([pvar_unknown]), so new at a and at ι types through the knownness
    of an instance of a hypothesis (sharp edges 59, 61, 110).

      fac  = !(f = λu. let () = u in let (c, c′) = new ∗ in
                       let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)
           : □(∗ ⊸ (?∗.Close)@a)
      main = let (f, u) = ⟨fac, ∗⟩ in let () = u in
             let () = recvclose ((force f) ∗) in recvclose ((force f) ∗)

    f is used twice (contraction at □). Both sessions live at a, so the
    client must finish one before it requests the next. Holding both
    while it blocks on one would ask a ≺ a.

    Both programs start under a top-level constraint (sharp edges 110)
    and type in the empty world. fac_main starts with one variable a and
    no fact. fa_main starts with two variables a and b and the facts
    a ≺ b̄ and a+1 ≺ b̄, which the world [Wfa] stated over constants
    before.

    With end points new in the body creates the channel at ā, so the
    returned end c′ sits at a and the spawned sender at ā. A gate
    compares with the partner of a held end, so the facts of fa_main
    name b̄, the partner of y at b.

    Syntactic points (sharp edges 173). A term names the point of new as
    a ground value, so a and b are constants of hypotheses ([fac_Ψ],
    [fa_Ψ]) and both programs go through [soundness_created_s]. fac
    writes the literal ā. faca takes the point ῑ as its parameter in
    place of the unit, and main passes ā and b̄. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.FreshTools.

Set Default Proof Using "All".

Lemma pvar_unknown W a : world_wf W → ¬ pt_known W (pvar a).
Proof. intros HW Hk. destruct (wf_names_const _ HW _ Hk) as [b Hb]. done. Qed.

Definition Tfac_body : ty := TLolli None None TUnit (TSess (SSeq (SRcv 0 TUnit) SEnd) (pc 0 0)).
Definition Tfac : ty := TBox 0 0 (BCs [] (λ _, False)) (TLolli None None TUnit Tfac_body).

Definition fac : expr :=
  EBox (Lam (LetU (Var 0) (let_new_pair_at (EPt (pt_dual (pconst 0)))
    (LetU (App ESpawn (Lam (LetU (Var 0) (sendclose (Var 2))))) (Var 0))))).

Definition request : expr := recvclose (App (App EForce (Var 1)) EUnit).

Definition fac_main : expr :=
  LetP (Pair fac EUnit) (LetU (Var 0) (LetU request request)).

(** fac_main starts with one top-level variable a and no fact. Under
    syntactic points a is the constant 0 of the hypotheses ([fac_Ψ]),
    so that the body of fac can write the literal ā. *)
Definition Cfac : bcs := BCs [] (λ _, False).

Lemma Cfac_ok peq plt : cc_ok peq plt Cfac.
Proof.
  set (r x := 2 * pt_off x + (if pt_pol x then 0 else 1)).
  apply (cc_ok_inner peq plt _ (λ x y, r x < r y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n pb o] _. unfold r, pt_shift. simpl. lia.
  - by intros g [].
  - intros [n [] o] _; unfold r, pt_shift, pt_dual; simpl; lia.
Qed.

Definition fac_Ψ : hyps := [] ++ [(Cfac, [pconst 0])].

Lemma fac_created : created (Wpo []) fac_Ψ.
Proof. apply created_snoc; [constructor|apply Cfac_ok|constructor|fresh_const]. Qed.

Lemma fac_typed : styped ∅ fac_Ψ [] (∅, None) fac_main TUnit.
Proof.
  apply styped_Wpo. set (W := Wpo []). pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  unfold fac_main, fac_Ψ.
  tstep.
  { tstep; [tstep|].
    apply (t_exp W _ _ _ _ _ 0 0 (BCs [] (λ _, False)) None Tfac_body 0); [by apply allunl_unl|set_solver|box_k0].
    cbn. eapply (tv_lam W HW _ _ _ _ _ TUnit _ None None 1); [set_solver|cbn; set_solver|].
    cbn. tstep; [tstep|]. cbn. unfold let_new_pair_at.
    apply (t_new_at W _ _ _ _ _ _ _ Sd (pt_dual (pconst 0)) HWs); [ground| |].
    { right. exists Cfac, [pconst 0], (pconst 0). split_and!; [by left|by left|done]. }
    cbn. tstep; [|tstep].
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pc 0 1))) (Some (pc 0 0)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pt_dual (pc 0 0))); cbn; set_solver|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual (pc 0 1)). split; [done|]. right. apply (slt_po W _ (pt_dual (pc 0 0)) HW).
    - apply KTClos.
    - done.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual (pc 0 1)). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  assert (∀ P, (∀ y, y ∈ P → False) →
    typed W ∅ ([] ++ [(Cfac, [pconst 0])]) ∅ [None; Some Tfac] (P, None) request TUnit) as Hreq.
  { intros P HP. unfold request, recvclose. tstep.
    - tstep; [| | |].
      + eapply tv_app; [exact HW|reflexivity| |tstep|apply ubs_none].
        cbn. apply (typed_force0 W _ _ _ _ _ _ 0 (BCs [] (λ _, False)) None Tfac_body []);
          [done|done| |constructor|apply ubs_none|tstep].
        apply bcs_hold_intro. by intros ? [].
      + apply KTRecv.
      + kscope.
      + apply ubs_intro; [|done]. intros y Hy. cbn in Hy.
        rewrite elem_of_union in Hy. destruct Hy as [Hy|Hy]; [by destruct (HP y)|set_solver].
    - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [|done]. intros y Hy. by destruct (HP y). }
  tstep; apply Hreq; cbn; set_solver.
Qed.

Lemma Cfac_acyclic : c0_acyclic 1 Cfac.
Proof. apply (c0_acyclic_rank 1 _ (vrank 1)); [apply vrank_shift|by intros ? ? []|apply vrank_dual]. Qed.

Lemma fac_deadlock_free : deadlock_free (∅, {[+ fac_main +]}).
Proof. apply (soundness_created_s fac_Ψ _ TUnit fac_created); [constructor|apply fac_typed]. Qed.

(** ** factory under □∀ι: typable (SHARP-EDGES 61)

      faca : □(∀ι. ∗ ⊸ (?∗.Close)@ι)      (the body of fac, new at ι)
      fa_main = let (f, u) = ⟨faca, ∗⟩ in let () = u in
                let (x, y) = ⟨(force f) ∗, (force f) ∗⟩ in
                let () = recvclose x in recvclose y

    new in the body creates the channel at the point variable ι. The
    static system reads ι as known, because it is a point of the body's
    own instance (skn, hyp_known), and force asks the instance known in
    the world. main forces at the top-level variables a and b and
    holds both sessions, which the one-point factory could not: x is
    used while y waits, so a ≺ b̄ and a+1 ≺ b̄, the facts of the
    top-level constraint [Cfa]. *)

Definition Tfa_body : ty :=
  TLolli None None (TPt (pt_dual (Pt (NVar 0) 0))) (TSess (SSeq (SRcv 0 TUnit) SEnd) (Pt (NVar 0) 0)).
Definition Tfa : ty := TBox 1 0 (BCs [] (λ _, False)) (TLolli None None TUnit Tfa_body).

(** Under syntactic points the body takes the point ῑ of the channel as
    its parameter in place of the unit (sharp edges 173). *)
Definition faca : expr :=
  EBox (Lam (let_new_pair_at (Var 0)
    (LetU (App ESpawn (Lam (LetU (Var 0) (sendclose (Var 2))))) (Var 0)))).

Definition fa_main : expr :=
  LetP (Pair faca EUnit) (LetU (Var 0)
    (LetP (Pair (App (App EForce (Var 1)) (EPt (pt_dual (pc 0 0))))
                (App (App EForce (Var 1)) (EPt (pt_dual (pc 1 0)))))
      (LetU (recvclose (Var 1)) (recvclose (Var 0))))).

Lemma faca_typed Ψ F : typed wnil ∅ Ψ ∅ [] F faca Tfa.
Proof.
  set (W := wnil). pose proof wnil_strict as HWs. pose proof (proj1 HWs) as HW. unfold faca, Tfa.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ None None 1); [set_solver|cbn; set_solver|].
  cbn. unfold let_new_pair_at. apply (t_new_v W _ _ _ _ _ _ _ Sd (pt_dual (Pt (NVar 0) 0)) _ HWs).
  { intros F'. cbn. tstep. }
  { right. eexists _, _, (pvar 0). split_and!; [apply elem_of_app; right; by left|by left|done]. }
  cbn. tstep; [|tstep].
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (Pt (NVar 0) 1))) (Some (Pt (NVar 0) 0)) 2);
    [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
  - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pt_dual (Pt (NVar 0) 0))); cbn; set_solver|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (Pt (NVar 0) 1)). split; [done|]. right. apply (slt_po W _ (pt_dual (Pt (NVar 0) 0)) HW).
  - apply KTClos.
  - done.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (Pt (NVar 0) 1)). split; [done|]. apply sle_refl, HW.
Qed.

(** fa_main starts with the top-level variables a = 0 and b = 1 under
    a ≺ b̄ and a+1 ≺ b̄. *)
Definition fa_fact (g : fact) : Prop :=
  g = FLt (pv 0 0) (pt_dual (pv 1 0)) ∨ g = FLt (pv 0 1) (pt_dual (pv 1 0)).
Definition Cfa : bcs := BCs [] fa_fact.

(** Under syntactic points a and b are the constants 0 and 1 of the
    hypotheses [fa_Ψ], b under the two facts of [Cfa], so that main can
    write the literals ā and b̄. *)
Definition fa_L : list (point * bool) := [(pc 0 0, false); (pc 0 1, false)].

Definition fa_Ψ : hyps := ([] ++ [(fresh_bcs [] [], [pconst 0])]) ++ [(freshp_bcs fa_L [], [pconst 1])].

Lemma fa_created : created (Wpo []) fa_Ψ.
Proof.
  apply created_p; [apply created_lh; [constructor|constructor|set_solver|fresh_const]| | |fresh_const].
  { cbn. repeat (apply Forall_cons; split; [eapply skn_inst; [by left|by left|done]|]). by apply Forall_nil. }
  { intros l h b _ Hh. by apply elem_of_nil in Hh. }
Qed.

Lemma fa_typed : styped ∅ fa_Ψ [] (∅, None) fa_main TUnit.
Proof.
  apply styped_Wpo. set (W := Wpo []). pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  unfold fa_main, fa_Ψ. match goal with |- typed _ _ ?Ψ0 _ _ _ _ _ => set (Ψ := Ψ0) end.
  assert (slt W Ψ (pc 0 0) (pt_dual (pc 1 0))) as H1.
  { apply (slt_freshp_l W Ψ fa_L [] (pconst 1) (pc 0 0) false); [by right; left|by left]. }
  assert (slt W Ψ (pc 0 1) (pt_dual (pc 1 0))) as H2.
  { apply (slt_freshp_l W Ψ fa_L [] (pconst 1) (pc 0 1) false); [by right; left|by right; left]. }
  assert (∀ a b, a < 2 → skn W Ψ (MkPt (NConst a) b 0)) as Hk.
  { intros a b Ha. right. destruct a as [|[|a]]; [| |lia].
    - exists (fresh_bcs [] []), [pconst 0], (pconst 0). split_and!; [by left|by left|done].
    - exists (freshp_bcs fa_L []), [pconst 1], (pconst 1). split_and!; [by right; left|by left|done]. }
  assert (∀ (F : sfuture) a, a < 2 →
    typed W ∅ Ψ ∅ [None; Some Tfa] F (App (App EForce (Var 1)) (EPt (pt_dual (pc a 0))))
      (TSess (SSeq (SRcv 0 TUnit) SEnd) (pc a 0))) as Hreq.
  { intros F a Ha. eapply tv_app; [exact HW|reflexivity| | |apply ubs_none].
    - cbn. apply (typed_force0 W _ _ _ _ _ _ 1 (BCs [] (λ _, False)) None Tfa_body [pc a 0]);
        [done|done| | |apply ubs_none|tstep].
      + apply bcs_hold_intro. by intros ? [].
      + constructor; [by apply Hk|constructor].
    - tstep. by apply Hk. }
  tstep.
  { tstep; [tstep|apply faca_typed]. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [apply (Hreq _ 1); lia|apply (Hreq _ 0); lia]. }
  cbn. tstep.
  - unfold recvclose. tstep.
    + tstep; [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
    + cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
  - unfold recvclose. tstep.
    + tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
    + cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma Cfa_acyclic : c0_acyclic 2 Cfa.
Proof.
  apply (c0_acyclic_rank 2 _ (vrank 10)); [apply vrank_shift| |apply vrank_dual].
  intros x y [[= -> ->]|[= -> ->]]; cbn; lia.
Qed.

Lemma fa_deadlock_free : deadlock_free (∅, {[+ fa_main +]}).
Proof. apply (soundness_created_s fa_Ψ _ TUnit fa_created); [constructor|apply fa_typed]. Qed.
