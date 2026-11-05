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
    name b̄, the partner of y at b. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Lemma pvar_unknown W a : world_wf W → ¬ pt_known W (pvar a).
Proof. intros HW Hk. destruct (wf_names_const _ HW _ Hk) as [b Hb]. done. Qed.

Definition Tfac_body : ty := TLolli None None TUnit (TSess (SSeq (SRcv 0 TUnit) SEnd) (pv 0 0)).
Definition Tfac : ty := TBox 0 0 (BCs [] (λ _, False)) (TLolli None None TUnit Tfac_body).

Definition fac : expr :=
  EBox (Lam (LetU (Var 0) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (sendclose (Var 2))))) (Var 0))))).

Definition request : expr := recvclose (App (App EForce (Var 1)) EUnit).

Definition fac_main : expr :=
  LetP (Pair fac EUnit) (LetU (Var 0) (LetU request request)).

(** fac_main starts with one top-level variable a and no fact. *)
Definition Cfac : bcs := BCs [] (λ _, False).

Lemma fac_typed : styped ∅ [(Cfac, ids 1)] [] (∅, None) fac_main TUnit.
Proof.
  apply styped_wnil. set (W := wnil). pose proof wnil_strict as HWs. pose proof (proj1 HWs) as HW. unfold fac_main.
  tstep.
  { tstep; [tstep|].
    apply (t_exp W _ _ _ _ _ 0 0 (BCs [] (λ _, False)) None Tfac_body 0); [by apply allunl_unl|set_solver|box_k0].
    cbn. eapply (tv_lam W HW _ _ _ _ _ TUnit _ None None 1); [set_solver|cbn; set_solver|].
    cbn. tstep; [tstep|]. cbn. apply (t_new_at W _ _ _ _ _ _ _ Sd (pt_dual (pv 0 0)) HWs).
    { right. exists Cfac, [pv 0 0], (pv 0 0). split_and!; [by left|by left|done]. }
    cbn. tstep; [|tstep].
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 0 1))) (Some (pv 0 0)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pt_dual (pv 0 0))); cbn; set_solver|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual (pv 0 1)). split; [done|]. right. apply (slt_po W _ (pt_dual (pv 0 0)) HW).
    - apply KTClos.
    - done.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_dual (pv 0 1)). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  assert (∀ P, (∀ y, y ∈ P → False) →
    typed W ∅ [(Cfac, ids 1)] ∅ [None; Some Tfac] (P, None) request TUnit) as Hreq.
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
Proof. apply (c0_acyclic_rank 1 _ (vrank 1)); [apply vrank_shift|by intros ? ? []|by intros ? ? []|apply vrank_dual]. Qed.

Lemma fac_deadlock_free : deadlock_free (∅, {[+ fac_main +]}).
Proof. apply (soundness_source 1 Cfac _ TUnit (c0_acyclic_creation _ _ Cfac_acyclic)); [constructor|apply fac_typed]. Qed.

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

Definition Tfa_body : ty := TLolli None None TUnit (TSess (SSeq (SRcv 0 TUnit) SEnd) (Pt (NVar 0) 0)).
Definition Tfa : ty := TBox 1 0 (BCs [] (λ _, False)) (TLolli None None TUnit Tfa_body).

Definition faca : expr := fac.

Definition fa_main : expr :=
  LetP (Pair faca EUnit) (LetU (Var 0)
    (LetP (Pair (App (App EForce (Var 1)) EUnit) (App (App EForce (Var 1)) EUnit))
      (LetU (recvclose (Var 1)) (recvclose (Var 0))))).

Lemma faca_typed Ψ F : typed wnil ∅ Ψ ∅ [] F faca Tfa.
Proof.
  set (W := wnil). pose proof wnil_strict as HWs. pose proof (proj1 HWs) as HW. unfold faca, fac, Tfa.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  cbn. eapply (tv_lam W HW _ _ _ _ _ TUnit _ None None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. apply (t_new_at W _ _ _ _ _ _ _ Sd (pt_dual (Pt (NVar 0) 0)) HWs).
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

Lemma fa_typed : styped ∅ [(Cfa, ids 2)] [] (∅, None) fa_main TUnit.
Proof.
  apply styped_wnil. set (W := wnil). set (Ψ := [(Cfa, ids 2)]).
  pose proof wnil_strict as HWs. pose proof (proj1 HWs) as HW. unfold fa_main.
  assert (∀ x y, fa_fact (FLt x y) → slt W Ψ x y) as Hf.
  { intros x y Hxy. apply (sl_hyp0 W Ψ fa_fact (ids 2) x y); [by left|done| | |].
    - destruct Hxy as [[= -> ->]|[= -> ->]]; cbn; lia.
    - apply pt_inst_ids. destruct Hxy as [[= -> ->]|[= -> ->]]; cbn; lia.
    - apply pt_inst_ids. destruct Hxy as [[= -> ->]|[= -> ->]]; cbn; lia. }
  assert (slt W Ψ (pv 0 0) (pt_dual (pv 1 0))) as H1 by (apply Hf; by left).
  assert (slt W Ψ (pv 0 1) (pt_dual (pv 1 0))) as H2 by (apply Hf; by right).
  assert (∀ (F : sfuture) a, a < 2 →
    typed W ∅ Ψ ∅ [None; Some Tfa] F (App (App EForce (Var 1)) EUnit)
      (TSess (SSeq (SRcv 0 TUnit) SEnd) (pv a 0))) as Hreq.
  { intros F a Ha. eapply tv_app; [exact HW|reflexivity| |tstep|apply ubs_none].
    cbn. apply (typed_force0 W _ _ _ _ _ _ 1 (BCs [] (λ _, False)) None Tfa_body [pv a 0]);
      [done|done| | |apply ubs_none|tstep].
    - apply bcs_hold_intro. by intros ? [].
    - constructor; [|constructor]. right. exists Cfa, (ids 2), (pvar a). split_and!; [by left| |done].
      unfold ids. apply list_elem_of_fmap. exists a. split; [done|]. apply elem_of_seq. lia. }
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
  apply (c0_acyclic_rank 2 _ (vrank 10)); [apply vrank_shift|by intros ? ? [?|?]| |apply vrank_dual].
  intros x y [[= -> ->]|[= -> ->]]; cbn; lia.
Qed.

Lemma fa_deadlock_free : deadlock_free (∅, {[+ fa_main +]}).
Proof. apply (soundness_source 2 Cfa _ TUnit (c0_acyclic_creation _ _ Cfa_acyclic)); [constructor|apply fa_typed]. Qed.
