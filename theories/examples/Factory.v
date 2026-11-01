(** * factory: a box that yields a fresh session per request

    [fac] creates every session at one constant point (a,0). [faca] is
    the same body under □∀ι and creates the session at the point
    variable ι. No well-formed world knows a point variable
    ([pvar_unknown]), so new at ι types through the knownness of the
    box's own instance (sharp edges 59, 61).

      fac  = !(f = λu. let () = u in let (c, c′) = new ∗ in
                       let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)
           : □(∗ ⊸^⊥_⊤ (?∗.Close)@(a,0))
      main = let (f, u) = ⟨fac, ∗⟩ in let () = u in
             let () = recvclose ((force f) ∗) in recvclose ((force f) ∗)

    f is used twice (contraction at □). Both sessions live at (a,0), so
    the client must finish one before it requests the next. Holding
    both while it blocks on one would ask (a,0) ≺ (a,0). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Lemma pvar_unknown W a : world_wf W → ¬ pt_known W (pvar a).
Proof. intros HW Hk. destruct (wf_names_const _ HW _ Hk) as [b Hb]. done. Qed.

Definition Tfac_body : ty := TLolli None None TUnit (TSess (SRcv 0 TUnit SEnd) (pc 0 0)).
Definition Tfac : ty := TBox 0 (BCs [] (λ _, False)) (TLolli None None TUnit Tfac_body).

Definition fac : expr :=
  EBox (Lam (LetU (Var 0) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (sendclose (Var 2))))) (Var 0))))).

Definition request : expr := recvclose (App (App EForce (Var 1)) EUnit).

Definition fac_main : expr :=
  LetP (Pair fac EUnit) (LetU (Var 0) (LetU request request)).

Lemma fac_typed W : strict W → pt_known W (pc 0 0) →
  typed W ∅ [] ∅ [] (∅, None) fac_main TUnit.
Proof.
  intros HWs Ha. pose proof (proj1 HWs) as HW. unfold fac_main.
  tstep.
  { tstep; [tstep|].
    apply (t_box W _ _ _ _ _ 0 (BCs [] (λ _, False)) None Tfac_body 0); [by apply allunl_unl|set_solver|].
    cbn. eapply (tv_lam W HW _ _ _ _ _ TUnit _ None None 1); [set_solver|cbn; set_solver|].
    cbn. tstep; [tstep|]. cbn. apply (t_new_at W _ _ _ _ _ _ _ Sd (pc 0 0) HWs (or_introl Ha)).
    cbn. tstep; [|tstep].
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pc 0 0)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pc 0 0)); cbn; set_solver|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 0 1). split; [done|]. right. apply (slt_po W _ (pc 0 0) HW).
    - apply KTClos.
    - done.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  assert (∀ P, (∀ y, y ∈ P → False) →
    typed W ∅ [] ∅ [None; Some Tfac] (P, None) request TUnit) as Hreq.
  { intros P HP. unfold request, recvclose. tstep.
    - tstep; [| | |].
      + eapply tv_app; [exact HW|reflexivity| |tstep|apply ubs_none].
        cbn. apply (typed_force W _ _ _ _ _ _ 0 (BCs [] (λ _, False)) None Tfac_body []);
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

Lemma fac_deadlock_free : deadlock_free (∅, {[+ fac_main +]}).
Proof.
  apply (soundness (Wpo [0]) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply fac_typed; [apply Wpo_strict|].
  unfold pt_known, Wpo. simpl. set_solver.
Qed.

(** ** factory under □∀ι: typable (SHARP-EDGES 61)

      faca : □(∀ι. ∗ ⊸^⊥_⊤ (?∗.Close)@ι)      (the body of fac, new at ι)
      fa_main = let (f, u) = ⟨faca, ∗⟩ in let () = u in
                let (x, y) = ⟨(force f) ∗, (force f) ∗⟩ in
                let () = recvclose x in recvclose y

    new in the body creates the channel at the point variable ι. The
    static system reads ι as known, because it is a point of the body's
    own instance (skn, hyp_known), and force asks the instance known in
    the world. main forces at (a,0) and (b,0) and holds both sessions,
    which the one-point factory could not: x is used while y waits, so
    (a,0) ≺ (b,0) and (a,1) ≺ (b,0). *)

Definition Tfa_body : ty := TLolli None None TUnit (TSess (SRcv 0 TUnit SEnd) (Pt (NVar 0) 0)).
Definition Tfa : ty := TBox 1 (BCs [] (λ _, False)) (TLolli None None TUnit Tfa_body).

Definition faca : expr := fac.

Definition fa_main : expr :=
  LetP (Pair faca EUnit) (LetU (Var 0)
    (LetP (Pair (App (App EForce (Var 1)) EUnit) (App (App EForce (Var 1)) EUnit))
      (LetU (recvclose (Var 1)) (recvclose (Var 0))))).

Lemma faca_typed W F : strict W → typed W ∅ [] ∅ [] F faca Tfa.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold faca, fac, Tfa.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  cbn. eapply (tv_lam W HW _ _ _ _ _ TUnit _ None None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. apply (t_new_at W _ _ _ _ _ _ _ Sd (Pt (NVar 0) 0) HWs).
  { right. eexists _, _, (pvar 0). split_and!; [by left|by left|done]. }
  cbn. tstep; [|tstep].
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (Pt (NVar 0) 1)) (Some (Pt (NVar 0) 0)) 2);
    [set_solver| |].
  { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
  - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (Pt (NVar 0) 0)); cbn; set_solver|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (Pt (NVar 0) 1). split; [done|]. right. apply (slt_po W _ (Pt (NVar 0) 0) HW).
  - apply KTClos.
  - done.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (Pt (NVar 0) 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma fa_typed W : strict W → pt_known W (pc 0 0) → pt_known W (pc 1 0) →
  w_lt W (pc 0 0) (pc 1 0) → w_lt W (pc 0 1) (pc 1 0) →
  typed W ∅ [] ∅ [] (∅, None) fa_main TUnit.
Proof.
  intros HWs Ha Hb H1 H2. pose proof (proj1 HWs) as HW. unfold fa_main.
  assert (∀ (F : sframe) a, pt_known W (pc a 0) →
    typed W ∅ [] ∅ [None; Some Tfa] F (App (App EForce (Var 1)) EUnit)
      (TSess (SRcv 0 TUnit SEnd) (pc a 0))) as Hreq.
  { intros F a Hk. eapply tv_app; [exact HW|reflexivity| |tstep|apply ubs_none].
    cbn. apply (typed_force W _ _ _ _ _ _ 1 (BCs [] (λ _, False)) None Tfa_body [pc a 0]);
      [done|done| |constructor; [by left|constructor]|apply ubs_none|tstep].
    apply bcs_hold_intro. by intros ? []. }
  tstep.
  { tstep; [tstep|apply faca_typed, HWs]. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [apply Hreq, Hb|apply Hreq, Ha]. }
  cbn. tstep.
  - unfold recvclose. tstep.
    + tstep; [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|done].
    + cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|done].
  - unfold recvclose. tstep.
    + tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
    + cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Definition Wfa : world := Wfacts [0; 1] [(pc 0 0, pc 1 0); (pc 0 1, pc 1 0)].

Lemma Wfa_strict : strict Wfa.
Proof.
  apply (Wfacts_strict _ _ (λ _, 1) (λ a, 10 * a) (λ _ _ _, 0)); [lia| |].
  - repeat constructor; cbn; set_solver.
  - repeat constructor; cbn; lia.
Qed.

Lemma fa_deadlock_free : deadlock_free (∅, {[+ fa_main +]}).
Proof.
  apply (soundness Wfa _ TUnit Wfa_strict).
  apply ptyped_closed; [constructor|]. apply fa_typed; [apply Wfa_strict| | | |].
  - apply Wfacts_known. set_solver.
  - apply Wfacts_known. set_solver.
  - apply Wfacts_lt. set_solver.
  - apply Wfacts_lt. set_solver.
Qed.
