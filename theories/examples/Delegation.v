(** * delegation: typable

    delegation = let (c, c′) = new ∗ in let (d, d′) = new ∗ in
                 let () = spawn (λu. let () = u in let (e, c′) = recv c′ in
                                     let () = close (send ⟨∗, e⟩) in close c′) in
                 let (c, u) = ⟨send ⟨d, c⟩, ∗⟩ in let () = u in
                 let (x, d′) = recv d′ in let () = x in let () = close d′ in close c

    c : !(∃ι. (!∗.Close)@ι).Close@(a,0). The receiver gets d at the slot
    (a,0)[0], written s below, and acts on it while it holds c′ at
    (a,1), so it needs (s,0) ≺ (a,1) and (s,1) ≺ (a,1): this is the
    spec's c[k][1] ≺ (c,k+1), slots counted from 0 here. The sender
    creates d at s itself, so the alias of the spec is the choice of
    the point of [new]. send asks (a,0) ≺ (s,0) (KTSend, {ι} ≺ heads of
    the payload), which the sender also needs because it holds d′ at s.
    ⟨send ⟨d, c⟩, ∗⟩ stands for a let of one variable. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition Sdel : sty := SSeq (SSnd 1 (TSess Sd (pvar 0))) SEnd.
Abbreviation ps k := (Pt (NSlot (NConst 0) 0 0) k).

Definition deleg_thunk : expr :=
  Lam (LetU (Var 0) (LetP (App ERecv (Var 3))
    (LetU (App EClos (App ESend (Pair EUnit (Var 1)))) (App EClos (Var 0))))).

Definition deleg_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn deleg_thunk)
      (LetP (Pair (App ESend (Pair (Var 1) (Var 3))) EUnit)
        (LetU (Var 0)
          (LetP (App ERecv (Var 2))
            (LetU (Var 1) (LetU (App EClos (Var 0)) (App EClos (Var 3))))))))).

Lemma deleg_typed W : world_wf W → pt_known W (pc 0 0) →
  w_lt W (pc 0 0) (ps 0) → w_lt W (ps 1) (pc 0 1) →
  typed W ∅ [] ∅ [] (∅, None) deleg_main TUnit.
Proof.
  intros HW Ha H1 H2.
  assert (w_lt W (ps 0) (pc 0 1)) as H3.
  { eapply (wf_lt_trans _ HW); [apply (wf_lt_po _ HW (ps 0))|exact H2]. }
  assert (pt_known W (ps 0)) as Hs by exact Ha.
  unfold deleg_main.
  tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sdel (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sd (ps 0) (or_introl Hs))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + tstep; [tstep|apply (KTRecv _ _ _ 1 (TSess Sd (pvar 0)) SEnd (pc 0 0))|kscope|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 0 1). split; [done|]. right. apply (slt_po W _ (pc 0 0) HW).
      + cbn. tstep.
        * tstep.
          -- tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (ps 0)); cbn; set_solver|done|].
             ++ tstep; tstep.
             ++ apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
                exists (pc 0 1). split; [done|]. right. by apply sl_w.
          -- apply KTClos.
          -- done.
          -- apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
             exists (pc 0 1). split; [done|]. right. by apply sl_w.
        * tstep; [tstep|apply KTClos|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 0 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|].
    tstep; [|apply (KTSend _ _ _ 1 (TSess Sd (pvar 0)) SEnd (pc 0 0))| |].
    - tstep; tstep.
    - cbn. intros h Hh. mem_cases Hh. by apply sl_w.
    - kscope.
    - apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w. }
  tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Definition Wdeleg : world := Wfacts [0] [(pc 0 0, ps 0); (ps 1, pc 0 1)].

Definition kdel (p : pname) : nat := match p with NConst _ => 10 | _ => 1 end.

Lemma Wdeleg_strict : strict Wdeleg.
Proof.
  apply (Wfacts_strict _ _ kdel (λ _, 0) (λ _ _ _, 15)); [intros []; cbn; lia| |].
  - repeat apply Forall_cons_2; try apply Forall_nil_2; cbn; set_solver.
  - repeat apply Forall_cons_2; try apply Forall_nil_2; cbn; lia.
Qed.

Lemma deleg_deadlock_free : deadlock_free (∅, {[+ deleg_main +]}).
Proof.
  apply (soundness Wdeleg _ TUnit Wdeleg_strict).
  apply ptyped_closed; [constructor|]. apply deleg_typed; [apply Wdeleg_strict| | |].
  - apply Wfacts_known. set_solver.
  - apply Wfacts_lt. set_solver.
  - apply Wfacts_lt. set_solver.
Qed.
