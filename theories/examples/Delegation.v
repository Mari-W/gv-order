(** * delegation: typable

    delegation = let (c, c′) = new ∗ in let (d, d′) = new ∗ in
                 let () = spawn (λu. let () = u in let (e, c′) = recv c′ in
                                     let () = close (send ⟨∗, e⟩) in close c′) in
                 let (c, u) = ⟨send ⟨d, c⟩, ∗⟩ in let () = u in
                 let (x, d′) = recv d′ in let () = x in let () = close d′ in close c

    c : !(∃ι. (!∗.Close)@ι).Close@(a,0). The receiver gets d at the point
    (a,0)[0], written s below, and acts on it while it holds c′ at
    (a,1), so it needs (s,0) ≺ (a,1) and (s,1) ≺ (a,1): this is the
    spec's (c,k)[1] ≺ (c,k+1), with positions counted from 0 here. The sender
    creates d at s itself, so the alias of the spec is the choice of
    the point of [new]. send asks (a,0) ≺ (s,0) (KTSend, {ι} ≺ heads of
    the payload), which the sender also needs because it holds d′ at s.
    ⟨send ⟨d, c⟩, ∗⟩ stands for a let of one variable.

    The program types in the empty world. c is created with the creation
    constraint {ι ≺ ι[0], ι[0]+1 ≺ ι+1}, two facts between ι and its own
    payload point, and d by the alias at ι[0] (sharp edges 105). The
    points (a,k) and s above are ι+k and ι[0]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition Sdel : sty := SSeq (SSnd 1 (TSess Sd (pvar 0))) SEnd.
Abbreviation ps k := (Pt (NPayload (NConst 0) 0 0) k).

Definition deleg_thunk : expr :=
  Lam (LetU (Var 0) (LetP (App ERecv (Var 3))
    (LetU (App EClos (App ESend (Pair EUnit (Var 1)))) (App EClos (Var 0))))).

Definition deleg_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn deleg_thunk)
      (LetP (Pair (App ESend (Pair (Var 1) (Var 3))) EUnit)
        (LetU (Var 0)
          (LetP (App ERecv (Var 2))
            (LetU (Var 1) (LetU (App EClos (Var 0)) (App EClos (Var 3))))))))).

(** The creation constraint of c: ι ≺ ι[0] and ι[0]+1 ≺ ι+1. Both facts
    stay inside ι, and the rank 10·k for ι+k and 5 + o for ι[0]+o
    orders them (sharp edges 105). *)
Abbreviation sd k := (Pt (NPayload (NVar 0) 0 0) k).

Definition dl_P (g : fact) : Prop := g = FLt (pv 0 0) (sd 0) ∨ g = FLt (sd 1) (pv 0 1).
Definition dl_C : bcs := BCs [] dl_P.

Definition dl_rank (x : point) : nat :=
  match pt_name x with
  | NVar 0 => 10 * pt_off x
  | NPayload (NVar 0) 0 0 => 5 + pt_off x
  | _ => pt_off x
  end.

Lemma dl_ok peq plt : cc_ok peq plt dl_C.
Proof.
  apply (cc_ok_inner peq plt dl_P (λ x y, dl_rank x < dl_rank y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [n o] _. unfold dl_rank, pt_shift. simpl. repeat case_match; lia.
  - intros g [-> | ->] _; eexists _, _; (split; [done|]); cbn; lia.
Qed.

Lemma deleg_typed : styped ∅ [] [] (∅, None) deleg_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold deleg_main.
  apply (t_new_open W _ _ ∅ _ _ _ _ Sdel dl_C); [apply dl_ok|constructor|].
  fresh_clean.
  set (Ψ := [(dl_C, [pvar 0])]).
  assert (slt W Ψ (pv 0 0) (sd 0)) as H1.
  { eapply (sl_hyp0 _ _ _ _ (pv 0 0) (sd 0)); [by left|by left|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (sd 1) (pv 0 1)) as H2.
  { eapply (sl_hyp0 _ _ _ _ (sd 1) (pv 0 1)); [by left|by right|cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (sd 0) (pv 0 1)) as H3.
  { eapply sl_trans; [apply (slt_po W _ (sd 0) HW)|exact H2]. }
  apply (t_new_at W _ _ _ _ _ _ _ Sd (sd 0) HWs); [eapply skn_inst; [by left|by left|done]|].
  cbn. tstep.
  { tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pv 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + tstep; [tstep|apply (KTRecv _ _ _ 1 (TSess Sd (pvar 0)) SEnd (pv 0 0))|kscope|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW).
      + cbn. tstep.
        * tstep.
          -- tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (sd 0)); cbn; set_solver|done|].
             ++ tstep; tstep.
             ++ apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
                exists (pv 0 1). split; [done|]. right. done.
          -- apply KTClos.
          -- done.
          -- apply ubs_intro; [intros y Hy; mem_cases Hy; done|].
             exists (pv 0 1). split; [done|]. right. done.
        * tstep; [tstep|apply KTClos|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pv 0 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|].
    tstep; [|apply (KTSend _ _ _ 1 (TSess Sd (pvar 0)) SEnd (pv 0 0))| |].
    - tstep; tstep.
    - cbn. intros h Hh. mem_cases Hh. done.
    - kscope.
    - apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. done. }
  tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma deleg_deadlock_free : deadlock_free (∅, {[+ deleg_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply deleg_typed].
Qed.
