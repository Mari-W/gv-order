(** * The classic deadlock (Mordido and Pérez 2026, p. 3): rejected

      T = ?∗;Close
      f = λp. let (x, y) = p in let (n, x) = recv x in
              let y = send ⟨n, y⟩ in close x; close y
      dl_main = let (a, a′) = new ∗ in let (b, b′) = new ∗ in
                spawn (λu. let () = u in f ⟨a, b′⟩); f ⟨b, a′⟩

    Both threads receive first, each on the channel the other would
    send on, so both block. FreeST accepts the program. Mordido and
    Pérez reject it because f ⟨a, b′⟩ needs p < q and f ⟨b, a′⟩ needs
    q < p. The same two facts are what our system cannot meet. The
    receive in the first thread blocks at (a,0) while the frame holds
    b′ at (b,0), so E-App asks (a,0) ≺ (b,0). The second thread asks
    (b,0) ≺ (a,0). No strict world has both.

    We prove the rejection without an inversion of derivations. The
    program reaches a state where both threads wait on a receive, so
    it is not deadlock free ([dl_not_deadlock_free]), and [soundness]
    then rules out every typing at every strict world
    ([dl_untypable]). Int becomes ∗.

    The repair of Mordido and Pérez swaps the operations in one thread:
    g sends on a′ first and receives on b afterwards. It types in the
    lockstep world, with (a,0) ≺ (b,0) ≺ (a,1) ≺ (b,1)
    ([dlfix_deadlock_free]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.CfstTools.

Set Default Proof Using "All".

Definition dl_f : expr :=
  Lam (LetP (Var 0) (LetP (App ERecv (Var 1))
    (App (Lam (LetU (App EClos (Var 1)) (App EClos (Var 0)))) (App ESend (Pair (Var 1) (Var 2)))))).

Definition dl_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam (LetU (Var 0) (App dl_f (Pair (Var 4) (Var 1))))))
      (App dl_f (Pair (Var 1) (Var 2))))).

(** The blocked thread: it waits on a receive on c. *)
Definition dl_wait (c : chan) (d : chan) : expr :=
  LetP (App ERecv (Chan c))
    (App (Lam (LetU (App EClos (Var 1)) (App EClos (Var 0)))) (App ESend (Pair (Var 1) (Chan d)))).

Lemma dl_wait_step c d α e' : tstep (dl_wait c d) α e' → ∃ v, α = LSess (SRecv c v).
Proof.
  intros H. inversion H as [? ? ? Hh| | | | | |? ? ? ? H1| | |]; subst.
  - inversion Hh.
  - inversion H1 as [? ? ? Hh|? ? ? ? H2|? ? ? ? ? H2| | | | | | |]; subst.
    + inversion Hh; subst. by eexists.
    + exfalso. by apply (val_no_tstep _ _ _ H2).
    + exfalso. by apply (val_no_tstep _ _ _ H2).
Qed.

Lemma ms_pair_elem (e t1 t2 : expr) (E : gmultiset expr) :
  E ⊎ {[+ e +]} = {[+ t1 +]} ⊎ {[+ t2 +]} → e = t1 ∨ e = t2.
Proof.
  intros H. assert (e ∈ {[+ t1 +]} ⊎ {[+ t2 +]}) as He by (rewrite <-H; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He]; apply gmultiset_elem_of_singleton in He; auto.
Qed.

Lemma ms_pair_elem2 (e f t1 t2 : expr) (E : gmultiset expr) :
  E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ t1 +]} ⊎ {[+ t2 +]} → (e = t1 ∨ e = t2) ∧ (f = t1 ∨ f = t2).
Proof.
  intros H. split; [apply (ms_pair_elem e t1 t2 (E ⊎ {[+ f +]}))|apply (ms_pair_elem f t1 t2 (E ⊎ {[+ e +]}))];
    rewrite <-H; multiset_solver.
Qed.

(** Two threads that wait on receives make no τ step. *)
Lemma dl_stuck C c d c' d' p' : ¬ preduction (C, {[+ dl_wait c d +]} ⊎ {[+ dl_wait c' d' +]}) p'.
Proof.
  intros H. inversion H; subst.
  all: first [match goal with
       | Hm : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _, Ht : tstep ?e _ _ |- _ =>
           apply ms_pair_elem2 in Hm as [[-> | ->] _]; apply dl_wait_step in Ht as [? ?]; discriminate
       end|match goal with
       | Hm : _ ⊎ {[+ ?e +]} = _, Ht : tstep ?e _ _ |- _ =>
           apply ms_pair_elem in Hm as [-> | ->]; apply dl_wait_step in Ht as [? ?]; discriminate
       end].
Qed.

Lemma ms_one (e : expr) : ({[+ e +]} : gmultiset expr) = ∅ ⊎ {[+ e +]}.
Proof. multiset_solver. Qed.

Ltac pbeta := eapply rtc_l; [apply PStepBeta|].

Lemma dl_not_deadlock_free : ¬ deadlock_free (∅, {[+ dl_main +]}).
Proof.
  intros Hdf.
  assert (∃ p', pred_star (∅, {[+ dl_main +]}) p' ∧ ¬ safe p') as (p' & Hp & Hs).
  2: { exact (Hs (Hdf p' Hp)). }
  eexists. split.
  - rewrite ms_one. unfold dl_main.
    eapply rtc_l; [apply (PStepNew _ _ _ "a"%string); [apply TStepLetP, TStepHead, HeadNew|set_solver|
      unfold echans; rewrite gmultiset_elements_empty; set_solver|cbn; set_solver]|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    eapply rtc_l; [apply (PStepNew _ _ _ "b"%string); [apply TStepLetP, TStepHead, HeadNew|set_solver|
      unfold echans; rewrite gmultiset_elements_empty; set_solver|cbn; set_solver]|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    eapply rtc_l; [apply PStepSpawn, TStepLetU, TStepHead, HeadSpawn; done|].
    (* the spawned thread up to its receive *)
    pbeta; [apply TStepHead, HeadApp; done|].
    pbeta; [apply TStepHead, HeadLetU|].
    pbeta; [apply TStepHead, HeadApp; done|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    (* main: f ⟨b, a⟩ up to its receive *)
    match goal with |- rtc _ (?C, (∅ ⊎ {[+ ?m +]}) ⊎ {[+ ?t +]}) _ =>
      replace ((∅ ⊎ {[+ m +]}) ⊎ {[+ t +]}) with ({[+ t +]} ⊎ {[+ m +]} : gmultiset expr)
        by multiset_solver end.
    pbeta; [apply TStepHead, HeadLetU|].
    pbeta; [apply TStepHead, HeadApp; done|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    apply rtc_refl.
  - intros [(v & E & Heq & _)|(p'' & Hst)].
    + injection Heq as Hc _. set_solver.
    + eapply dl_stuck. exact Hst.
Qed.

Lemma dl_untypable : ¬ ∃ W, strict W ∧ typed W ∅ [] ∅ [] (∅, None) dl_main TUnit.
Proof.
  intros (W & HW & Ht). apply dl_not_deadlock_free.
  apply (soundness W _ TUnit HW). apply ptyped_closed; [constructor|exact Ht].
Qed.

(** ** The repair: g sends first

      g = λp. let (x, y) = p in let y = send ⟨∗, y⟩ in let (n, x) = recv x in
              let () = n in close y; close x
      dlfix_main = let (a, a′) = new ∗ in let (b, b′) = new ∗ in
                   spawn (λu. let () = u in f ⟨a, b′⟩); g ⟨b, a′⟩

    f blocks at (a,0), (b,0), (a,1), (b,1) in this order and so does g,
    each action below the points the thread still holds. *)

Definition dl_g : expr :=
  Lam (LetP (Var 0) (LetP (Pair (App ESend (Pair EUnit (Var 0))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 3)) (LetU (Var 1) (LetU (App EClos (Var 3)) (App EClos (Var 0)))))))).

Definition dlfix_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam (LetU (Var 0) (App dl_f (Pair (Var 4) (Var 1))))))
      (App dl_g (Pair (Var 1) (Var 2))))).

Definition dlT : sty := SSeq (SRcv 0 TUnit) SEnd.

Section dlfix.
  Context (W : world) (HW : world_wf W).
  Context (Ha : pt_known W (pc 0 0)) (Hb : pt_known W (pc 1 0)).
  Context (Hab : ∀ k, w_lt W (pc 0 k) (pc 1 k)) (Hba : ∀ k, w_lt W (pc 1 k) (pc 0 (S k))).

  Lemma dl_ord Ψ : slt W Ψ (pc 0 0) (pc 1 0) ∧ slt W Ψ (pc 1 0) (pc 0 1) ∧ slt W Ψ (pc 0 1) (pc 1 1) ∧
                   slt W Ψ (pc 0 0) (pc 1 1) ∧ slt W Ψ (pc 1 0) (pc 1 1).
  Proof.
    assert (slt W Ψ (pc 0 0) (pc 1 0)) as H1 by apply sl_w, Hab.
    assert (slt W Ψ (pc 1 0) (pc 0 1)) as H2 by apply sl_w, Hba.
    assert (slt W Ψ (pc 0 1) (pc 1 1)) as H3 by apply sl_w, Hab.
    assert (slt W Ψ (pc 1 0) (pc 1 1)) as H5 by (eapply sl_trans; [exact H2|exact H3]).
    split_and!; try done. eapply sl_trans; [exact H1|exact H5].
  Qed.

  Lemma dl_f_typed Ψ F :
    typed W (<[0:=Some (pc 1 1)]> ∅) Ψ ∅ [None; None; None; None; None] F dl_f
      (TLolli (Some (pc 1 1)) None (TProd (TSess dlT (pc 0 0)) (TSess (dual dlT) (pc 1 0))) TUnit).
  Proof.
    destruct (dl_ord Ψ) as (H1 & H2 & H3 & H4 & H5). unfold dl_f.
    eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pc 0 0)) (TSess dlT (pc 0 0))); [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact H1|].
      exists (pc 1 1). split; [done|]. by right. }
    cbn. eapply (tv_app W HW _ _ _ _ _ _ (Some (pc 1 1)) (Some (pc 0 1)) (TSess SEnd (pc 1 1)) TUnit);
      [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ _ _ _ _ 2); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 0 1)) (TSess SEnd (pc 0 1))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; exact H3|].
        exists (pc 1 1). split; [done|]. by right.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 1 1)) (TSess SEnd (pc 1 1))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 1 1). split; [done|]. apply sle_refl, HW.
    - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 1 0)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) (pc 1 0)))).
      + tstep; tstep.
      + apply (KTSend _ _ _ 0 TUnit SEnd (pc 1 0)). cbn. set_solver.
      + kscope.
      + apply ubs_intro; [intros y Hy; mem_cases Hy; exact H2|].
        exists (pc 1 1). split; [done|]. by right.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 1). split; [done|]. apply sle_refl, HW.
  Qed.
  Lemma dl_g_typed Ψ F :
    typed W ∅ Ψ ∅ [None; None; None; None] F dl_g
      (TLolli (Some (pc 1 1)) None (TProd (TSess dlT (pc 1 0)) (TSess (dual dlT) (pc 0 0))) TUnit).
  Proof.
    destruct (dl_ord Ψ) as (H1 & H2 & H3 & H4 & H5). unfold dl_g.
    eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 0); [set_solver|cbn; set_solver|].
    cbn. tstep; [tstep|]. cbn. tstep.
    { tstep; [tstep|].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 0 0)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) (pc 0 0)))).
      - tstep; tstep.
      - apply (KTSend _ _ _ 0 TUnit SEnd (pc 0 0)). cbn. set_solver.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; exact H1|].
        exists (pc 1 1). split; [done|]. by right. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pc 1 0)) (TSess dlT (pc 1 0))); [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact H2|].
      exists (pc 1 1). split; [done|]. by right. }
    cbn. tstep; [tstep|]. cbn. tstep.
    + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 0 1)) (TSess SEnd (pc 0 1))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact H3|].
      exists (pc 1 1). split; [done|]. by right.
    + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pc 1 1)) (TSess SEnd (pc 1 1))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 1). split; [done|]. apply sle_refl, HW.
  Qed.

  Lemma dlfix_typed : typed W ∅ [] ∅ [] (∅, None) dlfix_main TUnit.
  Proof.
    unfold dlfix_main. destruct (dl_ord []) as (H1 & H2 & H3 & H4 & H5).
    tstep.
    { tstep; [tstep|apply (KTNew _ _ _ dlT (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
    cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ dlT (pc 1 0) (or_introl Hb))|done|apply ubs_none]. }
    cbn. tstep.
    { tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 1)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; exact H1]. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity|apply dl_f_typed| |].
      - eapply (tv_pair W HW _ _ _ _ _ _ (TSess dlT (pc 0 0))); [reflexivity|tstep|tstep].
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 1 1). split; [done|]. apply sle_refl, HW. }
    cbn. eapply tv_app; [exact HW|reflexivity|apply dl_g_typed| |].
    - eapply (tv_pair W HW _ _ _ _ _ _ (TSess dlT (pc 1 0))); [reflexivity|tstep|tstep].
    - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  Qed.
End dlfix.

Lemma dlfix_deadlock_free : deadlock_free (∅, {[+ dlfix_main +]}).
Proof.
  apply (soundness Wtree _ TUnit Wtree_strict).
  apply ptyped_closed; [constructor|]. apply dlfix_typed; [apply Wtree_strict| | | |].
  - unfold pt_known, Wtree. simpl. set_solver.
  - unfold pt_known, Wtree. simpl. set_solver.
  - intros k. apply glt_base. exists k. by left.
  - intros k. apply glt_base. exists k. by right; left.
Qed.
