(** * The classic deadlock (Mordido and Pérez 2026, p. 3): rejected

      T = ?∗;Close
      f = λp. let (x, y) = p in let (n, x) = recv x in
              let y = send ⟨n, y⟩ in close x; close y
      dl_main = let (a, a′) = new ∗ in let (b, b′) = new ∗ in
                spawn (λu. let () = u in f ⟨a, b′⟩); f ⟨b, a′⟩

    Both threads receive first, each on the channel the other would
    send on, so both block. FreeST accepts the program. Mordido and
    Pérez reject it because f ⟨a, b′⟩ needs p < q and f ⟨b, a′⟩ needs
    q < p. The same two facts are what our system cannot meet. Let α
    and β be the points of a and b. The receive in the first thread
    blocks at α while the frame holds b′ at β, so E-App asks α ≺ β. The
    second thread asks β ≺ α. No acyclic context has both.

    We prove the rejection without an inversion of derivations. The
    program reaches a state where both threads wait on a receive, so
    it is not deadlock free ([dl_not_deadlock_free]). [soundness] then
    rules out a derivation of the closed program ([dl_untypable]), and
    [soundness_source] one under any top-level points with an acyclic
    constraint ([dl_untypable_source]). Int becomes ∗.

    The repair of Mordido and Pérez swaps the operations in one thread.
    g sends on a′ first and receives on b afterwards. It types with the
    lockstep creation constraints of Stream.v, α+k ≺ β+k ≺ α+k+1, which
    give α ≺ β ≺ α+1 ≺ β+1 ([dlfix_deadlock_free]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.CfstTools.

Set Default Proof Using "All".

Definition dl_f : expr :=
  Lam (LetP (Var 0) (LetP (App ERecv (Var 1))
    (App (Lam (LetU (App EClos (Var 1)) (App EClos (Var 0)))) (App ESend (Pair (Var 1) (Var 2)))))).

Definition dl_main : expr :=
  let_new_pair (let_new_pair
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
    eapply rtc_l; [apply (PStepNew _ _ _ "a"%string); [apply TStepLetP, TStepPairL, TStepHead, HeadNew|set_solver|
      unfold echans; rewrite gmultiset_elements_empty; set_solver|cbn; set_solver]|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    pbeta; [apply TStepHead, HeadLetU|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    eapply rtc_l; [apply (PStepNew _ _ _ "b"%string); [apply TStepLetP, TStepPairL, TStepHead, HeadNew|set_solver|
      unfold echans; rewrite gmultiset_elements_empty; set_solver|cbn; set_solver]|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    pbeta; [apply TStepHead, HeadLetU|].
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

(** No derivation exists, neither for the closed program nor under any
    top-level points with an acyclic constraint. *)
Theorem dl_untypable : ¬ styped ∅ [] [] (∅, None) dl_main TUnit.
Proof.
  intros Ht. apply dl_not_deadlock_free.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)). apply ptyped_closed_s; [constructor|exact Ht].
Qed.

Theorem dl_untypable_source n C0 : c0_acyclic n C0 → ¬ styped ∅ [(C0, ids n)] [] (∅, None) dl_main TUnit.
Proof.
  intros HC Ht. apply dl_not_deadlock_free.
  apply (soundness_source n C0 _ TUnit HC); [constructor|exact Ht].
Qed.

(** ** The repair: g sends first

      g = λp. let (x, y) = p in let y = send ⟨∗, y⟩ in let (n, x) = recv x in
              let () = n in close y; close x
      dlfix_main = let (a, a′) = new ∗ in let (b, b′) = new ∗ in
                   spawn (λu. let () = u in f ⟨a, b′⟩); g ⟨b, a′⟩

    f blocks at α, β, α+1, β+1 in this order and so does g,
    each action below the points the thread still holds. *)

Definition dl_g : expr :=
  Lam (LetP (Var 0) (LetP (Pair (App ESend (Pair EUnit (Var 0))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 3)) (LetU (Var 1) (LetU (App EClos (Var 3)) (App EClos (Var 0)))))))).

Definition dlfix_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App dl_f (Pair (Var 4) (Var 1))))))
      (App dl_g (Pair (Var 1) (Var 2))))).

Definition dlT : sty := SSeq (SRcv 0 TUnit) SEnd.

Section dlfix.
  Context (W : world) (HW : world_wf W) (Ψ : hyps).
  Context (Hab : ∀ k, slt W Ψ (pv 1 k) (pv 0 k)) (Hba : ∀ k, slt W Ψ (pv 0 k) (pv 1 (S k))).

  Lemma dl_ord : slt W Ψ (pv 1 0) (pv 0 0) ∧ slt W Ψ (pv 0 0) (pv 1 1) ∧ slt W Ψ (pv 1 1) (pv 0 1) ∧
                 slt W Ψ (pv 1 0) (pv 0 1) ∧ slt W Ψ (pv 0 0) (pv 0 1).
  Proof.
    assert (slt W Ψ (pv 1 0) (pv 0 0)) as H1 by apply Hab.
    assert (slt W Ψ (pv 0 0) (pv 1 1)) as H2 by apply Hba.
    assert (slt W Ψ (pv 1 1) (pv 0 1)) as H3 by apply Hab.
    assert (slt W Ψ (pv 0 0) (pv 0 1)) as H5 by (eapply sl_trans; [exact H2|exact H3]).
    split_and!; try done. eapply sl_trans; [exact H1|exact H5].
  Qed.

  Lemma dl_f_typed F :
    typed W (<[0:=Some (pv 0 1)]> ∅) Ψ ∅ [None; None; None; None; None; None; None; None; None] F dl_f
      (TLolli (Some (pv 0 1)) None (TProd (TSess dlT (pv 1 0)) (TSess (dual dlT) (pv 0 0))) TUnit).
  Proof.
    destruct dl_ord as (H1 & H2 & H3 & H4 & H5). unfold dl_f.
    eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 0)) (TSess dlT (pv 1 0))); [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact H1|].
      exists (pv 0 1). split; [done|]. by right. }
    cbn. eapply (tv_app W HW _ _ _ _ _ _ (Some (pv 0 1)) (Some (pv 1 1)) (TSess SEnd (pv 0 1)) TUnit);
      [reflexivity| | |].
    - eapply (tv_lam W HW _ _ _ _ _ _ _ _ _ 2); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 1)) (TSess SEnd (pv 1 1))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; exact H3|].
        exists (pv 0 1). split; [done|]. by right.
      + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 1)) (TSess SEnd (pv 0 1))); [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 0 1). split; [done|]. apply sle_refl, HW.
    - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 0 0)))).
      + tstep; tstep.
      + apply (KTSend _ _ _ 0 TUnit SEnd (pv 0 0)). cbn. set_solver.
      + kscope.
      + apply ubs_intro; [intros y Hy; mem_cases Hy; exact H2|].
        exists (pv 0 1). split; [done|]. by right.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
  Qed.
  Lemma dl_g_typed F :
    typed W ∅ Ψ ∅ [None; None; None; None; None; None; None; None] F dl_g
      (TLolli (Some (pv 0 1)) None (TProd (TSess dlT (pv 0 0)) (TSess (dual dlT) (pv 1 0))) TUnit).
  Proof.
    destruct dl_ord as (H1 & H2 & H3 & H4 & H5). unfold dl_g.
    eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 0); [set_solver|cbn; set_solver|].
    cbn. tstep; [tstep|]. cbn. tstep.
    { tstep; [tstep|].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) SEnd) (pv 1 0)))).
      - tstep; tstep.
      - apply (KTSend _ _ _ 0 TUnit SEnd (pv 1 0)). cbn. set_solver.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; exact H1|].
        exists (pv 0 1). split; [done|]. by right. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess dlT (pv 0 0))); [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact H2|].
      exists (pv 0 1). split; [done|]. by right. }
    cbn. tstep; [tstep|]. cbn. tstep.
    + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 1)) (TSess SEnd (pv 1 1))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact H3|].
      exists (pv 0 1). split; [done|]. by right.
    + eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 0 1)) (TSess SEnd (pv 0 1))); [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW.
  Qed.

End dlfix.

(** After both [new]s b is 0, a is 1 and the ceiling z is 2, as in
    Stream.v. *)
Lemma dlfix_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) dlfix_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold dlfix_main.
  apply (t_new_open W _ _ ∅ _ _ _ _ dlT lsa_C); [apply lsa_ok|..].
  { constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  apply (t_new_open W _ _ ∅ _ _ _ _ dlT lsb_C); [apply lsb_ok; by right; left|..].
  { constructor; [eapply skn_inst; [by right; left|by left|done]|].
    constructor; [eapply skn_inst; [by left|by left|done]|constructor]. }
  fresh_clean.
  set (Ψ := [(top_C0, [pvar 2]); (BCs [pvar 2] lsa_P, [pvar 1]); (BCs [pvar 1; pvar 2] lsb_P, [pvar 0])]).
  assert (∀ k, slt W Ψ (pv 1 k) (pv 0 k)) as Hab.
  { intros k. eapply (sl_hyp W Ψ [pvar 1; pvar 2] lsb_P [pvar 0] (FLt (pv 1 k) (pv 0 k)));
      [by right; right; left|exists k; by left|fsc|reflexivity]. }
  assert (∀ k, slt W Ψ (pv 0 k) (pv 1 (S k))) as Hba.
  { intros k. eapply (sl_hyp W Ψ [pvar 1; pvar 2] lsb_P [pvar 0] (FLt (pv 0 k) (pv 1 (S k))));
      [by right; right; left|exists k; by right; left|fsc|reflexivity]. }
  destruct (dl_ord W HW Ψ Hab Hba) as (H1 & H2 & H3 & H4 & H5).
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 0 1)) (Some (pv 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; exact H1]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity|apply (dl_f_typed W HW Ψ Hab Hba)| |].
    - eapply (tv_pair W HW _ _ _ _ _ _ (TSess dlT (pv 1 0))); [reflexivity|tstep|tstep].
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity|apply (dl_g_typed W HW Ψ Hab Hba)| |].
  - eapply (tv_pair W HW _ _ _ _ _ _ (TSess dlT (pv 0 0))); [reflexivity|tstep|tstep].
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem dlfix_deadlock_free : deadlock_free (∅, {[+ dlfix_main +]}).
Proof. apply (soundness_source 1 top_C0 _ TUnit top_acyclic); [constructor|apply dlfix_typed]. Qed.
