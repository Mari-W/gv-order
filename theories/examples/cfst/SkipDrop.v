(** * Dropping a channel at Skip (Mordido and Pérez 2026, Fig. 12 and Fig. 15)

      sd_main = let (x, y) = new (!∗;Skip) in
                spawn (λu. let () = u in (λ_. ∗) (send ⟨∗, x⟩));
                let (_, _) = recv y in ∗

    Both threads drop their end of the channel once it is at Skip. The
    rules of Mordido and Pérez type the program. Skip has priority ⊤
    (Fig. 4, p. 11), the context split S-Top copies a type of priority
    ⊤ into both halves (Fig. 12, p. 24), and T-Const and T-Var accept a
    rest of priority ⊤ (pp. 12, 25). Their structural congruence
    (Fig. 15, p. 30) removes the restriction once both threads are
    done, through (νxy)∘⟨()⟩ ≡ ∘⟨()⟩ and scope extrusion, so the final
    configuration is •⟨()⟩ and Definition 1 (p. 16) holds.

    Our semantics keeps a restricted name until a close or a link
    releases it, and [terminated] asks for no restricted name. The run
    of sd_main ends in ({a}, {[+ ∗; ∗ +]}), which makes no step and is
    not terminated ([sd_not_deadlock_free]). So no typing rule alone
    can let a thread drop a channel at Skip. The semantics has to
    release the name, or [terminated] has to accept restricted names
    that no thread mentions. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.CfstDeadlock.

Set Default Proof Using "All".

Definition sd_main : expr :=
  let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (Lam EUnit) (App ESend (Pair EUnit (Var 2)))))))
      (LetP (App ERecv (Var 0)) EUnit)).

Lemma sd_final_stuck C p' : ¬ preduction (C, {[+ EUnit +]} ⊎ {[+ EUnit +]}) p'.
Proof.
  intros H. inversion H; subst.
  all: first [match goal with
       | Hm : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _, Ht : tstep ?e _ _ |- _ =>
           apply ms_pair_elem2 in Hm as [[-> | ->] _]; exfalso; exact (val_no_tstep _ _ _ Ht I)
       end|match goal with
       | Hm : _ ⊎ {[+ ?e +]} = _, Ht : tstep ?e _ _ |- _ =>
           apply ms_pair_elem in Hm as [-> | ->]; exfalso; exact (val_no_tstep _ _ _ Ht I)
       end].
Qed.

Lemma sd_final_stuck' C e1 e2 p' : e1 = EUnit → e2 = EUnit →
  ¬ preduction (C, (∅ ⊎ {[+ e1 +]}) ⊎ {[+ e2 +]}) p'.
Proof.
  intros -> ->. replace ((∅ ⊎ {[+ EUnit +]}) ⊎ {[+ EUnit +]}) with ({[+ EUnit +]} ⊎ {[+ EUnit +]} : gmultiset expr)
    by multiset_solver. apply sd_final_stuck.
Qed.

Lemma sd_not_deadlock_free : ¬ deadlock_free (∅, {[+ sd_main +]}).
Proof.
  intros Hdf.
  assert (∃ p', pred_star (∅, {[+ sd_main +]}) p' ∧ ¬ safe p') as (p' & Hp & Hs).
  2: { exact (Hs (Hdf p' Hp)). }
  eexists. split.
  - rewrite ms_one. unfold sd_main.
    eapply rtc_l; [apply (PStepNew _ _ _ "a"%string); [apply TStepLetP, TStepPairL, TStepHead, HeadNew|set_solver|
      unfold echans; rewrite gmultiset_elements_empty; set_solver|cbn; set_solver]|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    pbeta; [apply TStepHead, HeadLetU|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    eapply rtc_l; [apply PStepSpawn, TStepLetU, TStepHead, HeadSpawn; done|].
    pbeta; [apply TStepHead, HeadApp; done|].
    pbeta; [apply TStepHead, HeadLetU|].
    match goal with |- rtc _ (?C, (∅ ⊎ {[+ ?m +]}) ⊎ {[+ ?t +]}) _ =>
      replace ((∅ ⊎ {[+ m +]}) ⊎ {[+ t +]}) with ((∅ ⊎ {[+ t +]}) ⊎ {[+ m +]} : gmultiset expr)
        by multiset_solver end.
    pbeta; [apply TStepHead, HeadLetU|].
    eapply rtc_l; [eapply (PStepMsg _ _ "a"%string EUnit);
      [apply TStepAppR; [done|]; apply TStepHead, HeadSend; done
      |apply TStepLetP, TStepHead, HeadRecv; done]|].
    pbeta; [apply TStepHead, HeadLetP; done|].
    match goal with |- rtc _ (?C, (∅ ⊎ {[+ ?m +]}) ⊎ {[+ ?t +]}) _ =>
      replace ((∅ ⊎ {[+ m +]}) ⊎ {[+ t +]}) with ((∅ ⊎ {[+ t +]}) ⊎ {[+ m +]} : gmultiset expr)
        by multiset_solver end.
    pbeta; [apply TStepHead, HeadApp; done|].
    apply rtc_refl.
  - intros [(v & E & Heq & _)|(p'' & Hst)].
    + injection Heq as Hc _. set_solver.
    + eapply (sd_final_stuck' _ _ _ p''); [reflexivity|reflexivity|exact Hst].
Qed.
