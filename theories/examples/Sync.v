(** * Example 2.1: sync

    The closed process that forks a partner, exchanges the unit over a
    fresh channel and terminates gracefully.  It is typable, so it is
    also the smallest witness that the fundamental property bites. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Support.

Local Open Scope string_scope.


(** λa. clos (send ⟨∗, a⟩) *)
Definition ffbody : expr := App EClos (App ESend (Pair EUnit (Var 0))).
Definition ff : expr := Lam ffbody.

(** let ⟨b,a⟩ = recv (fork ff) in let ∗ = b in clos a *)
Definition sync_body : expr := LetU (Var 1) (App EClos (Var 0)).
Definition sync_main : expr := LetP (App ERecv (App EFork ff)) sync_body.
Definition sync_proc : proc := (∅, {[+ sync_main +]}).

Lemma echans_empty : echans ∅ = ∅.
Proof. unfold echans. by rewrite gmultiset_elements_empty. Qed.

(** Intermediate states of the reduction of Example 2.1. *)
Definition t1 : expr := LetP (App ERecv (Chan "c")) sync_body.
Definition u1 : expr := App ff (Chan "c").
Definition u2 : expr := App EClos (App ESend (Pair EUnit (Chan "c"))).
Definition t2 : expr := LetP (Pair EUnit (Chan "c")) sync_body.
Definition u3 : expr := App EClos (Chan "c").
Definition t3 : expr := LetU EUnit (App EClos (Chan "c")).

Example sync_reduces :
  pred_star sync_proc (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]}).
Proof.
  (* fork *)
  eapply rtc_l.
  { unfold sync_proc.
    replace ({[+ sync_main +]} : gmultiset expr)
      with ((∅ : gmultiset expr) ⊎ {[+ sync_main +]}) by multiset_solver.
    eapply (PStepFork _ _ _ "c" ff t1).
    - unfold sync_main. apply TStepLetP. apply TStepAppR; [done|].
      apply TStepHead. by apply HeadFork.
    - set_solver.
    - rewrite echans_empty. set_solver.
    - simpl. set_solver. }
  (* β in the forked thread *)
  eapply rtc_l.
  { replace (∅ ∪ {["c"]}) with ({["c"]} : gset chan) by set_solver.
    replace ((∅ : gmultiset expr) ⊎ {[+ t1 +]} ⊎ {[+ App ff (Chan "c") +]})
      with ({[+ t1 +]} ⊎ {[+ u1 +]} : gmultiset expr) by multiset_solver.
    apply (PStepBeta _ {[+ t1 +]} u1 u2).
    apply TStepHead. apply (HeadApp ffbody (Chan "c")). done. }
  (* communication over c *)
  eapply rtc_l.
  { replace ({[+ t1 +]} ⊎ {[+ u2 +]} : gmultiset expr)
      with (((∅ : gmultiset expr) ⊎ {[+ u2 +]}) ⊎ {[+ t1 +]}) by multiset_solver.
    eapply (PStepMsg _ ∅ "c" EUnit u2 u3 t1 t2).
    - unfold u2. apply TStepAppR; [done|].
      apply TStepHead. by apply HeadSend.
    - unfold t1. apply TStepLetP.
      apply TStepHead. by apply HeadRecv. }
  (* β: pair elimination *)
  eapply rtc_l.
  { replace ((∅ : gmultiset expr) ⊎ {[+ u3 +]} ⊎ {[+ t2 +]})
      with ({[+ u3 +]} ⊎ {[+ t2 +]} : gmultiset expr) by multiset_solver.
    apply (PStepBeta _ {[+ u3 +]} t2 t3).
    unfold t2. apply TStepHead. by apply (HeadLetP EUnit (Chan "c")). }
  (* β: unit elimination *)
  eapply rtc_l.
  { apply (PStepBeta _ {[+ u3 +]} t3 u3).
    unfold t3. apply TStepHead. apply HeadLetU. }
  (* close *)
  eapply rtc_l.
  { replace ({[+ u3 +]} ⊎ {[+ u3 +]} : gmultiset expr)
      with (((∅ : gmultiset expr) ⊎ {[+ u3 +]}) ⊎ {[+ u3 +]}) by multiset_solver.
    eapply (PStepClose _ ∅ "c" u3 EUnit u3 EUnit).
    - apply TStepHead. apply HeadClos.
    - apply TStepHead. apply HeadClos.
    - set_solver. }
  replace ({["c"]} ∖ {["c"]}) with (∅ : gset chan) by set_solver.
  replace ((∅ : gmultiset expr) ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]})
    with ({[+ EUnit +]} ⊎ {[+ EUnit +]} : gmultiset expr) by multiset_solver.
  apply rtc_refl.
Qed.

(** ** Example 2.8: blocked *)

(** The session type of the forked channel, seen from the forked
    thread: send a unit, then close. *)
Definition Sff : sty := SSnd TUnit SEnd.

Example sync_typed : ptyped ∅ sync_proc TUnit.
Proof.
  apply ptyped_term; [constructor|].
  (* let ⟨b,a⟩ = recv (fork ff) in sync_body *)
  eapply (typed_letp _ ∅ ∅ _ [] [] _ _ TUnit (TSess SEnd));
    [apply senv_split_empty_l|constructor| |].
  - (* recv (fork ff) : ∗ ⊗ SEnd *)
    eapply (typed_app _ ∅ ∅ _ [] [] _ _ (TSess (SRcv TUnit SEnd)));
      [apply senv_split_empty_l|constructor| |].
    + apply typed_konst; [auto|]. apply (KTRecv TUnit SEnd).
    + (* fork ff : dual Sff = ?∗.Close *)
      eapply (typed_app _ ∅ ∅ _ [] [] _ _ (TLolli (TSess Sff) TUnit));
        [apply senv_split_empty_l|constructor| |].
      * apply typed_konst; [auto|]. apply (KTFork Sff).
      * (* ff = λa. clos (send ⟨∗,a⟩) *)
        apply typed_lam.
        eapply (typed_app _ ∅ ∅ _ [None] [Some (TSess Sff)]
                  _ _ (TSess SEnd));
          [apply senv_split_empty_l|repeat constructor| |].
        { apply typed_konst; [auto|]. apply KTClos. }
        eapply (typed_app _ ∅ ∅ _ [None] [Some (TSess Sff)]
                  _ _ (TProd TUnit (TSess Sff)));
          [apply senv_split_empty_l|repeat constructor| |].
        { apply typed_konst; [auto|]. apply (KTSend TUnit SEnd). }
        eapply (typed_pair _ ∅ ∅ _ [None] [Some (TSess Sff)]);
          [apply senv_split_empty_l|repeat constructor| |].
        { apply typed_unit; auto. }
        { apply typed_var, lenv_only_1. }
  - (* sync_body under b : ∗ (idx 1), a : SEnd (idx 0) *)
    eapply (typed_letu _ ∅ ∅ _ [None; Some TUnit] [Some (TSess SEnd); None]);
      [apply senv_split_empty_l|repeat constructor| |].
    + apply typed_var, lenv_only_21.
    + eapply (typed_app _ ∅ ∅ _ [None; None] [Some (TSess SEnd); None]
                _ _ (TSess SEnd));
        [apply senv_split_empty_l|repeat constructor| |].
      * apply typed_konst; [auto|]. apply KTClos.
      * apply typed_var, lenv_only_20.
Qed.

(** Composing the pieces: by the fundamental property and adequacy,
    sync is deadlock free — and by [sync_reduces] it indeed runs to
    graceful termination. *)
Corollary sync_deadlock_free : deadlock_free sync_proc.
Proof. eapply typed_deadlock_free, sync_typed. Qed.

Print Assumptions sync_reduces.
Print Assumptions sync_deadlock_free.
