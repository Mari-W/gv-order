(** * Examples from the paper (§2)

    - [sync] (Example 2.1): the closed process that forks a partner,
      exchanges ∗ over a fresh channel and gracefully terminates.
    - [blocked] (Example 2.8): the classic two-thread deadlock, shown
      to be irreducible and unsafe. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import LogRel Compositionality.

Local Open Scope string_scope.

(** ** Example 2.1: sync *)

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
      apply TStepHead. by apply HeadRecv.
    - set_solver. }
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

Definition tA : expr := LetU (App EClos (Chan "c")) (App EClos (Chan "d")).
Definition tB : expr := LetU (App EClos (Chan "d")) (App EClos (Chan "c")).
Definition blocked : proc := ({["c"; "d"]}, {[+ tA +]} ⊎ {[+ tB +]}).

(** The only transition of clos applied to a channel is the close
    action on that channel. *)
Lemma tstep_clos_inv ch α e' :
  tstep (App EClos (Chan ch)) α e' → α = LSess (SClos ch) ∧ e' = EUnit.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep (Konst _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
  - exfalso. match goal with Hs : tstep (Chan _) _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
Qed.

(** The only transition of let ∗ = clos ch1 in clos ch2 is closing ch1. *)
Lemma tstep_blocked_inv ch1 ch2 α e' :
  tstep (LetU (App EClos (Chan ch1)) (App EClos (Chan ch2))) α e' →
  α = LSess (SClos ch1) ∧ e' = LetU EUnit (App EClos (Chan ch2)).
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh end.
  - match goal with Hs : tstep (App _ _) _ _ |- _ =>
      apply tstep_clos_inv in Hs as [-> ->]; auto end.
Qed.

Lemma blocked_pirred : pirred blocked.
Proof.
  intros π p' Hstep. inversion Hstep; subst.
  - (* session *)
    match goal with Hs : tstep ?e (LSess _) _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ (LSess _) _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq; set_solver.
  - (* beta *)
    match goal with Hs : tstep ?e LBeta _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ LBeta _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq.
  - (* fork *)
    match goal with Hs : tstep ?e (LFork _ _) _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ (LFork _ _) _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq.
  - (* msg *)
    match goal with Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
      assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} : gmultiset expr)) as Hin
        by multiset_solver end.
    apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin];
      apply gmultiset_elem_of_singleton in Hin; subst;
      match goal with Hs : tstep _ (LSess (SSend _ _)) _ |- _ =>
        apply tstep_blocked_inv in Hs as [Heq _] end;
      simplify_eq.
  - (* close *)
    match goal with
      Heq : ?E0 ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _ |- _ =>
      assert (e ∈ E0 ⊎ {[+ e +]} ⊎ {[+ f +]}) as HinE by multiset_solver;
      assert (f ∈ E0 ⊎ {[+ e +]} ⊎ {[+ f +]}) as HinF by multiset_solver;
      rewrite Heq in HinE; rewrite Heq in HinF
    end.
    apply gmultiset_elem_of_disj_union in HinE as [HinE|HinE];
      apply gmultiset_elem_of_singleton in HinE;
      apply gmultiset_elem_of_disj_union in HinF as [HinF|HinF];
      apply gmultiset_elem_of_singleton in HinF; subst;
      repeat match goal with
        Hs : tstep _ (LSess (SClos _)) _ |- _ =>
          apply tstep_blocked_inv in Hs as [? ?] end;
      simplify_eq;
      (* the two threads picked the same term: multiset count is off *)
      multiset_solver.
Qed.

Example blocked_not_safe : ¬ safe blocked.
Proof.
  intros [Hterm|[p' Hstep]].
  - destruct Hterm as (v & E & Heq & _).
    unfold blocked in Heq.
    assert ({["c"; "d"]} = (∅ : gset chan)) as Hc by congruence.
    set_solver.
  - exact (blocked_pirred _ _ Hstep).
Qed.

Example blocked_not_deadlock_free : ¬ deadlock_free blocked.
Proof.
  intros Hdf. apply blocked_not_safe, Hdf, rtc_refl.
Qed.

(** ** Example 2.11: sync is syntactically typable, hence deadlock free *)

Lemma lenv_empty_nil : lenv_empty [].
Proof. intros o Ho. by apply elem_of_nil in Ho. Qed.

Lemma lenv_empty_cons Δ : lenv_empty Δ → lenv_empty (None :: Δ).
Proof.
  intros HΔ o Ho. apply elem_of_cons in Ho as [->|Ho]; auto.
Qed.

Local Hint Resolve lenv_empty_nil lenv_empty_cons : core.

Lemma lenv_only_1 T : lenv_only [Some T] 0 T.
Proof.
  split; [done|]. intros [|y] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_20 T : lenv_only [Some T; None] 0 T.
Proof.
  split; [done|]. intros [|[|y]] T' H; simplify_eq/=; auto.
Qed.

Lemma lenv_only_21 T : lenv_only [None; Some T] 1 T.
Proof.
  split; [done|]. intros [|[|y]] T' H; simplify_eq/=; auto.
Qed.

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

(** Composing the pieces: by the fundamental property and adequacy
    (modulo the admitted compositionality lemmas), sync is deadlock
    free — and by [sync_reduces] it indeed runs to graceful
    termination. *)
Corollary sync_deadlock_free : deadlock_free sync_proc.
Proof. eapply typed_deadlock_free, sync_typed. Qed.

Print Assumptions adequacy.
Print Assumptions sync_reduces.
Print Assumptions sync_deadlock_free.
