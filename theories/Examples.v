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

(** Composing the pieces: by the fundamental property and adequacy,
    sync is deadlock free — and by [sync_reduces] it indeed runs to
    graceful termination. *)
Corollary sync_deadlock_free : deadlock_free sync_proc.
Proof. eapply typed_deadlock_free, sync_typed. Qed.


(** ** Multiset inversions for two-thread processes *)

Lemma gmultiset_pair_inv (E : gmultiset expr) e x y :
  E ⊎ {[+ e +]} = {[+ x +]} ⊎ {[+ y +]} →
  (e = x ∧ E = {[+ y +]}) ∨ (e = y ∧ E = {[+ x +]}).
Proof.
  intros Heq.
  assert (e ∈ ({[+ x +]} ⊎ {[+ y +]} : gmultiset expr)) as He
    by (rewrite <-Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He];
    apply gmultiset_elem_of_singleton in He; subst;
    [left|right]; (split; [done|multiset_solver]).
Qed.

Lemma gmultiset_pair_inv2 (E : gmultiset expr) e f x y :
  E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ x +]} ⊎ {[+ y +]} →
  E = ∅ ∧ ((e = x ∧ f = y) ∨ (e = y ∧ f = x)).
Proof.
  intros Heq.
  assert (e ∈ ({[+ x +]} ⊎ {[+ y +]} : gmultiset expr)) as He
    by (rewrite <-Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He];
    apply gmultiset_elem_of_singleton in He; subst.
  - assert (E ⊎ {[+ f +]} = {[+ y +]}) as HE by multiset_solver.
    apply gmultiset_singleton_inv in HE as [-> ->]. auto.
  - assert (E ⊎ {[+ f +]} = {[+ x +]}) as HE by multiset_solver.
    apply gmultiset_singleton_inv in HE as [-> ->]. auto.
Qed.

(** The only transition of let ∗ = ∗ in e2 is the β step to e2. *)
Lemma tstep_letu_unit_inv e2 α e' :
  tstep (LetU EUnit e2) α e' → α = LBeta ∧ e' = e2.
Proof.
  intros H. inversion H; subst.
  - match goal with Hh : head_step _ _ _ |- _ => inversion Hh; subst; auto end.
  - exfalso. match goal with Hs : tstep EUnit _ _ |- _ =>
      eapply val_no_tstep in Hs; done end.
Qed.

(** ** Example 2.2 / 3.14: the safe cyclic process

    cycle = ({c,d}, ⟨let ∗ = clos c in clos d, let ∗ = clos c in clos d⟩):
    same thread [tA] twice — the deadlock [blocked] with the second
    thread's channel order agreeing instead of clashing. *)

Definition cycle_proc : proc := ({["c"; "d"]}, {[+ tA +]} ⊎ {[+ tA +]}).

(** The intermediate thread shape after closing c. *)
Notation cycA := (LetU EUnit (App EClos (Chan "d"))).

(** Stage p4 = ({}, ⟨∗, ∗⟩): irreducible and terminated. *)
Lemma cycle_rel4 n : Prel n ∅ TUnit (∅, {[+ EUnit +]} ⊎ {[+ EUnit +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_intro.
  - intros _. exists EUnit, {[+ EUnit +]}. split_and!.
    + done.
    + done.
    + apply Vrel_unit.
    + intros e He. by apply gmultiset_elem_of_singleton in He.
  - intros π p' Hst. exfalso.
    inversion Hst; subst;
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = {[+ _ +]} ⊎ {[+ _ +]},
        Hs : tstep ?e _ _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          eapply val_no_tstep in Hs; done
      end.
Qed.

(** Stage p3 = ({d}, ⟨clos d, clos d⟩): the only step closes d. *)
Lemma cycle_rel3 n :
  Prel n ∅ TUnit
    ({["d"]}, {[+ App EClos (Chan "d") +]} ⊎ {[+ App EClos (Chan "d") +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ App EClos (Chan "d") +]} ⊎ {[+ App EClos (Chan "d") +]})
      with ((∅ ⊎ {[+ App EClos (Chan "d") +]} ⊎ {[+ App EClos (Chan "d") +]})
        : gmultiset expr)
      by multiset_solver.
    eapply PStepClose; [apply TStepHead, HeadClos..|set_solver].
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: subject d is restricted *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta: no β redex *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* msg: no send label *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_clos_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* close: the d-synchronization *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [-> [[-> ->]|[-> ->]]];
          apply tstep_clos_inv in Hse as [Hle ->];
          apply tstep_clos_inv in Hsf as [Hlf ->]
      end; simplify_eq; simpl; intros _.
      all: replace ({["d"]} ∖ {["d"]} : gset chan) with (∅ : gset chan)
        by set_solver.
      all: replace (∅ ⊎ {[+ EUnit +]} ⊎ {[+ EUnit +]})
        with ({[+ EUnit +]} ⊎ {[+ EUnit +]} : gmultiset expr)
        by multiset_solver.
      all: apply cycle_rel4.
Qed.

(** Stage p2 = ({d}, ⟨clos d, let ∗ = ∗ in clos d⟩): only the β step. *)
Lemma cycle_rel2 n :
  Prel n ∅ TUnit ({["d"]}, {[+ App EClos (Chan "d") +]} ⊎ {[+ cycA +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta.
    apply TStepHead, HeadLetU.
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> ->]|[-> ->]];
          [apply tstep_clos_inv in Hs as [Hα _]; simplify_eq
          |apply tstep_letu_unit_inv in Hs as [_ ->]]
      end.
      intros _. apply cycle_rel3.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* msg *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          [apply tstep_clos_inv in Hs as [Hα _]
          |apply tstep_letu_unit_inv in Hs as [Hα _]]
      end; simplify_eq.
    + (* close: partner thread has no close label *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> ->]|[-> ->]]];
          [apply tstep_letu_unit_inv in Hsf as [Hα _]
          |apply tstep_letu_unit_inv in Hse as [Hα _]]
      end; simplify_eq.
Qed.

(** Stage p1 = ({d}, ⟨let ∗ = ∗ in clos d, let ∗ = ∗ in clos d⟩). *)
Lemma cycle_rel1 n :
  Prel n ∅ TUnit ({["d"]}, {[+ cycA +]} ⊎ {[+ cycA +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|].
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    eapply (Hirr PTau). eapply PStepBeta.
    apply TStepHead, HeadLetU.
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* beta *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> ->]|[-> ->]];
          apply tstep_letu_unit_inv in Hs as [_ ->]
      end.
      all: intros _.
      all: replace ({[+ cycA +]} ⊎ {[+ App EClos (Chan "d") +]})
        with ({[+ App EClos (Chan "d") +]} ⊎ {[+ cycA +]} : gmultiset expr)
        by multiset_solver.
      all: apply cycle_rel2.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* msg *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_letu_unit_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* close *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_letu_unit_inv in Hse as [Hα _]
      end; simplify_eq.
Qed.

(** Stage p0 = cycle: the only step closes c. *)
Lemma cycle_rel0 n : Prel n ∅ TUnit cycle_proc.
Proof.
  destruct n as [|n]; [apply Prel_0|].
  unfold cycle_proc.
  apply Prel_S_intro.
  - intros Hirr. exfalso.
    eapply (Hirr PTau).
    replace ({[+ tA +]} ⊎ {[+ tA +]})
      with ((∅ ⊎ {[+ tA +]} ⊎ {[+ tA +]}) : gmultiset expr) by multiset_solver.
    eapply PStepClose;
      [apply TStepLetU, TStepHead, HeadClos..|set_solver].
  - intros π p' Hst.
    inversion Hst; subst.
    + (* session: subject c is restricted *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LSess _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq; simpl in *; set_solver.
    + (* beta *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e LBeta _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* fork *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} = _, Hs : tstep ?e (LFork _ _) _ |- _ =>
          apply gmultiset_pair_inv in Heq as [[-> _]|[-> _]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* msg *)
      exfalso.
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ _ +]} = _,
        Hs : tstep ?e (LSess (SSend _ _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [_ [[-> _]|[-> _]]];
          apply tstep_blocked_inv in Hs as [Hα _]
      end; simplify_eq.
    + (* close: the c-synchronization *)
      match goal with
      | Heq : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _,
        Hse : tstep ?e (LSess (SClos _)) _,
        Hsf : tstep ?f (LSess (SClos _)) _ |- _ =>
          apply gmultiset_pair_inv2 in Heq as [-> [[-> ->]|[-> ->]]];
          apply tstep_blocked_inv in Hse as [Hle ->];
          apply tstep_blocked_inv in Hsf as [Hlf ->]
      end; simplify_eq; simpl; intros _.
      all: replace ({["c"; "d"]} ∖ {["c"]} : gset chan)
        with ({["d"]} : gset chan) by set_solver.
      all: replace (∅ ⊎ {[+ cycA +]} ⊎ {[+ cycA +]})
        with ({[+ cycA +]} ⊎ {[+ cycA +]} : gmultiset expr)
        by multiset_solver.
      all: apply cycle_rel1.
Qed.

(** Example 3.14: cycle satisfies the semantic judgment directly —
    exhibiting an inhabitant of the process relation without going
    through the fundamental theorem — and is hence deadlock free
    despite being untypable (Example 2.11). *)
Example cycle_sem_ptyped : sem_ptyped ∅ cycle_proc TUnit.
Proof. intro n. apply cycle_rel0. Qed.

Corollary cycle_deadlock_free : deadlock_free cycle_proc.
Proof. eapply adequacy, cycle_sem_ptyped. Qed.

(** The composition of sync (typable, hence semantically typed by the
    fundamental theorem) and cycle (semantically typed directly), via
    P-Independent (Theorem 3.12), is deadlock free. *)
Corollary sync_cycle_deadlock_free :
  deadlock_free ({["c"; "d"]}, {[+ sync_main +]} ⊎ ({[+ tA +]} ⊎ {[+ tA +]})).
Proof.
  eapply adequacy.
  replace ({["c"; "d"]} : gset chan)
    with (∅ ∪ {["c"; "d"]} : gset chan) by set_solver.
  apply (sem_ptyped_independent ∅ ∅ ∅ ∅ {[+ sync_main +]}
           {["c"; "d"]} ({[+ tA +]} ⊎ {[+ tA +]}) TUnit);
    [constructor|apply senv_split_empty_l|set_solver..
    |exact (fundamental_proc _ _ _ sync_typed)
    |exact cycle_sem_ptyped].
Qed.

(** ** Negative check: blocked is not in the logical relation

    (at any environment and type, at any positive index): it is
    irreducible but holds restricted channels, so the termination
    clause of the process relation rejects it. *)
Lemma blocked_not_Prel Σ T n : ¬ Prel (S n) Σ T blocked.
Proof.
  intros HP.
  destruct (Prel_S_irred _ _ _ _ HP blocked_pirred) as (v & E & Heq & _).
  unfold blocked in Heq.
  assert ({["c"; "d"]} = (∅ : gset chan)) as Hcd
    by exact (f_equal fst Heq).
  set_solver.
Qed.

Corollary blocked_not_sem_ptyped Σ T : ¬ sem_ptyped Σ blocked T.
Proof. intros H. exact (blocked_not_Prel Σ T 0 (H 1)). Qed.

Print Assumptions adequacy.
Print Assumptions sync_reduces.
Print Assumptions sync_deadlock_free.
Print Assumptions cycle_deadlock_free.
Print Assumptions sync_cycle_deadlock_free.
