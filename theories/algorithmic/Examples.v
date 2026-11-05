(** * The checker on examples

    sync and cycle of examples/, written as annotated terms, run through
    [synth] by computation. The constraint it returns is discharged by
    hand in the context of the program's creation constraints, and
    [synth_deadlock_free] gives deadlock freedom of the erased program,
    which is the term of Sync.v and Cycle.v. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export algorithmic.Soundness examples.Sync examples.Cycle.

Set Default Proof Using "All".

(** A creation constraint without facts. *)
Definition nofacts : bcs := BCs [] (λ _, False).

Lemma cc_ok_nofacts peq plt : cc_ok peq plt nofacts.
Proof.
  apply (cc_ok_inner peq plt (λ _, False) pofs).
  - intros x y z. apply pofs_trans.
  - apply pofs_irrefl.
  - intros x _. apply pofs_shift.
  - intros g [].
  - intros x _. unfold pofs, pt_shift. simpl. split; [done|lia].
Qed.

Lemma c0_nofacts : creation_ok 0 nofact nofact (λ _, False) nofacts.
Proof.
  apply c0_acyclic_creation, (c0_acyclic_rank 0 _ pt_off);
    [intros x; cbn; lia|by intros ? ? []|by intros ? ? []|done].
Qed.

(** ** sync

    The thunk is annotated with its upper point ι+1 and its lower point
    ι. The channel c is at index 1 of the body and d at index 0, as in
    [let_new]. *)
Definition sync_a : aexpr :=
  ALetNew Ssync nofacts
    (ALetU (AApp (AKonst KSpawn)
              (ALam (Some (pv 0 1)) (Some (pt_dual (pv 0 0))) TUnit
                 (ALetU (AVar 0) (AApp (AKonst KClos) (AApp (AKonst KSend) (APair AUnit (AVar 2)))))))
       (ALetP (AApp (AKonst KRecv) (AVar 0)) (ALetU (AVar 1) (AApp (AKonst KClos) (AVar 0))))).

Lemma sync_a_erase : erase sync_a = sync_main.
Proof. reflexivity. Qed.

(** The checker accepts sync at type ∗, by computation. *)
Lemma sync_a_type : (fst <$> synth 0 ∅ [] (∅, None) sync_a) = Some TUnit.
Proof. vm_compute. reflexivity. Qed.

Lemma sync_a_deadlock_free : deadlock_free (∅, {[+ sync_main +]}).
Proof.
  rewrite <-sync_a_erase.
  eapply (synth_deadlock_free 0 nofacts sync_a TUnit); [exact c0_nofacts|constructor|cbn; reflexivity|].
  cbn. rewrite fhyps_pinst_empty, !lookup_insert_eq. cbn.
  split_and!; try done.
  all: try apply cc_ok_nofacts.
  all: try (intros y Hy; mem_cases Hy; left; apply he_refl).
  all: try (intros y Hy; mem_cases Hy).
  all: try (right; apply hlt_po).
  all: try (left; apply he_refl).
Qed.

(** ** cycle

    Two channels. The second is created under the constraint γ̂ ≺ ε̂,
    the four facts between the ends of γ and of ε (end points: the
    thread closes γ̄ while it holds ε̄ and needs γ̄ ≺ ε, the main thread
    closes γ while it holds ε and needs γ ≺ ε̄). *)
Definition hat_lo (x : point) : bcs :=
  BCs [x] (λ g, ∃ b c, g = FLt (pt_polar b (pvar 1)) (pt_polar c (pvar 0))).

Definition cycle_a : aexpr :=
  ALetNew SEnd nofacts
    (ALetNew SEnd (hat_lo (pvar 0))
       (ALetU (AApp (AKonst KSpawn)
                 (ALam (Some (pt_dual (pvar 0))) (Some (pvar 1)) TUnit
                    (ALetU (AVar 0) (ALetU (AApp (AKonst KClos) (AVar 5)) (AApp (AKonst KClos) (AVar 1))))))
          (ALetU (AApp (AKonst KClos) (AVar 5)) (AApp (AKonst KClos) (AVar 1))))).

Lemma cycle_a_erase : erase cycle_a = cycle_main.
Proof. reflexivity. Qed.

Lemma cycle_a_type : (fst <$> synth 0 ∅ [] (∅, None) cycle_a) = Some TUnit.
Proof. vm_compute. reflexivity. Qed.

(** The creation constraint γ̂ ≺ ε̂ of the second channel is a creation
    constraint over any context that knows γ: every fact enters ε̂ from
    outside, and no fact leaves it. *)
Lemma cc_ok_hat_lo peq plt x : cc_ok peq plt (hat_lo x).
Proof.
  assert (fresh_lt (hat_lo x)) as Hlt.
  { intros f (b & c & ->) Hs. left. eexists _, _. split; [done|].
    split_and!; [by exists b, c|done|by destruct c|by destruct b]. }
  apply cc_ok_fresh; [by left|]. apply fresh_between_lt; [done|].
  intros u p q v _ (Hf & _ & Hq & Hv) _. destruct Hf as (b & c & E). injection E as -> ->.
  by destruct b.
Qed.

Lemma set_map_empty_pt (f : point → point) : set_map (C:=gset point) (D:=gset point) f ∅ = ∅.
Proof. apply set_eq. intros x. rewrite elem_of_map. split; [intros (y & _ & Hy); set_solver|set_solver]. Qed.

Lemma cycle_a_deadlock_free : deadlock_free (∅, {[+ cycle_main +]}).
Proof.
  rewrite <-cycle_a_erase.
  eapply (synth_deadlock_free 0 nofacts cycle_a TUnit); [exact c0_nofacts|constructor|cbn; reflexivity|].
  cbn. rewrite fhyps_pinst_empty, !lookup_insert_eq, !set_map_empty_pt. cbn.
  set (Ψ := [(bcs_inst (pshift 1) (bcs_inst (pshift 1) nofacts), []);
             (bcs_inst (pshift 1) (bcs_inst (pshift 1) nofacts), [pt_inst (pshift 1) (pvar 0)]);
             (bcs_inst (pshift 1) (hat_lo (pvar 0)), [pvar 0])]).
  assert (∀ b c, hlt Ψ (pt_polar b (pt_inst (pshift 1) (pvar 0))) (pt_polar c (pvar 0))) as Hγε.
  { intros b c. apply (hl_h Ψ ∅). exists (bcs_inst (pshift 1) (hat_lo (pvar 0))), [pvar 0].
    split; [by right; right; left|].
    eexists. split.
    - exists (FLt (pt_polar b (pvar 1)) (pt_polar c (pvar 0))).
      split_and!; [by exists b, c|destruct b, c; cbn; split; lia|reflexivity].
    - destruct b, c; reflexivity. }
  pose proof (Hγε false false) as H1. pose proof (Hγε false true) as H2.
  pose proof (Hγε true false) as H3. pose proof (Hγε true true) as H4. cbn [pt_polar] in *.
  split_and!; try done.
  all: try apply cc_ok_nofacts.
  all: try apply cc_ok_hat_lo.
  all: try (eexists _, _, _; split_and!; [by right; left|by left|done]).
  all: try (intros y Hy; mem_cases Hy; rewrite ?pt_dual_dual; first [left; apply he_refl|done]).
  all: try (left; apply he_refl).
  all: try (right; done).
  all: try (intros y Hy; mem_cases Hy; rewrite ?pt_dual_dual;
            first [right; exact H4|left; exact (he_refl _ (pvar 1))]).
  all: try done.
Qed.
