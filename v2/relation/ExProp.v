(** * The existential property of the step index (stage 2)

    A family of propositions [P x α], down-closed in the level α, that
    has a witness at every level has one witness for every level
    ([exist_prop]). The proof is by contradiction. Every witness x fails
    at some level, a choice of one failing level per witness has an
    upper bound, the limit of that family, and the witness at the limit
    fails below it. Excluded middle and functional choice are explicit
    hypotheses, as for fair runs (lockfree/FairRun.v), and no axiom
    enters. The type of the witnesses must sit in the universe of the
    limits of [Ix], which is checked where the lemma is used. *)

From GV Require Export relation.Ord lockfree.FairRun.

Section exprop.
  Context (EM : excluded_middle) (FC : functional_choice).

  Lemma exist_prop (X : Type) (P : X → Ix → Prop) :
    (∀ x a b, ole a b → P x b → P x a) →
    (∀ a, ∃ x, P x a) → ∃ x, ∀ a, P x a.
  Proof.
    intros Hdown Hall.
    destruct (EM (∃ x, ∀ a, P x a)) as [H|Hno]; [done|exfalso].
    assert (∀ x, ∃ a : Ix, ¬ P x a) as Hfail.
    { intros x. destruct (EM (∃ a : Ix, ¬ P x a)) as [H|H]; [done|].
      exfalso. apply Hno. exists x. intros a.
      destruct (EM (P x a)) as [Hp|Hp]; [done|]. exfalso. apply H. by exists a. }
    destruct (FC X Ix (λ x a, ¬ P x a) Hfail) as [f Hf].
    destruct (Hall (olim f)) as [x Hx].
    apply (Hf x). apply (Hdown x (f x) (olim f)); [apply olt_lim|exact Hx].
  Qed.
End exprop.
