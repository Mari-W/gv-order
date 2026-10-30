# C. Data-dependent constraints

Goal. Facts about the order of points that depend on values a program computes
or on choices it makes at run time.

## Where the problem appears

1. Branches. A component that picks the order of two external actions at run
   time needs both orders. One world per component cannot hold both, so the
   composition is deadlock free but not derivable (sharp edges 4, deferred).
2. Rounds. A recursion orders the points of round k by a formula in k. Free
   constraints state these facts as infinite sets (sharp edges 65), with the
   round counter bound in set-builder notation.
3. Segments. A context-free protocol ends a segment after a number of actions
   that depends on the value sent (direction B).
4. Depth. A recursion on a received channel moves to ι.1 each round. The facts
   are indexed by the depth n, as in {ι.1ⁿ + 1 ≺ ι.1ⁿ⁺¹ ∣ n ∈ ℕ}.

Rounds and depth are solved by infinite constraints. Branches and segments are
open, and both need facts that refer to a value known only at run time.

## Directions

1. Offsets as terms. Let a point offset be an expression over data, ι + len(t)
   for a tree t, with existential offsets ∃n where the type does not name the
   data. Facts quantify over the offsets they mention. This covers segments.
2. Worlds indexed by choices. A world that grows at an internal choice with facts
   between existing points, provided the partner is ready in every branch. The
   receiving side learns the facts with the label. This covers branches. It
   breaks the assumption that only new extends a world conservatively (⊑ₒ), and
   P-Connect has to amalgamate a world per branch.
3. Label-dependent session types. Thiemann and Vasconcelos (2020) make session
   types depend on labels and naturals, with primitive recursion at the type
   level. Their system does not guarantee deadlock freedom. Facts that depend on
   the same labels would combine both.

## Open questions

- Whether direction 2 keeps the relation monotone. A fact added in one branch
  must never contradict a fact the other side already relies on.
- Whether offsets as terms keep the static fact theory first order.
- Which examples need it beyond the scheduler variant with a run-time order and
  tree serialization.
