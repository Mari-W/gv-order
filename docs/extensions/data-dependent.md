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

## Session choice needs names, not data (2026-10-31)

Done as K10 of context-free.md (SHARP-EDGES 76). Branch roots are in the
mechanization on branch cfst, every cfst example is ported to ceilings over
walks, and T1, T2 and T3 below type and are deadlock free in
theories/examples/cfst/BranchOrder.v. The rest of this section is the design
as written before the work.

Program T2 of mordido-perez.md §9.5 types in Mordido and Pérez and fails under
K5.

```
c : ⊕{A: !∗;Close, B: !∗;Close}      d : Close
T1 = select A c; send ∗ c; close c
T2 = branch c { A ⇒ close d; recv c; close c  |  B ⇒ recv c; close d; close c }
T3 = close d
```

K5 puts both continuations of a choice at ι+1. Branch A blocks on d while it
holds c at ι+1, so it needs (d,0) ≺ ι+1. Branch B needs ι+1 ≺ (d,0). E-Case
types both branches in one world, so the world has a cycle. The program is
regular, so the problem belongs to choice and not to context-free types.

Branch roots remove it. A new root x◁i names "the point of c after branch i
was picked at x", as a carried root x.i names a message position. selectᵢ and
branch move the entry from x to x◁i instead of x+1. The world laws gain
congruence x ≡ y ⇒ x◁i ≡ y◁i and program order x ≺ x◁i. T2 then needs
(d,0) ≺ ι◁A in branch A and ι◁B ≺ (d,0) ≺ ι◁B+1 in branch B. The world
ι ≺ ι◁B ≺ (d,0) ≺ ι◁A is strict. Every fact stays positive and static. Only
the name of the point records the branch, so no fact depends on a value. The
depth facts {ι.1ⁿ + 1 ≺ ι.1ⁿ⁺¹} above are the precedent. Carried roots already
turned a run-time depth into infinitely many named points.

What this covers.
- Subsumption of priority systems with session choice. A priority system gives
  each branch of a choice its own priorities, and branch roots give each branch
  its own points. The translation of Mordido and Pérez then maps a priority to
  the rank of a point per branch, and T2 types (checked by hand above).
- Branch-dependent instant counts. n-ary choice by nesting, and branches of
  different lengths before a common continuation, get distinct points per path
  instead of one shared instant.

What stays open.
- Branches on values (problem 1, sharp edges 4, C2). A case on a received bit
  does not move any channel, so no root records the branch. Priority systems
  cannot type such programs either. A priority belongs to a type, and both arms
  of a value case see the same types. Mordido and Pérez have no sums at all. So
  this part concerns only the comparison with GV♯, and needs direction 2.
- Segments (problem 3). With branch roots the point after sendTree names the
  tree as a path of roots, and the world of a closed program states
  sendTree t c ; close d ; send v c with static facts. The box type then has to
  say that its result is one of the end points of the paths through TreeC from
  ι, a membership in an infinite set of points, and the left and right recursive
  calls need different bounds. A sketch with path variables (ι′ ≡ ι·w with w
  ranging over the paths of a type) is open. Mordido and Pérez give an
  unbounded segment latent effect ⊤ (p. 21), the analogue of our coarse
  ceiling, so subsumption does not need it.

Cost. Branch roots revise K4 and K5 on branch cfst. They touch the point
syntax and world laws (as carried roots did, sharp edges 37 onwards), O-Select,
O-Branch, Q-Select, Q-Branch, the stage B lemmas that move an entry by a choice,
and the constraints of the examples with choice, whose ceilings become sets
over paths. In the event (sharp edges 76) Stream.v and CfstScheduler.v make no
choice and kept their constraints.

## Open questions

- Whether direction 2 keeps the relation monotone. A fact added in one branch
  must never contradict a fact the other side already relies on.
- Whether offsets as terms keep the static fact theory first order.
- Which examples need it beyond the scheduler variant with a run-time order and
  tree serialization.

Since K11 (2026-11-04) the continuation of branch i at x is x[i], and
select and branch owe x ≺ x[i]. T2 still types (theories/examples/cfst/
BranchOrder.v), with c created under {ι ≺ ι[0], ι ≺ ι[1], ι[1] ≺ ι[0]}.
