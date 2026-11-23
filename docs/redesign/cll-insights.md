# Insights from CLL≺, 2026-11-23

The author asked that what the CLL≺ project learns carries over to the
logical relation, and that fixes move both ways. CLL≺ is the Lean project at
~/proglang/research/lean/cll-order. Its sources for the points below are
cll-order/paper/main.tex and cll-order/.claude/notes (decisions.md,
counterexamples.md, ranking.md, report-2026-11-23.md). The D, O and Prop
numbers refer to those files. This file records the message of the CLL≺
session. No code changed for it.

## What CLL≺ reports

1. Generated facts. Each blocking rule generates its fact α ≺ β^⊥ (our
   u ≺ v̄), and composition checks acyclicity of the interface summaries
   (Thm 5.4). We answered that this fits the existential shape of
   `ptyped_sem` (static/Hiding.v). Boxes are the limit. A box is typed once
   and forced many times, so its generated facts become a constraint schema in
   its type and each force checks it.

2. A world per branch for conservativity. With one order for both branches,
   the CP process of their Example 4.8, whose branches need opposite orders,
   is rejected. PCP rejects it for the same reason. Checking only coherent
   pairs of branches is unsound (counterexamples.md). Request for the
   deadlock-free relation: test a branch rule that types each branch at its
   own extension of W. `wext` on strict worlds only preserves old facts, so
   the Kripke structure allows this. The fundamental theorem for such a rule is
   not checked.

3. Safety and liveness split (D74). Safe means no cycle in any slice. It gives
   subject reduction, progress, deadlock freedom and the diamond property, and
   it is a summary check at each composition. Live means well-founded plus
   finite traces. It is needed for lock freedom and has no finite local
   judgement (Prop 5.9, Cor 5.10). The proof is a pipeline whose finite
   truncations are correct while the infinite one is stuck. This is the
   Alpern–Schneider split and a candidate explanation of why our lock-free
   relation needs ranked worlds.

4. Ranks need only exist, per slice (ranking.md). Admissibility with finite
   traces holds iff a ranking into ℕ exists. CLL≺ never fixes ranks at
   creation. Our ranked worlds fix them at E-New (`wk_ext`, `w_rk_ord`), which
   rules out opposite orders across branches for lock freedom. Open question
   for us: can ranks be existential per branch?

5. Tickets as a qualitative condition (D57, D58). A trace follows an end as
   it passes from thread to thread until a thread acts on it. Liveness asks
   every trace to be finite. Grades remain only as a witness, like the ordinal
   fuel of Lantana. Possible simplification of our tickets.

6. The forwarder. A link at α, β generates αw ≺ (βw)^⊥ and βw ≺ (αw)^⊥ for
   every word w. Eager AxCut breaks subject reduction unless restrictions may
   move under prefixes and into case branches, the conversions (Guard) and
   (Case) used as an equivalence (D78, D79). Link and copycat differ inside
   cycles. The copycat is a one-place buffer, so a network can be correct with
   the copycat and deadlock with the link (D70, O19). Relevant to our link and
   to the fused link at dual points.

7. Reuse is the common obstacle. Primitive exponentials fail in CLL≺ because a
   requested copy needs addresses below one the server already holds (O21).
   Our box reuse forces constraint schemas. Shared idea to try: each copy or
   force gets fresh base addresses generated at the request, as CLL≺ does for
   cut ends, in place of sub-addresses.

8. Decidability of liveness for recursive programs is open in CLL≺ (O16).
   Finite traces are decidable in linear time. Infinite descending chains with
   unbounded addresses are the hard part, close to bouncing threads, whose
   validity is undecidable. CLL≺ runs an investigation on it.

## To test here

- Item 2, a branch rule at separate extensions of W, deadlock-free relation
  first.
- Item 4, existential ranks per branch for the lock-free relation.
- Item 7, fresh base points per force.
- Item 5, whether tickets reduce to finite traces with grades as witness.
