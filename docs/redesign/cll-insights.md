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
   own extension of W. Refuted (fx-branch, v2/examples/BranchExt.v,
   `bx_not_E`, `bx_rejected`). E holds at every extension W1 ⊒ W, and a W1 can
   already hold the opposite of an arm's fact between old points, so the
   fundamental theorem fails for such a rule at N = None, for every join
   restriction. Kripke monotonicity is the obstruction.

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

## Exchange, 2026-11-23

- Exponentials. CLL≺ adopts the shared formulation. Promotion only over
  ?-handles that hold no addresses, contraction and weakening free, a body
  schema instantiated at each use. This is our E-Box (`lenv_unl Δ`, the box
  clause asks Θ = ∅ and `fends e = ∅`) and E-Force (`hold_at W Γ C xs` at the
  caller). Our rules stay as they are.
- Tickets. CLL≺ takes tickets as the decidable sufficient check for liveness.
  Our incompleteness, derived from the rules and not mechanized, is that an
  end can be handed off at most N times before it is acted on (E-Send ages
  the payload by 1, credit a ≤ m ≤ N). So a lock-free program that delegates
  an end k times for a k received at run time types at no fixed N.
- Composition. CLL≺ adopts our proof route to drop its freshness hypothesis
  D102. Renaming apart happens in the proof (`ptyped_qren`, `qren_side`,
  `connect_hidden`), the summary property must be equivariant and monotone.
- Decidability, checked independently on the CLL≺ side (D112). Liveness of
  regular CLL≺ derivations with finite traces is undecidable and
  Π⁰₂-complete, for derivations without links or exponentials. Theorem A
  reduces two-counter machines to regular derivations that are correct iff
  the machine halts. Theorem B gets hardness from totality with a guessed
  input and the upper bound from König's lemma over consistent walks. The
  proof is in cll-order/paper/main.tex, Def 14.12, Lemmas 14.13 and 14.14,
  Thms 14.15 and 14.16, Remark 14.17. The check closed four gaps of the first
  sketch (round numbers end the downward regress, a permanence argument for
  wrong choices, a missing case, a fixed maximal-parallel schedule in place
  of fairness). CLL≺ contrasts this with validity of bouncing threads, which
  is Σ⁰₁-complete (Baelde et al.). The fragment without ⊕ and & is open. For our language, lock
  freedom of programs is undecidable already by Rice's theorem, because boxes
  give general recursion. The CLL≺ result is about a restricted class of
  regular derivations.
  The same holds inside DF typing. DF typing admits pure divergence and
  general recursion over sums, so a thread can run a two-counter machine and
  then act on an end whose partner waits. That program is lock-free iff the
  machine halts.

## Shared design proposal, 2026-11-23

CLL≺ proposed two levels for both projects: a global qualitative semantics
(acyclic slices for deadlock freedom, well-founded slices and finite traces
for lock freedom) and a local decidable static fragment (boxes with schemas,
generated facts, one world extension per & branch, tickets, summaries checked
at composition). Our reply, not decided by the author:

- Three levels, not two. Operational statement, then the relation (semantic,
  undecidable, compositional by `lf_p_connect`), then the typing. The relation
  is where lock freedom stops being global.
- Generate facts locally, check the schema at the force and the joined world
  at the connect.
- Per-branch extensions at E-Case and the offer rules need a join
  restriction. The conclusion stays at W and branch facts may only concern
  points whose use ends in the branch. Tickets are unaffected. Refuted later the same day, see item 2 above. No join
  restriction makes the rule sound, and the restriction to points created in
  the arm adds nothing to E-New and E-Open.
- For lock freedom, ranks fixed at creation forbid opposite orders on older
  points. The way out is transfinite indices (check-transfinite.md), with
  excluded middle and dependent choice. Proposed order of work: per-branch
  extensions for deadlock freedom first.
- Static typing is not decidable yet. The algorithmic plan makes it decidable
  relative to the constraint theory and an equivalence oracle.

## Three claims of CLL≺ checked, 2026-11-23

- Force as generation (E-Force adds C[xs] to a summary, P-Connect checks).
  Sound for deadlock freedom as annotation inference, unsound for lock
  freedom. Points xs created at run time never reach a composition, and the
  force check (`hold_at`, `wholds W' C xs` in the box clause) is what rejects
  the pipeline.
- The local form of CLL≺'s condition (E) is the box, not E-New. Proposition 7
  of check-general-new.md (argued): a box cannot force itself at an instance
  that descends in its schema. rx-chain falls under it for every sound E-New.
  The descent n times, which is lock-free, falls under it too.
- P-Connect and CLL≺'s Lemma 5.6 coincide for finite worlds and one slice.
