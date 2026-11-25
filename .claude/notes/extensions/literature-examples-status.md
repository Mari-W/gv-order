# Literature examples, status 2026-11-04

Every literature program that the docs claim the core types now has a Rocq
theorem, with three exceptions from the Mordido–Pérez gap list. Every
literature program that the docs claim the core rejects and that deadlocks now
has an underivability theorem. Seven programs gain their theorems on branch
`claude/lit-examples-cf15nz`, in theories/examples/lit/. This file collects the
verdicts of literature-examples.md, context-free.md, choice-encoding.md and
the three adequacy notes. It does not replace them.

The scope is the programs a paper prints and the programs the docs build from
a paper's counterexamples. Programs marked "ours" in the older files, such as
the bad `link` or `ordered` without its constraint, stay where they are.

Two routes count as typed. "core" means a whole-program `styped` derivation of
static/Source.v (or `typed` at `Wpo []`, which `typed_styped` reads back) and
deadlock freedom through `soundness_source` or `soundness`. "translation" means
the program is typed in the paper's repaired system and a translation of
theories/pgv, theories/pn or theories/mp yields the derivation. The new files
use `soundness_source` with C₀ = ∅ (`soundness_source_nil`, examples/lit/LitLib.v).

## Claimed typable

| Program | Source | Route | Rocq theorem |
|---|---|---|---|
| Milner's cyclic scheduler, k = 3 with collectors | Dardha and Gay, Example 1 | core | `ms_typed`, `ms_deadlock_free` (examples/MilnerSched.v) |
| recursive forwarder server | Kobayashi, Example 2 | core | `fwsrv_typed`, `fw_typed`, `fw_deadlock_free_kob` (examples/KobForwarder.v) |
| factorial server | Kobayashi p. 2, Padovani (3) | core | `fcsrv_typed`, `fc_typed`, `fc_deadlock_free` (examples/FactServer.v) |
| `stream` with a consumer | Padovani (4) | core | `stprod_typed`, `stcons_typed`, `st_typed`, `st_deadlock_free` (examples/Stream.v) |
| Example 2.1 | PGV p. 4 | translation | `ex21_typed`, `pgv_ex21_deadlock_free` (pgv/PGVExamples.v) |
| `fall2`, the falling session S1 = !⁵1.?⁰1.end⁶? | PGV §2 as read in pgv-adequacy.md §2 | core | `fall2_styped`, `fall2_deadlock_free` (examples/lit/Falling.v), new |
| `fallxy` | pgv-adequacy.md §8.1, after PGV | core | `fallxy_styped`, `fallxy_deadlock_free` (examples/lit/Falling.v), new |
| fibo | Padovani and Novara, Example 1 | translation | `fibo_deadlock_free` (pn/PNExamples.v), `fibo_deadlock_free_src` (pn/PNSimulation.v) |
| signal pipe | Padovani and Novara, Example 2 with the types of Example 4 | translation | `pipe_deadlock_free`, `pipe_deadlock_free_src` |
| div and divsend | Padovani and Novara p. 14 | translation | `div_deadlock_free_src`, `divsend_deadlock_free_src` |
| recvTree as drain, and copy | Thiemann and Vasconcelos pp. 2–3 | core | `tree_typed`, `tree_deadlock_free` (examples/cfst/TreeCopy.v) |
| treeSum serving transform | Thiemann and Vasconcelos, Listing 2 | core | `ts_typed`, `ts_deadlock_free` (examples/cfst/TreeSum.v) |
| arithmetic server | Thiemann and Vasconcelos, Listing 3 | core | `as_typed`, `as_deadlock_free` (examples/cfst/ArithServer.v) |
| two streams in a cycle | Mordido and Pérez, Listings 1.1 and 1.2 | core and translation | `st_typed`, `st_deadlock_free` (examples/cfst/Stream.v), `st_mp_deadlock_free`, `st_deadlock_free_src` |
| repair of the classic deadlock | Mordido and Pérez p. 3 | core and translation | `dlfix_typed`, `dlfix_deadlock_free` (examples/cfst/CfstDeadlock.v) |
| Milner's scheduler | Mordido and Pérez A.5 | core | `sch_typed`, `sch_deadlock_free` (examples/cfst/CfstScheduler.v) |
| receiveTree against a sender of Node(Leaf, Leaf) | Mordido and Pérez pp. 5, 21 | translation | `rt_deadlock_free_src`, `rt_deadlock_free_src3` |
| T1 ∥ T2 ∥ T3, branches that order d differently | mordido-perez.md §9.5, in their system | core and translation | `bo_typed`, `bo_deadlock_free` (examples/cfst/BranchOrder.v), `choice_typed`, `choice_deadlock_free` (examples/ChoiceEnc.v), `t2_deadlock_free_src` |
| a channel ordered against the returned channel both ways | mordido-perez.md §15.3 | core | `si_typed`, `si_deadlock_free` (examples/cfst/SegmentInterleave.v) |
| a channel created after a call, sent on the returned channel | mordido-perez.md gap list | core | `sd_typed`, `sd_deadlock_free` (examples/cfst/SegmentDeleg.v) |
| copy with a second linear parameter | mordido-perez.md gap list | core | `tree_deadlock_free` |
| `lp_main`, a µ body with a type variable | mordido-perez.md gap list | core, claimed | missing |
| `rt2_main`, an unopened segment result | mordido-perez.md gap list | core, claimed | missing |
| `fa_main`, a held channel sent at the first action | mordido-perez.md gap list | open | missing |

The reduced scheduler of examples/Scheduler.v (`sched_typed`) and the
Mordido–Pérez examples that only versions 2 and 3 of theories/mp cover
(`rr_main`, `ch3_main`, `rtA_main`, `rtB_main`, the partial send) are ours,
written after a paper, and keep their entries in mordido-perez.md.

## Claimed rejected

| Program | Source | Core verdict | Rocq theorem |
|---|---|---|---|
| Milner's scheduler with A_0 reversed | Dardha and Gay, Example 1 reversed | not deadlock free, no derivation | `msr_not_deadlock_free`, `msr_untypable`, `msr_untypable_source` (examples/lit/LitRejected.v), new. `ms_rev_underivable` (examples/Rejected.v) shows the needed facts close a cycle |
| PGV program 1, the T-Pair defect | pgv-counterexamples.txt §1 | not deadlock free, no derivation | `pcx1_not_deadlock_free`, `pcx1_untypable`, `pcx1_untypable_source`, new. Repaired PGV rejects it (`cx1_rejected`) |
| PGV program 2, a payload below its carrier | pgv-counterexamples.txt §2 | not deadlock free, no derivation | `pcx2_not_deadlock_free`, `pcx2_untypable`, `pcx2_untypable_source`, new. Repaired PGV rejects it (`cx2_rejected`) |
| the classic deadlock | Mordido and Pérez p. 3 | not deadlock free, no derivation | `dl_not_deadlock_free`, `dl_untypable`, `dl_untypable_source` (examples/cfst/CfstDeadlock.v) |
| Mordido–Pérez program 2, a partial send hides its payload | mordido-perez-counterexamples.txt §2 | not deadlock free, no derivation | `mcx2_not_deadlock_free`, `mcx2_untypable`, `mcx2_untypable_source`, new |
| Mordido–Pérez program 3, a polymorphic payload below its carrier | mordido-perez-counterexamples.txt §3 | not deadlock free, no derivation | `mcx3_not_deadlock_free`, `mcx3_untypable`, `mcx3_untypable_source`, new |
| `ll_main`, a held channel sent where the data decides | mordido-perez.md gap list | rejected, argument checked below | none |
| `sendTree t c; close d; send v c` | context-free.md K8 | outside, needs facts that depend on data | none |
| drop at Skip, `sd_main` | Mordido and Pérez gap list | not deadlock free in our semantics, needs a decision | `sd_not_deadlock_free` (examples/cfst/SkipDrop.v) |

Each `*_untypable` theorem states that no `styped ∅ [] [] (∅, None) e T`
derivation exists for any T with `prim T`, and each `*_untypable_source` adds
any number n of top-level points under any C₀ with `c0_acyclic n C₀`.

## What the new files prove

### The rejections, without inversion

examples/lit/LitRejected.v runs each of the five programs by hand to a
configuration where every thread waits on a send or a receive and no two
threads wait on one channel in opposite directions. `offers_stuck`
(examples/lit/LitLib.v) shows that such a configuration makes no τ step, for
any number of threads. A restricted channel remains, so the configuration is
not terminated, and the program is not deadlock free. `soundness` and
`soundness_source` then rule out a derivation. This is the argument of
`dl_untypable`, stated once.

The argument needs a program that deadlocks. All five do. PGV programs 1 and 2
contradict PGV's Theorem 3.13, and the two Mordido–Pérez programs contradict
their Theorem 3, as the counterexample files show. The reversed scheduler
deadlocks at once, because all six threads start with a receive.

The older argument for the reversed scheduler named three facts and showed
that they close a cycle (`ms_rev_underivable`). The step from the program to
the facts was a comment. `msr_untypable_source` removes that step.

Each program is the paper's with ∗ for 1 and `close` for `wait`. PGV program 1
writes `let z = (c, send ((), w)) in let (c, w) = z in …` as one let pair on
the pair. The evaluation order is PGV's, so the send on w runs while the pair
holds c. Mordido–Pérez program 2 writes the partial send as λc. send ⟨x, c⟩,
which is how their counterexample file reads it for our system. Program 3
erases the polymorphic payload.

### The falling sessions

pgv-adequacy.md §8.2 states that `fallxy` types in the core with a fresh point
per `new`, and names two facts, {ι_b ≺ x} at b and {c+1 ≺ ι_d} at d. The
derivation in examples/lit/Falling.v needs five, two at b and three at d.

```
x : ∅      b : {β ≺ ξ, ξ+2 ≺ β+1}      c : ∅      d : {γ+1 ≺ δ, δ ≺ γ+2, γ+2 ≺ δ+1}
```

The thread X sends on b at β while it holds x at ξ, then acts on x at ξ, ξ+1
and ξ+2 while it holds b at β+1. The main thread receives on c at γ+1 while it
holds d at δ, sends on d at δ while it holds c at γ+2, and closes c at γ+2
while it holds d at δ+1. The three facts at d each relate δ to γ, and
`cc_ok_out` of examples/cfst/CfstTools.v checks acyclicity and conservativity
(`fxb_ok`, `fxd_ok`). The only fact between two older points that the
constraint of d derives is γ+1 ≺ γ+2, which program order gives.

One encoding differs from PGV. The main thread writes `let c = send ((), c) in
…` as a let pair on ⟨send ⟨∗, c⟩, ∗⟩. Written as an application of a λ, the
λ needs an upper point above every action of its body, and the body creates d,
which has no point outside it. Every other let of the program is an
application, as in PGV.

`fall2` is the two-thread program of pgv-adequacy.md §2. Its one channel acts
at ξ, ξ+1 and ξ+2 and needs program order only. In PGV the priority of x falls
from 5 to 0. Here the points rise and the falling priorities have no
counterpart, which is the reading of §2, where a PGV priority describes an
instant and not a rank over time.

## Missing, with the reason

`lp_main` (mordido-perez.md, "µ bodies with a type variable"). The doc claims
that no rule excludes it and that unfolding the instantiated µ needs a fusion
lemma for `sinst` after `sren`, which types/Types.v does not have. That lemma
is a change outside examples/, so this branch leaves the claim as a claim.

`rt2_main` (mordido-perez.md, "Returning an unopened segment result"). The doc
rests the claim on drain of examples/cfst/TreeCopy.v, which returns the result
of its second recursive call through λr. r and so opens and repacks a segment
result. rt2_main itself has no derivation. Its derivation would wrap drain in
one more box with the same open and pack.

`fa_main` (mordido-perez.md, "Handing over a held channel inside a segment
function"). The doc marks it open and claims no verdict. A derivation needs a
box constraint ι ≡ κ[0] for the point ι of d.

## Rejections checked by argument

`ll_main` sends a channel d, held across the recursion, at the leftmost leaf of
a tree channel. The send rule of the core asks the payload's point to be the
payload point of the carrier (O-Send reads `payload_at`). The carrier at the
leftmost leaf sits at κ·w for the walk w to that leaf, so the payload point is
(κ·w)[0]. d has one point, fixed when the box is entered, and w depends on the
tree that arrives at run time. No single point equals (κ·w)[0] for every w, so
the box body has no derivation for an unknown tree. The argument is by hand
and reads only the send premise. The doc gives no client for ll, so the route
through `soundness` has no program to run. Mordido and Pérez's repaired rules reject it
too (R8 checks the payload above the carrier at every round).

## Corrections to the older files

Two files still call T2 of mordido-perez.md §9.5 rejected by our system. The
status paragraph for Mordido and Pérez in adequacy.md says it types there and
not here, and mordido-perez.md §9.5 says that no strict world types its
translation and that the order system rejects it. `bo_deadlock_free` and
`choice_deadlock_free` type it in the core. The rejection holds for the earlier
choice of K4 and K5, which puts both continuations at ι+1.

literature-examples.md says the step from a program to the facts its
derivation forces stays a comment. For the reversed scheduler that step is now
a theorem, and for the PGV and Mordido–Pérez counterexamples no such step is
needed.

pgv-adequacy.md §8.2 names two facts for `fallxy`. The derivation needs the
five above.

## Assumptions

`Print Assumptions` reports "Closed under the global context" for

```
pcx1_untypable  pcx1_untypable_source  pcx2_untypable  pcx2_untypable_source
msr_untypable   msr_untypable_source   mcx2_untypable  mcx2_untypable_source
mcx3_untypable  mcx3_untypable_source
fall2_deadlock_free  fallxy_deadlock_free  fallxy_styped  fxb_ok  fxd_ok
```

No typing rule and no existing statement changed. `_CoqProject` lists the
three new files, and the full build is green.
