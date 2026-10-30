# Extensions

State of 2026-10-30. The core is the design of ORDERS-SPEC.md after sharp edges 67,
mechanized with closed proofs of soundness and of every example. Four directions
extend it. Each has its own outline in this folder.

| | Direction | File | Depends on |
|---|---|---|---|
| A | Algorithmic typing | [algorithmic.md](algorithmic.md) | core |
| B | Context-free session types | [context-free.md](context-free.md) | core, parts of C |
| C | Data-dependent constraints | [data-dependent.md](data-dependent.md) | core |
| D | Subsumption of related systems | [subsumption.md](subsumption.md) | core, B for the CFST systems |

## Why these four

D positions the work. If every program that PGV, Padovani's system or GV♯ types
also types here, orders are a common generalization of priorities and trees. It
is the result a reader of the paper asks for first.

C is the problem that keeps coming back. The order of two points depends on data
in three places so far. A run picks a branch and with it an order (sharp edges 4,
deferred). A recursion orders the points of round k by a formula in k, which free
constraints now state (65). A context-free protocol ends its segment after a
number of actions that depends on the value sent. A design for facts that depend
on data would serve all three.

B is the natural next calculus. Context-free session types need polymorphism over
the continuation and polymorphic recursion, and their segments have data-dependent
length. They exercise the infinite constraints of 65 and need C.

A is optional for this work. It types examples automatically and fixes which
constraint fragments a tool can decide.

## Smaller extensions

These are open as well. None has an outline yet.

- Shared channels with acquire and release, in the style of Balzer, Toninho and
  Pfenning (ESOP 2019), whose types order the acquires by an acyclic order on
  worlds. The load balancer would then type statically.
- Asynchronous communication with buffers. Sends never block, so readiness
  constrains receives only. Sends already cost no index.
- Cancellation and exceptions in the style of Fowler et al. A dropped channel
  releases its points.
- Lock freedom through a fairness condition in the relation, comparable to the
  tickets of Padovani (CSL-LICS 2014).
- Order polymorphism on linear functions, beyond □. The earlier mechanization
  failed at term-level ∀ (spec §15).
- Borrowing. Context-free session types with borrowing still admit deadlocks.
  Orders could rule them out, with a borrowed entry lent for one frame.

## Order of work

C and D first. D is mostly a paper proof and C is the design question behind B.
B follows once C has settled how offsets depend on data. A runs alongside when an
example needs it.
