# Regions: orders inside, trees between

State of 2026-11-05. A design note, nothing here is mechanized. It records the
discussion of 2026-11-04/05 on data-dependent orders, the region design that came
out of it, and how it compares to paper 1 (GV♯), the current paper and the
connectivity-graph line of work. Claims about other papers cite the facts in the
papers store with their page.

## 1 The problem

A thread that talks to two partners in an order chosen at run time has no
derivation today.

```
R ⟨e, ⟨c, d⟩⟩ = let (b, e) = recv e in
                case b of inl _ ⇒ close c; close d; close e
                        | inr _ ⇒ close d; close c; close e
```

Closing c while d is still held needs α ≺ β, the other branch needs β ≺ α. Both
facts together are a cycle. The program is deadlock free when the partners on c
and d are independent threads. Plain GV types it, because GV has no order at all.
Every order- or priority-based system rejects it, ours included
(`db_component_unrealizable`, theories/examples/DataBranch.v), and PCP and PGV by
their rules.

Paper 1's static system is GV, so paper 1 types this program and the current
paper does not. The current system does not subsume paper 1's static system.

Two kinds of run-time dependence show up in the examples.

| | the order is fixed by | typical program |
|---|---|---|
| decisions | one thread, from data it receives or computes | dispatcher with per-request order, fallback to a backup, R above |
| shared data | a value every party can compute | transfers ordered by account id, rings and grids of size n, round-dependent orders |

The first kind lives in tree-shaped parts of a program. The second lives inside
cycles. Regions solve the first. Guarded shared facts (§6) solve the second.

### What does not work

- A dead arm can already learn a false fact. Typing `inj₁ ∗` at
  `∗ ⊕ ∃{d ≺ c}. ∗` lets the right arm open the existential and assume d ≺ c
  next to the outer c ≺ d. Typing never asks the hypotheses of an arm to be
  consistent, and the relation never runs the arm. This types programs whose
  branch is fixed statically (`db_typed`). It fails as soon as the sender may send
  either label, because one world then has to make both arm constraints true
  (`db_component_sides`). The running example SemFlag.v discards the payloads in
  both arms for this reason. A discarded payload is unlimited, a box, and a box
  has nothing to open.
- A second channel kind with `fork`, as in GV, next to `new` for ordered
  channels. Mixing the two kinds is unsound without topology in the types. If A
  keeps c and sends c′ over a tree channel t to B, A blocked on c and B blocked on
  t form a cycle that neither gate sees. Rejected by the author.
- Pending choices with an owner (data-dependent-worlds.md §4.4). Sound at the
  level of worlds (BranchWorlds.v), but it needs an explicit linear ownership
  token per choice and a family of worlds per choice vector. Regions cover the
  same programs without either.

## 2 The principle

The gate is where deadlock freedom is enforced. A thread blocked at u that still
needs v must have Γ ⊢ u ≺ v. A deadlock through this thread is a cycle of waiting
that enters at v and leaves at u. Such a cycle passes through the channel of u
and the channel of v, so both channels lie on a common cycle of the topology.

If the two channels lie on no common cycle, no deadlock passes through the thread
via u and v, and no fact is needed.

A **region** is a set of channels that may lie on a common cycle of the
topology. In graph terms a region is a union of biconnected components of the
graph of threads and channels. Region membership is a property of the channel,
the same for both ends and fixed for the channel's life. Points say when,
regions say where.

## 3 Static design

### Creation and the constraint language

`new` places the fresh point in a region, an existing one or a fresh one.

```
let (a, b) = new ∗ in r        adds ι ∈ r to Γ
```

The constraint language gains two atoms.

- p ∈ r, membership. Offsets inherit it, p+k ∈ r when p ∈ r. A payload
  constraint may state self[j] ∈ r′, relative to the carrier like the points of a
  payload.
- r ≠ r′, region inequality, for box constraints.

Types do not change. Session types keep carrying a point, and the point carries
its region through Γ.

### The gate

Blocking at u needs Γ ⊢ u ≺ v only for the heads v of the future with
Γ ⊢ region(v) = region(u). Heads in other regions impose nothing.

### The invariant and its three side conditions

Invariant: every cycle of the topology stays inside one region. Three operations
can close a cycle, and each checks a condition on the thread's own Δ. The
invariant makes each check local.

| operation | side condition | why it suffices |
|---|---|---|
| send x over c, x ∈ r, c ∈ r′, r ≠ r′ | the sender keeps no other end in r | another path from the sender to x's partner leaves through a different region, and by the invariant cannot return. Moving x closes no cycle |
| spawn | for every region other than that of the channels split between parent and child, the parent's ends in that region go entirely to one side | otherwise parent and child connect twice through different regions |
| link x y, x ∈ r, y ∈ r′, r ≠ r′ | as for send | linking joins the partners of x and y |

Same-region sends, spawns and links need no condition. Cycles inside a region are
allowed and guarded by facts, as today.

### Boxes

A box is typed for every assignment of its region variables. By default that
includes the assignment where all are equal, which gives exactly today's checks.
A box constraint may state r ≠ r′ for more precision.

### Conservativity

With one region the gate and the side conditions are those of today. Every
existing derivation stays valid.

## 4 Examples

`⟨ρ⟩` marks the region of an end where it helps the reading. It is derived from
Γ, not written in types.

**The bit program.** c, d and e get fresh regions at creation, and each spawn
takes all remaining ends of one region.

```
main = let (c, c′) = new ∗ in r₁ in let (d, d′) = new ∗ in r₂ in
       let (e, e′) = new ∗ in r₃ in
       spawn (λ_. close c′); spawn (λ_. close d′);
       spawn (λ_. close (send ⟨inj₁ ∗, e′⟩));
       R ⟨e, ⟨c, d⟩⟩
```

At `close c` the future holds β ∈ r₂ and γ+1 ∈ r₃, neither in r₁. No fact is
needed in either branch. Today the program needs α ≺ β and β ≺ α.

**A proxy that receives a channel.**

```
proxy ⟨c⟩ = let (x, c) = recv c in          -- x at α[0], self[0] ∈ r′ fresh
            let (n, c) = recv c in
            if n > 0 then send ⟨n, x⟩; close c; close x
                     else close c; send ⟨n, x⟩; close x
```

The sender keeps no other end of x's region, so the send satisfies its side
condition and the payload may declare a fresh region. The order between α[0]
and α+2 is free per branch.

**The case that must stay rejected.** A creates (c, c′) in r_c, sends c′ over t
in r_t and keeps c. The send's side condition fails unless r_c = r_t. With one
region the gate asks for a shared fact between c and t, and B's order
contradicts it.

**A recursive merger.**

```
merge : □(∀α β r₁ r₂. {r₁ ≠ r₂}. ∗ ⊸ L@α ⊗ L@β ⊸ ∗)    L = µt. ?Bool.t,  α ∈ r₁, β ∈ r₂
merge ⟨l, r⟩ = let (x, l) = recv l in
               if x then let (_, r) = recv r in force merge ⟨l, r⟩
                    else force merge ⟨l, r⟩
```

r₁ ≠ r₂ says the producers are not connected behind the merger, and the body
reads l and r in a data-dependent pattern with no facts.

**Shared accounts.** `transfer ⟨a, b⟩ = if id a < id b then (a; b) else (b; a)`.
Other transfers connect the accounts, so a and b share a region and the gate asks
for a shared fact. Regions correctly reject it. It needs §6.

**GV (conjecture).** Every `new` gets a fresh region, so every region holds one
channel. The fork pattern, `new` followed by a spawn that takes one end,
satisfies the spawn condition. A GV sender never holds both ends of a channel, so
it keeps no other end of the sent channel's region. Every gate check is vacuous,
and GV should embed with no facts.

## 5 Semantic side, sketch

The world maps points to regions. The map is fixed at creation and therefore
monotone. Two arguments combine.

- Inside a region, readiness follows from the strict order of points, as today.
- Between regions, the relation must maintain the invariant that cycles stay in
  a region, and readiness follows from it by an argument over the acyclic graph
  of regions and threads, waiting induction in the style of Jacobs, Balzer and
  Krebbers (connectivity graphs, p. 18). Their insertion and exchange lemmas
  (p. 19) are the counterparts of the three side conditions.

This puts a second proof principle into the core next to the order argument. It
touches readiness and the cut, which makes it more work than context-free
sessions, which only add type formers.

## 6 Guarded shared facts

Inside a region, an order that depends on shared data needs facts guarded by
values, g ⇒ φ.

- Points indexed by term values, p + e and p[e], for naturals, booleans and
  identifiers reflected through singleton or refinement types.
- Branching refines Γ by the path condition.
- Entailment reasons under guards, through the `Solver` interface
  (theories/algorithmic/Solver.v). Decidability is not a requirement for the
  design.

This types transfers ordered by id, rings and grids of size n, and the
round-dependent order of SemRounds.v. It is independent of regions and composes
with them. Regions handle orders between parts that no cycle joins, guarded facts
handle orders inside a cycle.

## 7 Comparison

| | connectivity graphs, LinearActris | paper 1 (GV♯) | paper 2, current | paper 2 + regions |
|---|---|---|---|---|
| static type system | linear GV, no annotations | linear GV | points, facts, creation constraints, boxes, existentials | the same, plus p ∈ r and r ≠ r′ |
| channel creation | `fork` | `fork` | `new` and `spawn` | `new … in r` and `spawn` |
| topologies typable statically | trees | trees | cycles guarded by facts | cycles inside a region, a forest between regions |
| topologies the semantic judgment accepts | trees (strong acyclicity is a global invariant) | anything inside a component, a tree at the external interface | anything consistent with a strict order of points | paper 2 plus forest-shaped freedom between regions |
| data-dependent order in a tree | free | free | rejected | free between regions |
| data-dependent order inside a cycle | not typable | semantic only | semantic only (SemFlag, SemRounds) | needs §6 |
| order polymorphism, recursion over orders | not needed | not needed | ∀/∃ over points, payload points, CFST walks | the same |
| extensions | sums, unrestricted types, recursive types and sessions, references (LinearActris), multiparty (MPGV) | branching, recursion, unrestricted channels, linking | choice, context-free sessions, sums, existentials | the same |
| subsumes | GV | GV | PGV, Padovani–Novara, Mordido–Pérez (mechanized fragments) | GV and the three priority systems (conjecture) |
| properties | partial deadlock freedom, leak freedom, asynchronous | safety, deadlock freedom, synchronous | deadlock freedom, synchronous | the same |
| proof principle | acyclic connectivity graph, waiting induction | logical relation, tree invariant at the interface | logical relation, strict partial order in worlds | order inside regions, topology between them |

Sources for the first column. Connectivity graphs (Jacobs, Balzer, Krebbers,
POPL 2022): a linear session-typed λ-calculus without order annotations, `fork`
fusing creation and spawn, the invariant that the graph has no undirected cycles
(p. 8, p. 10), waiting induction (p. 18), extensions with sums, unrestricted and
equi-recursive types (p. 23), partial deadlock and leak freedom (p. 24).
LinearActris (POPL 2024): strong acyclicity, at most one path between two nodes
(p. 17), cyclic topologies outside the logic (p. 4), a semantic GV system with
recursive types, subtyping, polymorphism and unique references (p. 5). Multiparty
GV (ICFP 2022): cycles only within one multiparty session, without priorities
(p. 5). Paper 1: the abstract and introduction on the old repo's main.

### Observations

1. Neither line subsumes the other. LinearActris states it (p. 2), "other methods
   neither supersede nor subsume session types in the range of programs they can
   prove to be deadlock free". It also writes (p. 26) that it is "far from clear
   how to build a logical relation for a language with session types in terms of
   a separation logic with lock orders". The current paper is such a logical
   relation, with an order-based deadlock argument.
2. Paper 2 gave up part of paper 1. Paper 1's static system types every
   data-dependent order in a tree. Paper 2 traded the tree discipline for orders,
   gained cycles and the priority systems, and lost those programs. The related
   work should say so, or regions should fix it.
3. Regions are paper 1's insight made static. Paper 1 shows that the topological
   invariant is needed only at the external interface and that a component may be
   cyclic inside. A region is a component that may be cyclic inside, and the
   forest between regions is the interface invariant. Paper 2's facts are the
   static support inside a region that paper 1 lacked.
4. λ-lock++ (Jacobs and Balzer, POPL 2023) already has regions, for locks. Lock
   groups permit cyclic sharing inside a group under a local order, and the
   sharing topology's invariant holds between groups (p. 3). "Local orders are
   compositional in that they remove the need for local orders to comply with each
   other or a global lock order when acquiring locks from distinct groups" (p. 3),
   and "one is always free to acquire locks from different lock groups" (p. 21).
   The order inside a group is the position in a type-level list of fixed length,
   so polymorphism ranges over positions, not over order variables (p. 27).
   Novelty of regions has to be framed against this. What regions add is the
   session-typed version with a polymorphic fact theory (∀/∃ over points, payload
   points, context-free walks), a logical relation, and the GV embedding next to
   the PGV, Padovani–Novara and Mordido–Pérez embeddings.

## 8 Assessment

| | |
|---|---|
| fixes | data-dependent orders in tree-shaped programs, which GV accepts and every order-based system rejects |
| static cost | small. Two atoms in the constraint language, a region at `new`, the gate restricted to one region, three side conditions. No change to type syntax |
| semantic cost | high. Topology reasoning next to the worlds, maintenance of the invariant under reduction, a combined readiness argument |
| paper cost | a second principle next to strict partial orders |
| payoff | a GV embedding without a second channel kind, a static form of paper 1's interface invariant, and with §6 dynamic orders inside cycles |

Recommendation: a follow-up paper, not an extension section of the current one.
Choice and context-free sessions add type formers on an unchanged core. Regions
change the gate and the readiness argument. Order of work: the static rules for
the core (gate, new, spawn, send, receive, link) written out formally, the
examples of §4 checked on paper, then a sketch of the combined readiness argument,
then Rocq.

## 9 Open points

1. Payload regions in recursive and context-free sessions. The continuation at
   x[i] keeps x's region. Whether the channel returned by a segment call keeps
   the region of its argument is unchecked.
2. Region polymorphism for recursive servers. The default, all region variables
   possibly equal, is safe. Whether GV-style recursion needs r ≠ r′ in box
   constraints is untested.
3. The spawn condition for closures that capture ends of several regions, and how
   much of it the arrow type has to expose.
4. The GV embedding is a conjecture until the translation is written and the
   side conditions are checked on GV's fork, delegation and recursion.
