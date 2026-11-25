# Lock freedom: plan

Branch `liveness`, after `live_soundness`. Draft for discussion, nothing is
implemented. Section 9 of liveness.md has the counterexamples this plan
answers.

## 0  Target and scope

A thread is pending when its redex is a session action on an end e. A run is
lock free when every pending thread later takes part in a step. A program is
lock free when every weakly fair maximal run from it is lock free. Weak
fairness is per thread: no thread stays enabled from some position on without
taking part in a step. A blocked thread is enabled exactly while its partner
offers the dual action, and an offer persists until it fires, so weak fairness
suffices.

Out of scope. Recursion whose termination rests on data (`fibo_pn`, the CFST
tree servers in non-tail position, Padovani's fact). Padovani's lock-free
system rejects them for the same reason (padovani2014deadlock, p8, Example
III.6 needs negative priorities, and p7 restricts lock freedom to natural
priorities).

## 1  What is missing, and why fairness alone does not supply it

Fairness helps only an enabled thread. Three patterns keep a pending thread C
disabled forever while the program stays live. Each holds the end ē that C
waits for.

1. Postponement. The holder A takes channel steps forever and never acts on ē
   (liveness.md §9, the loop on fresh channels).
2. Endless delegation. ē travels from thread to thread forever and nobody acts
   on it (padovani2014deadlock, p2, Example (2)).
3. Growing chains. A blocks on a fresh point below ē, served by a thread that
   blocks on a fresher point below that, and so on (liveness.md §9, the
   chatterbox chain).

The gate already constrains all three. A thread that holds ē unoffered offers
only below the partner point of ē (`below_rest`, Readiness.v). What is missing
is a bound on how often this can happen.

## 2  Problems in the current state

These affect generality and must be settled before lock freedom.

**G1  Worlds are chosen per index.** O-New, Q-Admin and the link clauses
choose the next world existentially, separately for every n. A run therefore
has no canonical world, and any bound stored in a world may grow with n.
Adequacy for deadlock freedom never needed a run-level world. Lock freedom
does, because its proof needs a bound fixed before the index is chosen.
Every later run-level property (lock freedom, fair termination, resource
bounds) meets the same wall.

**G2  Links are channel steps but compare nothing.** A link costs 1 and
counts as progress in `live_runs`, yet the gate exempts it (`link_t`,
sharp edge 68). A loop `let (a, b) = new in link a b; f ()` is guarded, takes
a channel step per round, holds any end forever and is accepted. It observes
nothing. So `live_runs` counts silent rounds as progress, and lock freedom has
to account for links separately.

**G3  Points are not linear.** `new@x` may place a second channel at a point
that already carries one. A criterion that counts points below ē undercounts
actions. Every bound below therefore counts actions, never points.

**G4  The live relation lacks the semantic box rule.** SemRounds stays out
because its box is semantic. Every semantic rule of the old relation should
have a live counterpart, otherwise semantic typing loses examples at each
extension.

**G5  Two relations.** The base and the live relation are two developments of
about 12k lines each. A relation parametric in its cost function would carry
both. This is a refactoring question, independent of lock freedom.

**G6  No thread identities.** The process soup is a multiset. Fairness needs
to name threads.

## 3  Design

### 3.1  Two quantities, both local

Lock freedom needs exactly two bounds, one for patterns 1 and 2 and one for
pattern 3. Both mirror Padovani's two annotations, with tickets and priorities
(padovani2014deadlock, p2 and p7).

(Revised in §7: fuel ticks only while the partner end is offered.)

**Fuel** bounds patterns 1 and 2. Every held entry k carries fuel φ(k) ∈ ℕ. A
channel step of the holder on another entry, a link included, decrements φ(k).
Sending k passes its remaining fuel minus one. An action on k itself gives the
entry at its next point fresh fuel. At φ(k) = 0 the holder offers k next.
Fuel is thread-local, so other threads cannot interfere with it.

**Rank** bounds pattern 3. Every point carries rk(x) ∈ ℕ, fixed when the point
enters the world. The gate fact u ≺ ȳ that a blocked thread relies on implies
rk u < rk y. Ranks are fixed, so extensions preserve them, and no thread can
change another's.

Fuel also settles G2. A link is a step of its thread and consumes fuel like
any other step.

### 3.2  Uniformity (G1)

Fuel and rank values must not depend on the index. There are two ways.

- **(U1) A choice oracle.** The live relation takes a function ω that makes
  the choices at O-New, Q-Admin and the link clauses: the fresh name, the
  extension, the rank of new points and the fuel of new entries. The
  relation becomes `LPrel ω n W Σ T p`, and adequacy assumes
  `∀ n, LPrel ω n W ∅ T p` for one ω. The fundamental theorem proves
  `∃ ω`. The composition lemmas combine the oracles of their components,
  split by which side created the name. Their premises gain ω and keep the
  rest of their form.
- **(U2) Static annotations.** Fuel and rank become part of the session
  types, as Padovani does. Types evolve deterministically along a run, so
  uniformity is free. The cost is that every session type in the paper
  gains two numbers.

Recommendation: U1. It keeps the type syntax as it is and fixes G1 for every
later run-level property. It changes the shape of the composition
statements by one parameter, which needs your approval.

### 3.3  The criterion, free of types

Stated over the instrumented semantics of §4.1, with no logical relation
involved.

```
Theorem lf_criterion p :
  (∀ q, p →* q → local_progress q) →          from the LR, per state
  no_tau_divergence p →                        live_adequacy
  fuel_bounded p → rank_bounded p →            from the budgeted relation
  lock_free p.
```

Here local_progress q means that the dependency chain of every pending thread
in q, through the holders of the ends it waits for, ends in an enabled
thread. It follows from `ready_p` and `above_offered` at one state, because
the world restricted to the finitely many held heads is a finite strict
order.

(§7: the induction keeps its shape. The fuel argument applies because C is
pending, so its end is offered.)

Proof. By induction on (rk y, φ of the holder's entry for ȳ), lexicographic,
for C pending at y. Let A be the holder of ȳ. A leaves every τ sequence by no
τ-divergence. If A blocks at u, the gate gives rk u < rk y, and the induction
hypothesis fires A's offer, so A steps again. Every step of A on another entry
lowers φ. At φ = 0, A offers ȳ. Both offers persist, C is enabled from then
on, and weak fairness fires the synchronization. Delegation moves ȳ to a new
holder with strictly less fuel, which the same measure covers.

### 3.4  The static fragment

Fuel and rank exist for a program when no recursion round leaves an end
unbounded. Four rules, each closing one door. They are read off the box body,
like the guard of sharp edge 160.

| Rule | Excludes |
|---|---|
| R1 empty future at recursion: a call that can unroll a recursive box happens with empty future | postponement by a frame, non-tail recursion |
| R2 advance before recursion: every end passed into a recursive call was acted on in the current round, or created in it | postponement by holding across rounds |
| R3 no waiting on later rounds: a round does not act on an end whose partner it passes into a recursive call | growing chains |
| R4 no blind forwarding in a round: an end received in a round is acted on before the round sends it on | endless delegation |

(§7: R2 stays as it is in the static fragment, which stays conservative.)

Static fuel then equals the length of a round in channel steps. That length
is finite by the guard and R1, and the oracle can compute it from the typing
derivation. Static ranks come from the creation constraints. R3 ensures that
a round never needs a rank below its own.

**Why no numbers in the fragment.** A fuel bound d > 1 per action buys
nothing without reasoning about data. A program that acts on b in every
second round is the same program with a body unrolled twice, and that body
satisfies R2 with fuel 1. A bound that depends on a counter in the data is
termination on data, which is out of scope. So the fragment needs no
annotation, and every static bound is derivable by unrolling (see
minimal-rules).

**Expected verdicts** (to be confirmed in phase 0):

- In, as live programs that satisfy R1 to R4: the forwarder, producer and
  consumer, SemRounds once G4 is closed, Milner's scheduler, the tail call,
  servers that act on every client end in every round.
- Out: KobForwarder (guard already), `fibo_pn` and fact (data), the CFST tree
  servers in non-tail position (R1), servers that serve one client only on
  request (R2, which is correct, because a client that never requests starves
  the other).

## 4  Phases

**Phase 0, on paper, about two days.**
- Write the definitions of §3.1.
- Prove `lf_criterion`, including delegation and links.
- Prove that R1 to R4 give fuel and rank. R3 is the weakest point: show that
  without a round waiting on a later one, ranks never run out, or replace R3
  with a rank condition at box instantiation (recursive calls instantiated at
  points not below the caller's), as Padovani's shift n ≥ 0 does (p7, Lemma
  III.2(3)).
- Check the expected verdicts against the examples.

Go or no-go with you before any Rocq.

**Phase 1, type-free, about 2 days.**
- An instrumented semantics in a new file, with thread identifiers and labels
  naming the threads of each step. An erasure lemma to the existing
  semantics. Nothing existing changes.
- Fairness, pending and `lock_free` on it.
- `local_progress` from `ready_p` and `above_offered`. This adds a lemma and
  changes no definition.
- `lf_criterion` over abstract fuel and rank hypotheses.

**Phase 2, the budgeted live relation, about a week.**
- The oracle ω (U1), rank on points, fuel on entries.
- The O-σ clauses decrement and refresh fuel, and the gate checks rank.
- Port monotonicity, bind, the constants, Internalize, P-Connect, P-Term and
  P-Join with ω. Statements change by the parameter ω only.
- Adequacy: `fuel_bounded` and `rank_bounded` from `∀ n, LPrel ω n`.

**Phase 3, the fragment, about a week.**
- R1 to R4 as a boolean check next to `guarded`, and `lfptyped := gptyped ∧ R`.
- A fundamental theorem: `lfptyped W ∅ p T → ∃ ω, ∀ n, LPrel ω n W ∅ T p`.
- `lf_soundness : lfptyped W ∅ p T → lock_free p`.
- Examples as lock-free theorems. KobForwarder, `fibo_pn` and the CFST tree
  servers become rejection theorems where cheap.

**Phase 4, paper.** One section on liveness and lock freedom. Order-free
termination of internal steps, then fuel and rank as tickets and priorities
over the points that are already there.

## 5  Decisions for you

1. Uniformity by an oracle (U1, recommended) or by annotations in types (U2).
   U1 adds the parameter ω to the composition statements.
2. The static fragment R1 to R4, or Padovani's rank condition at instantiation
   in place of R3 (decided in phase 0).
3. Links (G2). Under fuel, links are harmless for lock freedom. `live_runs`
   still counts them as progress. Option: give the link τ cost 0, which makes
   link loops τ-divergence. This changes the cost table of liveness.md §2.
4. G4 before or after lock freedom. Without it SemRounds stays out of both
   theorems.

## 6  Stage 0a results and revisions (2026-11-08)

A paper proof of `lf_criterion` exists (stage 0a agent report, folded in
here). The measure is lexicographic on (rk of the waiting point, fuel of the
partner entry, the Acc structure of the admin steps of its holders). This is
Padovani's priority, tickets and depth (padovani2014deadlock, p15, Def. B.8).

### 6.1  Corrections to §3

1. **Links can refresh fuel.** In the loop `let (a, b) = new@y in link ⟨e, a⟩;
   e := b`, the holder of C's partner replaces it by a fresh end at the same
   point after every round. A spawn variant hands each fresh end to a new
   thread. Fuel per point misses both, because a link moves no point.
   With the author's decision that a link τ costs 0 (§5, decision 3),
   a link becomes an admin step. Both loops are then τ-divergent and
   rejected by `no_tau_divergence`. With links at cost 1, fuel needs caps per
   entry that strictly decrease across links.
2. **The rank condition** is x ≺ z ⇒ rk x < rk z, applied to the gate fact
   u ≺ y of a holder of ȳ blocked at u. §3.1 mixed y and ȳ.
3. **local_progress cannot come from `ready_p`.** For a closed process Σ = ∅,
   and `above_offered` says nothing about restricted channels. The per-thread
   gates (`below_rest` at each thread's Θ) must be part of the instrumented
   invariant. With rank_bounded and safety, local_progress is then redundant.
4. **Finished threads.** A thread that finishes holds nothing only if the
   main result type has no channels. lf_soundness assumes `prim T`, as
   live_soundness already does.

### 6.2  Lemmas the proof needs

Frozen threads keep their term. Every live entry has one holder and a dual
peer. Sync steps name both holders. Mutual offers stay enabled. In a closed
state every link redex is enabled. Admin redexes are always enabled. Every
thread is a value or has one redex (admin, link, or an action on one entry).
Links move no point. Steps commute with renaming. The admin steps of the
successive holders of one entry replay as a padmin chain. Finished threads
hold nothing.

### 6.3  Open: classical reasoning

The step "the partner's fuel is eventually constant" argues by contradiction
on an infinite run. That needs classical logic, which means an axiom such as
excluded middle, and adding one needs the author's approval. A constructive
alternative states fairness with explicit deadlines (a fair scheduler gives,
for every enabled thread, a position by which it steps). Lock freedom then
comes with a computable bound. To be decided before stage 1 closes
lf_criterion.

### 6.4  Third option for uniformity: a constant world

Proposed by the author. Forbid a larger world at O-New and Q-Admin, so W′ = W
and every channel is created with `new@x` at a point that already exists.
The world is then the same along the whole run and for every index. Rank and
fuel live in the world per point (`rk, fu : point → ℕ`). They are uniform
without an oracle, and composition statements keep their form. Fresh names
and cofinite freshness disappear from the relation. The cost is that the
lock-free fragment uses only `new@x`, with the facts for all points given up
front as patterns over shifts and fields. On the branch, 8 example files use
fresh `new` (FactoryEx, ChoiceEnc, ChoiceTranslate, ChoiceTranslateEx,
DataBranch, FreshTools, ChoiceNegative, LitRejected). With links as admin
steps (6.1.1), fuel per point suffices, so the caps per entry are unneeded.
Stage 0b checks the examples against this option.

## 7  Fuel ticks only while the partner waits (2026-11-08, approved by the author)

**Problem.** Fuel per holder step rejects lock-free programs that hold an
end forever while nobody waits on it.

```
let (ctl, ctl') = new in let (r, r') = new in
spawn (rec server. recv r'; server);     holds ctl' forever, never uses it
rec client. send r (); client            holds ctl forever, never uses it
```

Nobody is ever pending on ctl, so the program is lock free by §0. Under §3.1,
however, φ(ctl') runs out after a few server rounds. Padovani's tickets have
the same limit.

**Change.** φ(c) decrements on a holder step on another entry only while
the partner end c̄ is offered. The oracle, or the world under §6.4, fixes the
value when the partner starts offering. Acting on c refills it. Sending c
while its partner is offered passes φ − 1. Rank is unchanged. It constrains
only gate facts that a blocked thread relies on. In the controller, every
point of r gets rank 0 and ctl rank 1.

**Checks.**
- The postponement program of liveness.md §9 stays rejected. Its main thread
  offers b from the start, so the holder's fuel runs out.
- The controller is accepted.
- Endless delegation of an end someone waits on stays rejected.

**Compositionality, and where it bites.** A single thread cannot see
whether its partner offers. A component whose end is external (in Σ) has to
assume the partner may offer at any time, and its fuel ticks as before.
Fuel ticks "only while offered" only where both ends lie inside the process,
on a restricted channel, so P can see the offer. Consequences:
- The compositional fundamental theorem keeps the conservative behaviour.
  The static fragment keeps R2 as it is.
- The controller types semantically only by a direct proof at the process
  level, where ctl is restricted. It does not type component by component.
  This makes it a "semantic typing types more" example, beside SemRounds.
- Marking ends whose partner never waits (in the type) would let
  composition see it too. Not pursued, because it adds annotations.

**Terminology for the paper.** The condition is stated as well-foundedness
of waiting, with fuel and rank as proof devices. Plain well-foundedness of ≺
is too weak: the postponement program has an ascending chain below b of
order type ω, which is well-founded with b at height ω.

**Required example.** The controller, typed by a direct semantic proof, and
rejected by the static fragment (R2).

## 8  Motivating examples

Every change to the relation answers one program. "Rocq" marks a closed
theorem. All other entries are argued on paper.

### Liveness (no τ-divergence)

| Program | What goes wrong | Change it motivates |
|---|---|---|
| Kobayashi's server (KobForwarder.v): each call creates a reply channel, spawns the next call, blocks | infinite new, spawn, β, no channel step, deadlock free (Rocq `kob_tau_diverges`) | least fixpoint over internal steps, costs 0 and 1 |
| PN's ⟨fix λx.x⟩ (`div_main`) | diverges internally, PN types it (Rocq `pn_div_not_guarded`) | guard as a separate fragment, E-Exp stays unguarded for subsumption |
| typed program diverging under the old static system | Rocq `live_fundamental_false` | guard on recursion |
| `!(x. let ∗ = (force x) g in λy.y)`, forced | forcing the self reruns a non-λ body forever (Rocq `live_guarded_unrepaired_false`) | force of the self only under the λs of the body (sharp edge 161) |
| `rec f. let (a, b) = new in link a b; f ()` | a link per round counts as progress, nothing is observed | link τ costs 0, link leaves the guard's paying primitives |
| one synchronization of an internalized process = send plus receive of the original | index halves per step (sharp edge 44) | synchronization costs 2 |

### Lock freedom (every waiting thread is served)

| Program | What goes wrong | Change it motivates |
|---|---|---|
| A holds b and loops forever: new channel below b̄, one step on it. C waits on b̄ | A is live, C starves under every fair scheduler | fuel, because rank alone does not help (every world has finitely many points below b̄) |
| A holds b and loops on a, served by B. C waits on b̄ | same, with ω many points below b̄ | fuel |
| a server receives an end and sends it back on its next point, forever (Padovani's Example (2), padovani2014deadlock p2) | the end travels forever, its waiter starves | fuel passes with −1 when an end is sent (tickets) |
| each thread spawns the next and blocks on a fresh point below its predecessor's, after one step with a chatterbox | the waiting chain grows forever, the first waiter starves | rank |
| `let (a, b) = new@y in link ⟨e, a⟩; e := b`, looped by the holder of C's partner | each link hands C a fresh partner with fresh fuel | link as an internal step (cost 0), or caps per entry |
| `let _ = server () in close b` with an infinite server | b sits in the frame forever | R1, recursion only with empty future |
| a server that serves client b only when client a requests | b's waiter starves if a never requests | R2, correctly rejected |
| main returns a channel end | a finished thread may hold the partner | premise `prim T` |
| the controller (§7): both sides hold ctl forever, nobody waits on it | lock free, but holder-side fuel rejects it | fuel ticks only while the partner waits |

### Out of scope

| Program | Why |
|---|---|
| `fibo_pn`, Padovani's fact | recursion bounded by data, needs termination checking, Padovani's lock-free system rejects them too (padovani2014deadlock p8, Example III.6) |
| CFST tree servers recursing in non-tail position | an infinite tree from the client keeps the frame forever |

## 9  The strongest property in reach

Lock freedom together with no τ-divergence and weak fairness gives individual
progress: in every weakly fair maximal run, every thread terminates or takes
part in infinitely many channel steps. Proof: a thread with an internal
redex takes finitely many internal steps (no τ-divergence) and is fired by
fairness. A pending thread is served (lock freedom). So no thread stops
forever short of a value. This is stated as a corollary `thread_progress` in
stage 3.

Stronger still is fair termination (every fair run terminates, as in
padovani2025fair). It needs termination of recursion, which is out of scope.

## 10  Stage 0b results: the revised design (2026-11-08)

Stage 0b read the rules and the examples against the constant world.
Verdicts come from reading, not from Rocq. The design below supersedes §3.1
and §3.4 where they differ.

### 10.1  Counterexamples to §3.4

- **C1, a spawner chain.** A recursive box creates a channel at κ[0] each
  round, spawns a thread that blocks on it while holding the previous end,
  and recurses at κ[0]. Every round takes a channel step with a chatterbox.
  It satisfies the guard and R1 to R4, yet main starves. The gate needs
  κ[0]^{k+1} ≺ κ[0]^k, an infinite descending chain. R3 misses it.
- **C1′.** The same chain with points shifted upward at every call. The
  alternative "recursive calls not below the caller's points" misses it too,
  because ≺ is not closed under shift and field.
- **C2, a pipeline.** Each stage receives, creates a channel, spawns the next
  stage on one end, and sends on the other. Lock free, rejected by R3.
- **C3, link refresh with a chatter step.** The holder of C's partner links it
  to a fresh end each round and also takes a step on another channel. Not
  τ-divergent even with links at cost 0, accepted by R1 to R4, and C starves.
- **C4.** R4 rejects the Forwarder, which forwards a received end once.

### 10.2  The revised conditions

- **Guard**, with link removed from the paying primitives (stage 2a).
- **R1.** A potentially recursive call happens with empty future. A
  potentially recursive call is a force of a box whose body forces, or of a
  box variable, parameter or received box. R1′ (only the call's results
  remain in the frame) would admit TreeSum. Left for later.
- **R2′, advance.** On every path through a round, every end passed into a
  potentially recursive call, and every argument of a link, was acted on
  earlier in the round or created in it. The link clause closes C3.
- **R4′, bounded forwarding.** The graph with an edge A → B, when an end
  received on a carrier of session type A is sent unacted on a carrier of
  type B (types up to points), is acyclic. It admits the Forwarder and
  rejects forwarding rings.
- **Rank.** The world is well founded: `well_founded (w_lt W)`. This is a
  condition on W, checked once, not a check on box bodies. C1 and C1′ have
  harmless bodies, and the descending chain lives in the facts. The union of
  two well-founded constraint families can descend, so a check per box would
  not compose. Under the constant world every gate fact at runtime is a fact
  of W. So no rank function is needed. Acc on W suffices.
- **R3 is dropped.**

### 10.3  Fuel and rank, simplified

- **Rank** needs no number. Well-foundedness of W replaces rk. A rank into ℕ
  would fail on TailCall ({ι+k ≺ ι[0] | k}), the CFST scheduler and TreeSum,
  which have ceilings. Well-founded induction (Acc) handles ceilings. The
  claim in liveness.md §9 that lock freedom needs a rank into ℕ is wrong once
  fuel is present.
- **Fuel** is one constant N per program: N = (d+1)·2L, with L the maximum
  number of channel steps in a round (finite by the guard and R1) and d the
  longest path in the R4′ graph. The factor 2 covers an end acted on at the
  start of round k and next at the end of round k+1. The relation takes N as
  a parameter, so fuel is uniform by construction. Per-point fuel is
  unnecessary. The semantic judgment hides N: `⊨ p := ∃ N, ∀ n, LPrel N n p`.
  The relation is monotone in N (more fuel asks less), so composition takes
  the maximum. The fundamental theorem computes N from the program text. A
  direct semantic proof picks its own N. The definition never computes N
  from syntax, so it stays a semantic notion.

### 10.4  The constant world and the examples

About 34 example files type a fresh `new`, not 8. Almost all are top-level
`new` in a closed main typed in the empty world (sharp edge 105). Each
becomes a constant of W, and the creation facts become facts of W. Three
files have a fresh `new` inside a box: FactoryEx, FreshBetween and FreshMany.
They stay typable, with a stronger box constraint that the caller states in
W. No program is lost, but those box types ask more of their callers, and
the "typed in the empty world" statements become "typed in W".

Decision taken under the author's delegation: the constant world applies to
the lock-free relation only, as a restriction of its fragment. The core
relation keeps fresh extension. Whether to adopt it in the core, given the
three stronger box types, goes to the author.

### 10.5  Example verdicts

| Example | Verdict |
|---|---|
| Forwarder | in (R4′ admits the single hop), fuel 2 |
| SemRounds | lock free, out of the static fragment until G4 |
| CfstScheduler (the recursive scheduler) | in, round of 6 steps |
| MilnerSched.v | no recursion, lock free trivially |
| TailCall | in, needs Acc because of the ceiling ι[0] |
| KobForwarder, FactServer | out (guard, and Rank fails) |
| cfst/TreeSum | lock free, out by R1, in under R1′ |

## 11  Proposals from the literature session, and decisions (2026-11-08)

- **Drop fairness, prove Padovani's reachability form instead.** Rejected
  as a replacement. The author asked for the fair form, and stage 1 already
  proves `lf_criterion` for weakly fair runs, constructively. The
  reachability form (`lock_free_reach`, defined in Fair.v) can follow as a
  corollary, because the induction builds the schedule. Added to stage 3 as
  an optional corollary.
- **One waiter measure instead of fuel and rank.** Adopted for the paper
  only: "every wait has an ordinal variant that decreases with every action
  below the waiting point". The Rocq proof keeps fuel (local to the holder)
  and well-foundedness of W (§10), because a shared measure would need
  agreement between components at composition.
- **ℕ fuel against bounds that arrive late.** A holder that receives n and
  then runs n rounds before serving a waiter needs ordinal fuel. This is
  postponement justified by data, and it is a stated limitation, the same as
  termination on data. One constant N is enough for the fragment.
- **No select, no mixed choice.** Weak fairness suffices because an offer
  persists until it fires. That holds because the calculus has no select and
  no mixed choice. The paper states this, so that no claim about Go or Rust
  inherits it.
- **Further limitations, stated in the paper.** Internal computation that
  terminates because of data before serving a waiter (excluded by the guard).
  Servers that loop while the client says "more" (lock free only through the
  client's data). Divide and conquer such as parallel mergesort, which is
  semantically fine and statically excluded by R1.

## 12  Coverage of the literature (author's acceptance criterion, 2026-11-08)

The author accepts the design if it covers everything the standard
literature on lock freedom covers, statically and semantically. Stage 3c
checks this before any claim:

- **Static.** Every program that a lock-freedom type system in the store
  accepts must be typed by the static fragment, after translation to the
  calculus. Sources: padovani2014deadlock (the ⊢LF examples: stream, the
  node configurations of Example II.2/III.5, the growing ring III.7, the
  alternating bit protocol III.8), kobayashi2002type (no PDF yet, to be
  fetched), kobayashi2006new (Example (10) of padovani2014deadlock p9, typed
  by Kobayashi and not by Padovani), padovani2013lock, padovani2014typing.
  A program outside the fragment that one of them types is a gap. A gap
  either relaxes the fragment or, if the program is not lock free in our
  semantics, is shown not to be.
- **Semantic.** Every such program, and every lock-free program among the
  motivating examples (§8), must be in the lock-free relation. Programs
  outside the static fragment get a direct semantic proof (the controller,
  SemRounds after G4, TreeSum).
- **Expected tension.** R1 excludes non-tail recursion. Padovani's ⊢LF
  excludes the corresponding π-calculus patterns (fact, Fibonacci need
  negative priorities, p8). Kobayashi's obligation levels may accept more.
  Example (10) is the first case to check.
- What counts as a gap follows the rule for subsumption: only a program
  confirmed typable by them and not by us, after removing translation
  artefacts.

## 13  Stage 3c results: coverage (2026-11-08)

Analysis on paper of the lock-freedom systems in the store. The full table is
in the progress log. kobayashi2002type now has its PDF (author's copy).

**Covered.** Stream (session form), Padovani's nodes (L2(A,B), L2(B,A), and
Node A via a send loop and a receive loop per node), the alternating bit
protocol (III.8), Kobayashi's sum server and loop (Ex. 2.1, 2.5),
Padovani 2013's forwarder system (= Forwarder.v, Rocq `fw_lfptyped`),
PVV14's (2) and (4). Correctly rejected: L1(B), L2(B,B), PVV14 (3), the
infinite delegation (2), Kobayashi's recursive forwarder.

**Non-tail recursion.** R1 rejects no lock-free program of these papers.
Fact and Fibonacci are rejected by ⊢LF (padovani2014deadlock p10, "deadlock
free but not lock free") and by Kobayashi 2002 (p32). In our calculus a
non-tail call becomes a spawned call and a wait, which R1 accepts. Guard and
Rank reject it, matching Padovani's ban on negative priorities.

**Outside the calculus.** Kobayashi's objects with racing method servers
(Ex. 3.6, 3.7) and the dining philosophers with semaphores (Ex. 3.8, which
need strong fairness, kobayashi2002type p8). The two-server process on a
shared channel (p9 of padovani2014deadlock) needs nondeterministic choice of
server.

**One gap: the growing ring (padovani2014deadlock, Example III.7).** ⊢LF
types it and it is lock free in our semantics. Every translation fails the
guard or R2′. Concurrency within a round is needed, so some spawned thread
either recurses before the round's first primitive (guard) or hands a
received end back to recursion (R2′).

**Over-restrictions in the repo.** R2′ rejects ReceivedChain.v (a received
payload passed to recursion inside a spawn), and state passed through
unchanged.

**Decision (under delegation): adopt R2-recv with fed slots.** A received
payload counts as advanced when it is passed to a recursive call, but not
when it is linked. Every parameter slot that a received payload can reach
must be acted on before the round sends it on. The second clause is
necessary. Without it a server passes a received end into recursion and the
next round sends it back unacted, and the waiter starves. The relaxation
admits the ring, ReceivedChain, the literal Node A and fork-join in general.
It keeps rejecting C1 (Rank) and C3 (link clause). It changes only the
fragment check, not the relation or the guard. The alternative G′ (closures
built before the guard may hold the self if their own body is guarded)
would rework the LiveGuard proofs and is kept in reserve.

**To verify in Rocq (stage 3c, Rocq part):** the core types the spawn-ahead
ring, Rank holds for it, the fuel bound N = (d+1)·2L stays valid under
R2-recv (a received end is delayed by at most one round), and the ring,
ReceivedChain and the ABP pass the revised checks.

## 14  Stage 2b: the lock-free relation (2026-11-09)

Stage 2b stopped before any Rocq definition. The judgment of §10.3,
`⊨ p := ∃ N, ∀ n, LPrel N n p`, does not imply lock freedom for any layer
that reads the rank off the points of the live relation. The constant world
fixes W for every index. It does not fix where an entry sits in W. O-New
picks its point x and its session types inside each level (`∃ x s s'` in
`Ebody`), and O-Send, O-Spawn and O-Recv pick environment splits there too.
So a reachable state has one placement per index, and placements at
different indices need not agree.

### 14.1  Counterexample: C1 with a ceiling

Argued on paper, not mechanized. Take the spawner chain C1 of §10.1 in a well-founded world with a ceiling,
the shape of TailCall. W knows ι and ζ, with the facts ι+k ≺ ι[0] and
ζ+j ≺ ι+k for all j and k. W is well founded and ι[0] has height ω. Main
waits on c₀ at ι[0]. Round k creates c_k, spawns T_k, which blocks on c_k
while it holds the partner end of c_{k−1}, and takes one step with a
chatterbox at ζ+k.

At index n the relation places c_k at ι+(n−k) for k ≤ n. Every gate of
round k needs ι+(n−k) ≺ ι+(n−k+1), which program order gives, and the
first needs ι+(n−1) ≺ ι[0]. After n/2 rounds the index is spent and level 0
holds everything. So the process is in the relation at every index, with
the per-thread invariant of stage 1 at every state. Fuel 2 suffices. A
blocked thread takes no step, so the fuel of the end it holds never ticks,
and the recursive thread hands c_k on after one chatter step. W is well
founded. Yet main waits forever in every fair run.

A uniform placement turns the chain into an infinite descent in W, which
`well_founded (w_lt W)` excludes. So rank needs a placement that is the
same at every index and coherent along the run, and the plan has none. In
`lf_criterion` this is the stability clause of `rank_bound`
(`we (S k) t = we k t`), which nothing indexed can supply.

### 14.2  What is unaffected

Fuel is uniform. N is a constant, and the counters are functions of the
run, because ends are named by channels. Local progress, links_restricted
and the per-thread invariant are facts of one state, so one index n ≥ 1
supplies them at every reachable state (`live_reach`). no_tau_divergence
comes from `live_adequacy` as before.

### 14.3  Ways out, for the author

1. A placement oracle (U1 of §3.2, restricted to placement). The
   relation takes ω, which fixes the point and the types at O-New and the
   splits at O-Send and O-Spawn, and adequacy assumes
   `∃ N ω, ∀ n, LPrel N ω n p`. Composition combines the oracles of its
   components. The fundamental theorem reads ω off the typing derivation.
2. Uniform choices without an oracle. A coinductive invariant over
   configurations annotated with thread environments chooses each
   successor annotation once, outside the index, and asks the live
   relation at every index of each annotated state. Adequacy then needs
   no choice principle if `lf_criterion` takes rank and fuel as relations
   on positions rather than functions. The fundamental theorem must pick
   its witnesses independently of n, which amounts to option 1 with ω
   taken from typing.
3. Points in the syntax. `new@x` with a point expression in the term.
   Box instantiation would then substitute points into terms, which the
   calculus does not do today.
4. A depth bound instead of Rank. A second constant D bounds the length
   of every chain of waits at every reachable state. The bound is a fact
   of the configuration and needs no placement. The criterion then
   inducts on the vector of fuels along the chain, lexicographically,
   which is well founded because the length is at most D. The cost is
   that D does not compose by maximum, because a chain may cross between two
   components many times, and programs whose blocked chains grow without
   bound (possibly the growing ring) fall out.

We recommend option 1. It is the only one that keeps Rank as
`well_founded (w_lt W)` and keeps compositionality checkable, at the cost
of one parameter in the composition statements.

## 15  Stage 2b with the oracle (2026-11-09)

The relation is the live relation with an invariant layer. The layer
annotates every configuration that a run of p reaches, and the oracle ω
fixes that annotation once, for every index. Rocq in
theories/lockfree/LFRelation.v (definitions, monotonicity) and
theories/lockfree/LFAdequacy.v (adequacy).

### 15.1  Why a layer and not a constrained O-New

O-New sits inside the inductive `Eind` of the live relation. A layer
outside `Eind` cannot reach that existential, and a new parameter of
`Ebody` changes a statement of theories/liveness. The process relation
at Σ = ∅ also forgets the threads (stage 1, finding 1), so a constraint
there constrains nothing. The layer therefore makes the choices itself.
It annotates configurations, computes the annotation of every successor
from ω, and asks the live term relation of every thread at that
annotation, at every index.

### 15.2  The oracle

```
Record placement := Placement {
  pl_pt : point; pl_s : sty; pl_s' : sty;   (* new: c ↦ Both (pl_s, pl_pt) (pl_s', pt_dual pl_pt) *)
  pl_give : tenv }.                          (* spawn, send: the entries handed over *)
Record oracle := Oracle {
  or_init : config → nat → tenv;             (* environments of the starting threads *)
  or_pick : tenv → expr → placement }.       (* read at the thread's Θ and term *)
```

`or_pick` reads the environment and the term before the step, so it
never sees the fresh name. The splits are a real choice. A thread that
holds both ends of c and hands c to a spawned thread or a payload while
its continuation keeps c chooses which end goes. For Close/Close the two
ends differ only in their point, x or x̄, and the gates read that point.
Entries that the term does not mention can also go either way. So ω
gives the handed-over entries (`pl_give`). Every other choice of the
live relation is forced. The entry after an action is `snd_next`,
`rcv_next`, `sel_next b` or `bra_next b` of the entry before it, a
received entry keeps the sender's entry, and a link only renames.
Worlds have no aliases on this branch (`w_eq` is equality), so points
are exact.

### 15.3  Annotations and their update

```
Record aconf := AConf { ac_q : config; ac_env : nat → tenv; ac_fuel : nat → chan → nat }.
Definition aupd (ω : oracle) (N : nat) (a : aconf) (L : gset nat) (q' : config) : aconf.
Definition astep ω N a a' := ∃ L q', istep (ac_q a) L q' ∧ a' = aupd ω N a L q'.
Definition areach ω N := rtc (astep ω N).
Definition ainit ω N q := AConf q (or_init ω q) (λ _ _, N).
```

`aupd` reads the step off L, the two configurations and the redexes.

| Step of thread i (and j) | Environments | Counters |
|---|---|---|
| β | unchanged | unchanged |
| new c | c ↦ Both (pl_s, pl_pt) (pl_s', pt_dual pl_pt) at i | c of i set to N |
| spawn j | i keeps Θ minus pl_give, j gets pl_give | j gets i's counter − 1 |
| link r o (r removed) | i drops r and o, every other thread renames r to o | the peers of r and o get min(own, min(i's r, i's o) − 1) on o |
| message c, i to j | i: payload removed, c by snd_next. j: c by rcv_next, payload added | c set to N on both, every other counter − 1, j's received entries get i's counter − 1 |
| close c | c removed on both | c set to N on both, others − 1 |
| choice b on c | sel_next b and bra_next b | c set to N on both, others − 1 |

Threads outside L keep their environment and counters, up to the
renaming of a link and its counter transfer. The environments never
read the counters.

### 15.4  The invariant and the relation

```
Definition LFErel n W (Θ : tenv) (φ : chan → nat) (e : expr) : Prop :=
  (∃ U, LErel n W Θ U ∅ e) ∧ dom Θ = fchans e ∧ (irred e → Θ = ∅) ∧
  (∀ c, c ∈ dom Θ → φ c = 0 →
     ∃ a S, act e = Some a ∧ ¬ is_admin a ∧ asubjs a = Some S ∧ c ∈ S).

Definition LFconf n W Σ a : Prop :=
  (∀ t e, M !! t = Some e → LFErel n W (A t) (Φ t) e) ∧
  (∀ t e, M !! t = Some e → fchans e ⊆ C ∪ dom Σ) ∧
  (∀ t e k ek, M !! t = Some e → tenv_entry (A t) k = Some ek → k.1 ∉ dom Σ →
     ∃ s es k' ek', M !! s = Some es ∧ tenv_entry (A s) k' = Some ek' ∧ k'.1 = k.1 ∧
       (s, k') ≠ (t, k) ∧ ek'.2 = pt_dual ek.2 ∧ sdual ek.1 ek'.1) ∧
  (no channel has three entries)
  where (C, M) = ac_q a, A = ac_env a, Φ = ac_fuel a.

Definition LFPrel (N : nat) (ω : oracle) (n : nat) W Σ T p : Prop :=
  LPrel n W Σ T p ∧
  ∀ q a, erase q = p → areach ω N (ainit ω N q) a → LFconf n W Σ a.
```

The index n enters only through `LPrel n` and the `LErel n` of each
thread. The annotation of a reachable configuration is the same for
every n. Fuel is one constant N, and the judgment hides it as
`∃ N ω, ∀ n, LFPrel N ω n W ∅ T p`. Rank is the premise
`well_founded (w_lt W)`, with no number. Fuel is per thread and channel,
not per point.

### 15.5  Statements

```
Theorem LFPrel_down N ω n m W Σ T p : m ≤ n → LFPrel N ω n W Σ T p → LFPrel N ω m W Σ T p.
Theorem LFPrel_fuel N N' ω n W Σ T p : N ≤ N' → LFPrel N ω n W Σ T p → LFPrel N' ω n W Σ T p.

Theorem lf_adequacy N ω W T p :
  world_wf W → well_founded (w_lt W) → (∀ n, LFPrel N ω n W ∅ T p) → lock_free p.
Corollary lf_adequacy_ex W T p :
  world_wf W → well_founded (w_lt W) → (∃ N ω, ∀ n, LFPrel N ω n W ∅ T p) → lock_free p.
Corollary lf_thread_progress W T p :
  world_wf W → well_founded (w_lt W) → (∃ N ω, ∀ n, LFPrel N ω n W ∅ T p) →
  ∀ r l, erase (r 0) = p → maximal r l → wfair r l → thread_progress_run r l.
```

`lf_criterion` changes its hypotheses, not its conclusion. Local
progress is asked at the positions of runs only. Uniqueness, persistence,
fuel, stability and the rank clause are asked only of threads whose
redex is a session action other than a link (`npend`). A pending link
is administrative and enabled under `links_restricted`, so the proof
fires it by weak fairness, as it already did for the other
administrative redexes. `local_progress_ready` asks readiness only of
threads that can step, asks that a thread holding an entry can step,
and lets two meeting offers enable either thread, because a meeting
partner may sit at a link.

The adequacy proof instantiates the criterion as follows.
- `fu k t` is the counter of the partner entry of t's channel at the
  annotation of position k. A step of the holder on another channel
  ticks it. Handing the entry on by a send, a spawn or a link passes at
  most the counter minus one. An administrative step of the holder
  that keeps the entry keeps the holder and the counter.
- `we k t` is the point of the entry that t offers, and R is `w_lt W`.
  A thread that does not step keeps its entry, up to renaming. The gate
  of the holder s, read from `LErel 1` at s's environment, puts the point
  of s's offer below the dual of s's entry of t's channel, which pairing
  makes t's point.
- local progress and `links_restricted` are facts of one annotated
  configuration, and `no_tau_divergence` comes from `live_adequacy`.

### 15.6  C1 with a ceiling is rejected

Take any N and ω with `∀ n, LFPrel N ω n W ∅ T p` for the program of
14.1, and the fair run in which every round fires. The annotation of
this run is one sequence, computed by `aupd` from ω, the same at every
index. At the position where T_k blocks, `LFconf 1` gives T_k's gate.
T_k offers its end of c_k at y_k and holds the partner end of c_{k−1},
which pairing puts at pt_dual y_{k−1}. The gate gives y_k ≺ y_{k−1}. A
blocked thread keeps its entries, so the points y_k do not move. The run
yields y_0 ≻ y_1 ≻ y_2 ≻ … in W, against `well_founded (w_lt W)`. In
14.1 the index-n relation placed c_k at ι+(n−k), a different placement
for each n. Here n only sets how deep `LErel` is read at a fixed
annotated configuration. The same follows from `lf_adequacy`, because
C1 is not lock free. No Rocq lemma states it, because C1 as a closed
program with a ceiling world and a fair starving run is not built.

### 15.7  What stage 3 has to supply

The layer is a property of closed runs. It does not compose over a cut,
because the runs of a composite interleave interactions across the cut
that neither component's internal runs contain. Stage 3 therefore proves
the layer from typing by preservation along annotated steps, not by
semantic composition. The statements it needs are these, with `LFtyped`
the typed form of `LFconf` (every thread typed in the guarded static
system at its annotated environment, ω's picks equal to the points and
splits of those typings, pairing, at most two entries per channel, and
counters at least the remaining fragment budget).

```
lf_init      : lfptyped W ∅ p T → ∃ N ω, ∀ q, erase q = p → LFtyped N ω W (ainit ω N q).
lf_preserve  : LFtyped N ω W a → astep ω N a a' → LFtyped N ω W a'.
lf_typed_rel : LFtyped N ω W a → ∀ n, LFconf n W ∅ a.
lf_live      : lfptyped W ∅ p T → ∀ n, LPrel n W ∅ T p.        (live_soundness)
```

Two risks for stage 3. First, `or_pick` is a function in Type, and the
point of a `new` lives in a Prop typing derivation and not in the term,
because box instantiation substitutes points into types only. A function
of (Θ, e) defined on all reachable states needs countable choice over
those derivations, unless the picks are computable from the term. Points
in the syntax (14.3, option 3) make them computable. The relational form
(14.3, option 2) avoids the function: replace `aupd` by any successor in
an invariant set, and run the criterion over finite annotated prefixes.
Second, two threads with Θ = ∅ and the same term receive the same picks.
Such a thread starts an independent subsystem, so one pick should serve
both, but this uniformization is unproved.

A semantic composition of the layer would need runs with external
actions, so that each component's layer covers the interactions across
the cut. Its P-Connect statement would combine the oracles by the side
that holds the thread, which needs `or_pick` to see more than (Θ, e).

## 16  Syntactic points (design, 2026-11-09)

The author replaced the oracle of §15 by syntactic points (453a4c2). This
section is the design. It changes no Rocq file. The program names the point
of every `new`, and the two ends of a channel carry different names. Then
every point the live relation places is a function of the run, the same at
every index, and the closed-run layer of §15 goes away for placement and
rank. Lock freedom becomes a judgment over thread soups that composes like
the live relation, plus one clause on fuel. Fuel is the one part that stays a
property of closed runs (16.5). Section 16.8 sketches how to close that gap.

### 16.1  Choices inside a level

Rank reads the point of the end that a pending thread offers and the gate of
the holder of the partner end (`rank_bound`, 15.5). Fuel reads counters
along the run. A choice inside a level matters for lock freedom exactly when
it can move the point of some entry, or the holder of some end, between two
indices or between a state and its successor. The table lists every
existential of `Ebody`, `LEobl`, `LElink`, `Vspawn`, `LVdef` and `Pbody`
(theories/liveness/LiveRelation.v). `Eobl` and `Vdef` of the base relation
(theories/relation/LogicalRelation.v) have the same ones. Deadlock freedom
never needed a uniform placement, so the base relation changes only because
the syntax does.

| Choice | Clause | Matters | Fixed by |
|---|---|---|---|
| point x of the channel | O-New, `∃ x s s'` | yes, it is C1 with a ceiling (14.1) | the term names x and the label `LNew c x` carries it |
| session types s, s′ | O-New | no | stays an existential per index. Gates and rank read points and the end named by the label, and a wrong type at that end fails the obligation of the next action |
| which end of c goes to the closure | O-Spawn, `∃ Θ1 Θ2` | yes, when the thread holds both ends of c | end names. `Vspawn` asks `fends eb = tenv_ends Θ1`, so Θ1 holds exactly the ends the closure mentions |
| bounds ub, lb of the closure | O-Spawn | no | they only constrain. The soup starts a spawned thread with F = ∅ |
| which entries travel with the payload | O-Send, `tenv_comp (w_eq W) Θr Θ1 Θ2` | yes, Chan c with both ends held, and the Close/Close case of §15.2 | end names. V at the payload type forces `tenv_ends Θ2 = fends w` |
| m, U, s, k, Θ′ of O-Send | O-Send | no | forced by `tenv_hd` once the label names the end |
| received entries | O-Recv | no | universal. A received entry keeps the sender's point, because `payload_at` reads only fields and `payload_pts_dual` holds |
| the entry acted on | O-Close, O-Select, O-Branch, `selects` | yes, `selects` picks the first Close entry by side | the end bit of the label |
| the two linked entries | O-Link, `LElink` | no once the label names ends | the peer of the removed end is renamed and keeps its point (16.5) |
| split of a pair | `LVdef` at `TProd` | yes, `Pair (Chan c) (Chan c)` right after new | end names. V at `TSess s x` asks `pt_pol kk = b` |
| witnesses xs | `LVdef` at `TEx` | no | entry points come from Θ, xs only instantiate the type |
| the constant | `LVdef` and `Vspawn`, `∃ kc T0` | no | holds no channel |
| side bits of a `Both` | `below_rest`, `above_offered` | no | both quantify over all keys. With `selects` reading the end bit, the offered entries are fixed by points |
| future worlds | `Ebody` `∀ W1`, O-Recv `∀ W' j` | no | universal |
| successors | Q-Admin, `Psend_case`, `Plink_case`, `recv_back` | no | process level. The lock-free judgment reads threads and uses `LPrel` only for `no_tau_divergence` |
| fuel counters | none | no | a function of the run and N |

### 16.2  The syntax

**Option (a), point expressions in terms.** A term embeds a `point` at `new`
and at force. Its point variables are bound by the enclosing boxes, force
carries the instance list, and the force step substitutes it (a new
traversal `pinst_expr` beside `subst`). Three costs follow. Every force site
writes its instance, and boxes or force occur on 453 lines in 83 files.
E-Open places the opened variables at 0 by `pshift m`, so a term point under
an opened existential refers to a different variable in the premise of
`t_open`, and the premise must type a shifted term. An opened existential
has no runtime witness, so `new@ι` at an opened ι leaves a free point
variable at runtime. An atom pt(a) for the current point of a held end,
resolved through Θ, repairs the last cost but mentions a linear variable
without consuming it.

**Option (b), points as values.** A point value `EPt x` has the singleton type
`TPt x`. `new` takes its point as its argument, `App ENew v` with
`v : TPt x`. Two constants compute points, `KPay i` for x[i] and `KSucc` for
x + 1. A literal is ground (no `NVar` in it), so every point substitution
fixes it and E-Exp, E-Open and `PointSubst.v` stay as they are. A box whose
body creates a channel at a box variable ι takes a parameter of type
`TPt ι`, and value substitution instantiates it. Boxes, force and
existentials stay Curry style. The relation forces the runtime point to
equal the typing instance, because V at `TPt x` asks `v = EPt x`. The costs
are one type, one value, two constants, a parameter on the four boxes that
create channels (FactoryEx, FreshBetween, FreshMany, GuardCex), and a
`TPt ι` in the package of any existential that is opened to create a channel
at ι. SegmentInterleave is the only known case, and it left the build under
sharp edge 172.

We choose (b). It touches the sites that create channels and nothing else,
and it keeps box instantiation in typing.

**No session types on `new`.** O-New keeps `∃ s s'`. The gates and the rank
never read a session type, the end an action uses comes from the label, and
`selects` checks the type only to reject an ill-typed action, which the next
obligation rejects anyway.

**Ends.** A channel value carries its end, `Chan c b`, where b is the
polarity of the end's current point. The two ends of a channel sit at x and
x̄, which differ exactly in `pt_pol`, so the bit names the end and the
environment needs no new key. `tenv` stays `gmap chan ends`, and the end of
an entry e at c is `(c, pt_pol e.2)`. The bit moves with the point. `new`
at x returns `Pair (Chan c (pt_pol x)) (Chan c (negb (pt_pol x)))`. Send and
receive keep it, because `pt_shift` keeps polarity. Select returns
`Chan c false` and branch returns `Chan c true`, because `sel_pt` is negative
and `bra_pt` is positive. A link renames `Chan c β` to `Chan d β` and keeps
the bit, which is correct because `w_eq W kc (pt_dual kd)` makes the bits of
the two linked ends differ. The alternative, an annotation on spawn and send
naming the ends handed on, needs a set of ends per step for nested values and
closures, and it leaves the split of `Pair (Chan c) (Chan c)` free. We reject
it.

**Top-level channels.** A ground literal cannot name a point variable of the
hypotheses Ψ. `created` therefore introduces a fresh constant per top-level
channel instead of a variable, `created_snoc` appends
`(bcs_inst (plist [pconst a]) C, [pconst a])` for an a outside `w_names W`
and the earlier constants, and nothing shifts. A top-level `new` writes
`EPt (pconst a)`. `soundness_created` keeps its statement, and its world
places a by `wext_cc` at that very name.

### 16.3  Rule changes

Syntax and steps (theories/lang).

```
Inductive konst := … | KPay (i : nat) | KSucc.
Inductive expr := … | Chan (c : chan) (b : bool) | EPt (x : point).   (* is_val (EPt x) *)
Notation cend := (chan * bool).
Fixpoint fends (e : expr) : gset cend.                 (* fchans e = set_map fst (fends e) *)
Definition let_new_at (v e : expr) : expr :=
  LetP (Pair (App ENew v) EUnit) (LetU (Var 0) (LetP (Var 1) e)).

Inductive slabel :=                                     (* every subject is an end *)
  | SRecv (c : cend) (v : expr) | SSend (c : cend) (v : expr) | SClos (c : cend)
  | SLink (cd : gset cend) | SSel (c : cend) (b : bool) | SBra (c : cend) (b : bool).
Inductive tlabel := LBeta | LSess (σ : slabel) | LNew (c : chan) (x : point) | LSpawn (v : expr).

| HeadNew c x  : head_step (App ENew (EPt x)) (LNew c x)
                   (Pair (Chan c (pt_pol x)) (Chan c (negb (pt_pol x))))
| HeadPay i x  : head_step (App (Konst (KPay i)) (EPt x)) LBeta (EPt (pt_payload x i))
| HeadSucc x   : head_step (App (Konst KSucc) (EPt x)) LBeta (EPt (pt_shift 1 x))
| HeadSel1 c b : head_step (App ESel1 (Chan c b)) (LSess (SSel (c, b) false)) (Chan c false)
| HeadBra c b i : head_step (App EBra (Chan c b)) (LSess (SBra (c, b) i)) (inj_of i (Chan c true))
```

Send, receive, close and link carry `(c, b)` in their labels the same way.
In `proc_step`, P-Act-Msg, P-Act-Close and P-Act-Choice pair an action on
`(c, b)` with one on `(c, negb b)`. P-Act-Link keeps `echsubst c d`, which
keeps bits. `subjs` and `sentc` return channel names, so `C : gset chan` and
the freshness side conditions of P-Act-New stay. `eswap`, `chsubst` and
`fchans` keep their meaning.

Types and typing (theories/types, theories/static).

```
Inductive ty := … | TPt (x : point).          (* unlimited, heads ∅, tsize 1 *)

| KTNewAt S x : pk x → konst_ty peq plt pk KNew
    (TLolli None None (TPt x) (TProd (TSess S x) (TSess (dual S) (pt_dual x))))
| KTPay i x : pk (pt_payload x i) → konst_ty peq plt pk (KPay i)
    (TLolli None None (TPt x) (TPt (pt_payload x i)))
| KTSucc x : pk (pt_shift 1 x) → konst_ty peq plt pk KSucc
    (TLolli None None (TPt x) (TPt (pt_shift 1 x)))

| t_pt Φ Ψ Δ F x :                             (* E-Pt *)
    lenv_empty Δ → pt_ground x → skn W Ψ x → typed W Φ Ψ ∅ Δ F (EPt x) (TPt x)
| t_ch Φ Ψ Δ F c b s k s' y :                  (* E-Ch, one premise more *)
    lenv_empty Δ → seq s s' → seqs W Ψ k y → pt_pol k = b →
    typed W Φ Ψ {[c := One (s, k)]} Δ F (Chan c b) (TSess s' y)
```

E-Force (`typed_force`, `KTForce`) is unchanged. `pinst_ty`, `sren_ty`,
`sflip_ty`, `sinst_ty`, `heads`, `hbot`, `tsize`, `unlimited` and `steq` get
a `TPt` case. `created` changes as in 16.2.

Base relation (theories/relation/LogicalRelation.v, Readiness.v).

```
Vdef at TSess s x : ∃ c b s0 kk, v = Chan c b ∧ Θ = {[c := One (s0, kk)]} ∧ seq s0 s ∧
                      w_eq W kk x ∧ pt_pol kk = b
Vdef at TPt x     : Θ = ∅ ∧ v = EPt x ∧ pt_known W x
Vdef at TLolli    : fends eb = tenv_ends Θ   (was fchans eb = dom Θ)
O-New             : c ∉ dom Θ → pt_known W x ∧
                      ∃ s s', sdual s s' ∧ at_cost … W (<[c := Both (s, x) (s', pt_dual x)]> Θ) T F e'
O-σ               : tenv_hd_end Θ (c, b) u k Θ1 := tenv_hd Θ c u k Θ1 ∧ pt_pol k = b
O-Link            : cd = {[(c, bc); (d, bd)]} with pt_pol kc = bc and pt_pol kd = bd
selects Θ σ k     : the entry at k has pt_pol = the bit of σ's end, the type check stays
```

`tenv_ends Θ` is the set of `(c, pt_pol e.2)` over the entries e of Θ.

Live relation (theories/liveness/LiveRelation.v). The same changes to
`LVdef`, `LEobl`, `LElink` and O-New, `Vspawn` asks
`fends eb = tenv_ends Θ`, and `Ebody` gains one clause.

```
Definition tenv_fit (Θ : tenv) (e : expr) : Prop :=
  tenv_ends Θ = fends e ∧ ∀ c e1 e2, Θ !! c = Some (Both e1 e2) → pt_pol e1.2 ≠ pt_pol e2.2.

Definition Ebody … : Prop :=
  tenv_fit Θ e ∧                                                    (* E-Fit *)
  ∀ W1, wext_r W W1 → … (E-Stop, E-Step, O-Beta, O-New as above, O-Spawn, O-σ, O-Link).
```

E-Fit makes the holder of an end the unique thread whose term mentions it.
`Huniq` and local progress read holders off terms (`waits`, Fair.v), and a
dead mention of a handed-on end would give a second holder. An untyped
term can mention one end both in a spawned closure and in its continuation.
`Vspawn` gives the end to the closure, and the continuation keeps a mention
that no index observes when it is dead code. So the clause has to sit in the
relation and not in the soup.

The lock-free judgment (theories/lockfree, new file LFSoup.v).

```
(* a closed or open soup of threads, each in the live relation *)
Definition soup_ok W (Σ : senv) (T : ty) (π : gmap cend point) (C : gset chan)
    (ts : list (expr * tenv * ty)) : Prop :=
  (one entry has type T, every other entry has TUnit) ∧
  (the environments are disjoint per end, and together they hold both ends of
   every c ∈ C and the one end of every c ∈ dom Σ, at Σ's entry) ∧
  (every entry of end o has point π !! o) ∧
  (the two ends of every c ∈ C have dual session types).

Definition LFsoup (n : nat) W Σ T (π : gmap cend point) (p : proc) : Prop :=
  ∃ ts, p.2 = list_to_set_disj ((λ t, t.1.1) <$> ts) ∧ soup_ok W Σ T π p.1 ts ∧
        Forall (λ '(e, Θ, U), LErel n W Θ U ∅ e) ts.

Definition LFP W Σ T (p : proc) : Prop :=
  (∀ n, LPrel n W Σ T p) ∧ ∃ π, ∀ n, LFsoup n W Σ T π p.

(* counters along a run, ticking only while the partner end is offered (§7) *)
Fixpoint cnt (N : nat) (r : nat → config) (l : nat → gset nat) (k : nat) : cend → nat.
Definition fuel_ok (q : config) (φ : cend → nat) : Prop :=
  ∀ s es o, q.2 !! s = Some es → o ∈ fends es → offered_end q (cdual o) → φ o = 0 →
    ∃ a, act es = Some a ∧ ¬ is_admin a ∧ aend a = Some o.
Definition fuel_run (N : nat) (p : proc) : Prop :=
  ∀ r l k, erase (r 0) = p → (∀ j, j < k → istep (r j) (l j) (r (S j))) →
    fuel_ok (r k) (cnt N r l k).
(* cdual (c, b) = (c, negb b). offered_end q o: some thread's redex is a session
   action on o other than a link. aend a: the end that action a acts on. *)
```

`cnt` sets an end to N while its partner is not offered and when the holder
acts on it. While the partner is offered it drops by one at every
non-administrative step of the holder on another end and at every hand-over
by send or spawn. A link moves counters as in the table of 15.3. π fixes the
points of the ends present at the start, once, outside the index. Session
types stay inside the index.

Algorithmic checker (theories/algorithmic). `ALetNew S x e` erases to
`let_new_at (EPt x) (erase e)` and its check asks `pt_ground x` beside
`AKnown x`. The guard and the fragment (Guard.v, Fragment.v) treat `EPt`,
`KPay` and `KSucc` as values and β constants that pay for nothing, and R2′
counts a point value as fresh.

### 16.4  Files, sizes, and statements that change

| Group | Change | Size (changed lines) |
|---|---|---|
| lang (Syntax, Semantics, ChannelSwap, Harmony, Safety, ThreadSim, 2.7k lines) | `Chan c b`, `EPt`, `KPay`, `KSucc`, labels on ends, `HeadNew`, `fends`, `let_new_at`, swaps keep bits | 400 to 600 |
| types (Types, SessionEquiv, LinearEnv) | `TPt` in every fixpoint, three `konst_ty` cases, `tenv_ends`, `tenv_fit` | 150 to 250 |
| static (Typing, PointSubst, FactTheory, Source, SourceRules, Mixed, Fundamental) | `t_pt`, `t_ch`, `created` over constants, `soundness_created` | 300 to 500 |
| relation and rules (LogicalRelation, Readiness, Worlds, BranchWorlds, rules/) | V clauses, O-New, `tenv_hd_end`, `selects`, link clause | 400 to 600 |
| invariance (7.1k lines) | renaming and junk renaming keep bits, labels on ends | 300 to 500 |
| composition (ConnectCut, ConnectSteps, Internalize, PConnect, PConnectN, PTerm, ReadyChain) | labels on ends, cut ends paired by bit | 300 to 500 |
| liveness (12k lines) | as the base relation, plus E-Fit in every construction of `Eind` (LiveTermRules, LiveBind, LiveConsts, LiveUnfold, LiveConv, LiveEconv, LiveGuardRules, LivePTerm, LiveInternalize, LiveJunk, LiveRenaming) | 1000 to 1500, the largest and riskiest group |
| lockfree (5.1k lines) | `waits` by ends, labels in Instr, Reach, TauThread, LocalProgress. LFRelation.v deleted, LFSoup.v new, LFAdequacy.v rewritten | about 1700 deleted, 1200 new or adapted |
| examples (about 70 files with `new`) | a literal at each top-level `new`, `created` over constants, a point parameter in four boxes | 600 to 900 |
| algorithmic | erasure of `ALetNew`, ground check | 50 |
| pgv, pn, mp (in the build) | see 16.7 | out of the build until revisited |

Statements the author approved that change in form.

1. The calculus. `Chan c b`, `EPt x`, `KPay i`, `KSucc`, the labels name ends,
   `LNew c x`, `HeadNew c x`, and P-Act-Msg, P-Act-Close and P-Act-Choice
   pair dual ends. Terms are Curry style except that `new` names its point.
2. `KTNewAt` takes `TPt x` instead of `TUnit`. `typed` gains `t_pt`, and
   `t_ch` gains `pt_pol k = b`.
3. `created` introduces constants. `soundness_created`, `soundness` and
   `soundness_source` keep their statements. Example typing lemmas keep the
   form `styped ∅ X_Ψ …` with X_Ψ over constants, and their deadlock freedom
   theorems keep their form over the changed terms.
4. `LVrel`, `LErel` and `LPrel` change by definition (E-Fit, O-New, V at
   `TSess` and `TPt`, `fends` in the arrow and `Vspawn`). `live_adequacy`,
   `live_fundamental_guarded`, `live_soundness`, `LPrel_connect`,
   `LPrel_join` and `LPrel_term` keep their statements.
5. `waits` (Fair.v) reads ends. `lock_free`, `local_progress` and
   `lf_criterion` keep their statements.
6. `lf_adequacy`, `lf_adequacy_ex` and `lf_thread_progress` replace the
   hypothesis `∃ N ω, ∀ n, LFPrel N ω n W ∅ T p` by
   `LFP W ∅ T p ∧ ∃ N, fuel_run N p`. `LFPrel_down` and `LFPrel_fuel` become
   `LFsoup_down` and `fuel_run_mono`. The statements of 15.7 give way to
   `lf_fundamental` (16.6).
7. New. `LFP_term`, `LFP_connect` and `LFP_join` with the hypotheses of
   `LPrel_term`, `LPrel_connect` and `LPrel_join`.

### 16.5  Placement, rank and composition without a run layer

**Points are a function of the run.** Let `pupd π q L q'` update a point map
along one step. New sets `(c, pt_pol x)` to x and the other end to x̄, read
off the label. A message shifts both ends by one. A choice moves the
selecting end to `(c, false)` at `sel_pt k i` and the branching end to
`(c, true)` at `bra_pt k i`. Close removes both ends. A link on
`(c, b)` and `(d, negb b)` removes them and moves the point of `(c, negb b)`
to `(d, negb b)`. That point was x̄_c = x_d before, so the peer keeps its
point. β, spawn and the transfer of a payload change nothing. The key lemma
is preservation of the soup.

```
Lemma lfsoup_step n W T π q L q' :
  world_wf W → LFsoup (S (S n)) W ∅ T π (erase q) → istep q L q' →
  LFsoup n W ∅ T (pupd π q L q') (erase q').
```

Each case reads the clause of the stepping thread at its environment, and
every environment of the successor is forced. O-New names x. In O-Spawn,
`Vspawn` fixes Θ1 to the ends of the closure and E-Fit leaves the rest to
the continuation, and the child is `Etop` at level n with Θ′ = ∅. In a
message, V at the payload type fixes the travelling entries. The receiver
chooses nothing, and its `∀ W' j Θ2` takes W′ = W (`wext_refl`), j = pred n,
and the sender's Θ2, which has the right type because `payload_at m U k`
equals `payload_at m U (pt_dual k)` and the paired types are dual. Close,
select and branch take the entry the label names. A link renames the peer
by `LiveRenaming.v` and keeps its point. Threads that do not step keep their
relation, and `LErel_down` brings everything to the index of the slowest
thread. Session types are chosen again at each index, which nothing reads.

**One placement for every index.** Fix a run r with `erase (r 0) = p` and
`LFP W ∅ T p`, and take the π of the judgment. Let π₀ = π and
π_{k+1} = `pupd` π_k (r k) (l k) (r (S k)). π_k does not depend on n, and
induction on k with `lfsoup_step` gives `∀ n, LFsoup n W ∅ T π_k (erase (r k))`.
So at every position each thread sits in the live relation at every index,
at an environment whose points are π_k. This is what §14 found missing.

**The criterion applies.** `lf_criterion` is instantiated as in 15.5 with
the annotation replaced by π_k and `cnt`.
- `we k t` is π_k of the end that t offers, and R is `w_lt W`, well founded
  by hypothesis. A thread that does not step keeps its end, and π_{k+1}
  agrees with π_k on it up to the renaming of a link, so `Hstab` holds.
- `Hrank`. Let s hold the partner ō of t's end o, with s pending. If s
  offers ō, then t is enabled. Otherwise s is stable, and `ready_t` from
  `LFsoup 1` at s gives `below_rest`. The entry s offers lies below
  `pt_dual (π_k ō) = π_k o`, so `w_lt W (we k s) (we k t)`.
- `Huniq` and `Hpers` follow from E-Fit and disjointness of the soup.
  Local progress and `links_restricted` are facts of one soup at index 1,
  as in LocalProgress.v. `no_tau_divergence` comes from `live_adequacy`
  through the first conjunct of `LFP`.
- `fu k t` is `cnt N r l k` at the partner of t's end, and `fuel_run N p`
  gives `Hfuel`. While t is pending its partner end is offered, so the
  counter ticks at every step of the holder on another end and at every
  hand-over, and `fuel_ok` stops it at 0.

So `lf_adequacy` needs no closed-run layer for placement or rank, no oracle,
and no choice principle. π is a finite map in a Prop existential and `pupd`
is a function.

**Composition.** `LFP_term` takes `lsem_typed W (tenv_of Σ ∪ ΘB) [] ∅ t T`,
as `LPrel_term` does, with π the points of `tenv_of Σ ∪ ΘB`. E-Fit for t
holds because Θ is fixed outside n. `LFP_connect` and `LFP_join` concatenate
the two soups and join the two point maps. The cut ends are paired by the
side condition of P-Connect, and `LErel` moves to `wjoin W1 W2` by
`wext_join_l'` and `wext_join_r'`. The `LPrel` conjuncts compose by the
existing theorems. All three keep the form of `ptyped`'s rules. The soup is
flat, so a cyclic topology that arises at runtime needs no tree structure,
and the order of W carries the argument as before.

**C1 with a ceiling is rejected.** Round k creates c_k with
`new (EPt y_k)`, where y_k is the value the round computed, for example by
`KPay 0` from the round's parameter. The ceiling placement ι+(n−k) of 14.1
would need a point that depends on n, which no term can write. When T_k
blocks, it offers its end of c_k at y_k and holds the partner end of
c_{k−1} at ȳ_{k−1}. Its gate at index 1 gives y_k ≺ y_{k−1}, and every
such position lies on the fair run where every round fires. So any W in
which the gates hold has the chain y_0 ≻ y_1 ≻ … and is not well founded.

**The controller is accepted by the closed judgment.** The soup holds by
the guarded core typing, which §7 implies when it names R2 as the rule that
rejects the controller.
`fuel_run` holds for every N ≥ 1 by a direct proof. Nobody ever offers on ctl or
ctl′, so their counters stay at N, and every end of r is acted on in each
round. This replaces the process-level semantic proof that §7 asked for.
The conservative fuel of 15.4 is gone, because `cnt` ticks only while the
partner is offered.

**What remains is fuel.** `fuel_run` quantifies over runs of the closed
program, so it does not compose over a cut. It cannot move into the term
relation as it stands. The receiver of an end gets its counter from the
sender, and O-Recv is universal over what the environment sends. A
receiver that must cope with every counter must act on a received end
before any other channel step, because the counter may be 0. That rejects
the Forwarder, which receives an end and sends it on, and any fixed lower
bound on received counters fails the same way one hop later. A bound that
works must decrease along a chain of forwards, so it needs information that
sender and receiver share. Unlike the layer of §15, `fuel_run` involves no
choice and no index. It is a property of the untyped runs of p, close to
the `fuel_bound` hypothesis of the criterion, and the fragment proves it
from typing by preservation of a budget (16.6). 16.8 gives the way to make
it compositional.

**Risks.** E-Fit has to be proved wherever an `Eind` is built. In LiveBind
the evaluation context's ends are known from the continuation only at
inhabited value types. If that fails, the bind lemma takes `fends K` as a
hypothesis, which typing supplies, or `waits` moves to holders read off the
soup's environments, which changes the hypotheses of `lf_criterion`.

### 16.6  Stages

Each stage is one agent. At most two run at once, P3a beside P3b.

- **P1, lang and types.** `Chan c b`, `EPt`, `KPay`, `KSucc`, labels on
  ends, `HeadNew c x`, `fends`, `let_new_at`, `TPt`, `konst_ty`,
  `tenv_ends`, `tenv_fit`. Builds through theories/types.
- **P2, static, base relation, rules, invariance.** `t_pt`, `t_ch`,
  `created` over constants, `soundness_created`, the V clauses, O-New,
  `tenv_hd_end`, `selects`. Builds through theories/invariance and
  theories/static.
- **P3a, composition and liveness.** Labels on ends, E-Fit, `fends` in
  `Vspawn` and the arrow. `live_adequacy`, `live_fundamental_guarded`,
  `LPrel_connect`, `LPrel_term` rebuilt with unchanged statements.
- **P3b, examples and algorithmic, beside P3a.** Literals at top-level
  `new`, `created` over constants, point parameters in FactoryEx,
  FreshBetween, FreshMany and GuardCex, erasure of `ALetNew`. The live
  example theorems wait for P3a.
- **P4, lock-free relation.** `waits` by ends, labels in Instr, Reach,
  TauThread and LocalProgress. LFSoup.v with `LFsoup`, `LFP`, `pupd`, `cnt`,
  `fuel_run`, `LFsoup_down`, `fuel_run_mono`, `LFP_term`, `LFP_connect`,
  `LFP_join`. LFAdequacy.v rewritten around `lfsoup_step`.
- **P5, fundamental theorem.** Fragment.v traversals, and
  `lf_fundamental : lfptyped W ∅ p T → LFP W ∅ T p ∧ ∃ N, fuel_run N p`.
  The soup comes from `live_fundamental_guarded` and a lemma
  `typed_fit` (a closed typed term fits its environment). `fuel_run` comes
  from preservation along runs of a typed invariant whose counters are at
  least the remaining budget, with N = (d+1)·2L computed from the text. This
  is the stage 3 of 15.7 without the oracle. The controller (16.5) and C1
  as Rocq lemmas are optional here.
- **P6, optional, for the author.** Budgets in the world (16.8).
- After P2 and after P4, a sharp edge (173, syntactic points) and the
  update of gvsharp-orders.lagda.

Stage 2b, kept, adapted or deleted.

| File | Fate |
|---|---|
| Criterion.v, `lf_criterion` | kept. Statement unchanged, `waits` changes underneath |
| Fair.v | `waits` reads ends, the rest kept |
| ThreadProgress.v, `thread_progress` | kept |
| TauThread.v, Instr.v, Reach.v, LocalProgress.v | adapted to labels on ends and `selects` by bit |
| LFRelation.v | deleted (`placement`, `oracle`, `aconf`, `aupd`, `areach`, `LFconf`, `LFPrel`). `snd_next`, `rcv_next`, `sel_next`, `bra_next`, `tick` and `link_fuel` move into LFSoup.v for `pupd` and `cnt` |
| LFAdequacy.v | the instantiation of the criterion is kept and moved from annotations to π_k and `cnt` (`holder_one`, `holder_exists`, `sync_partner`, `nonpart_terms`, `fuel_pos`, `c_waits_holder`, `rank_pt_eq`). `areach_isteps` and everything about ω go. `lfsoup_step` replaces the preservation of annotations |

### 16.7  Translations and paper

PGV, PN and MP share `expr`, so `Chan c b` and the labels reach their
sources too (MP2Semantics.v, PNSemantics.v). PN and MP translate typing
derivations (`pn_typed Γ e s τ e'`) and can write the point of each `new`
from the level or priority of its derivation. A level-polymorphic PN
function needs a point parameter, which (b) supplies. PGV translates the
constant `new` to a fixed term (`new_tr`, PGVTranslate.v), so its
translation has to become type directed, or PGV's `new` has to carry its
priority. The three stay out of the build until the translations resume.

The paper says that terms carry no types or points. After this change a
term carries the point of each `new`, as a value of type Pt(ι), and boxes
stay Curry style. The two ends of a channel get names c⁺ and c⁻. Lock freedom reads as the live relation on
thread soups plus a fuel condition on runs, and the composition rules of
the paper keep their form.

### 16.8  Closing the fuel gap (for the author)

Fuel composes if the shared world carries the bound that 16.5 found
missing. Let W carry budgets β from points to ℕ below N, and let the term
relation carry counters φ for held ends that tick at every step of the
holder on another end. O-Recv quantifies over received counters
φ_in(o) ≥ β k for the carrier point k, and O-Send asks φ(o) − 1 ≥ β k for
every end it hands on at k. Acting refills to N. A forward from carrier k
to carrier m then needs β k > β m, so endless delegation needs an infinite
descent in ℕ and fails, while the Forwarder passes with β k ≥ β m + L + 1.
P-Connect and P-Join see one W, so budgets need no combining. The fragment
sets β k from the R4′ depth of the session type at k, (d − depth + 1)·2L.
The cost is a component of the world and an index of `Ebody`. Ticking stays
conservative inside the term relation, so the controller keeps needing the
closed judgment of 16.5. This option is unverified, and tickets in session
types are the syntactic alternative.

## 17  One order, one fuel: the obligations view (design, 2026-11-09)

This section tests the obligations view against the definitions and the
examples. It changes no Rocq file. "Checked" marks a claim checked against a
definition or a Rocq lemma, "argued" a claim argued on paper.

Verdict. Addition (B) does not replace uniform placement. A height bound on
the waited point helps only if the point is the same at every index, and
O-New picks it per index. C1 is in the relation at every index in a world
where every point has finite height (17.2). So the syntactic points of §16
stay, and Rank stays `well_founded (w_lt W)`. Addition (A) holds after two
corrections. Fuel must not burn on internal steps, and the payload bound
belongs to the carrier's point, not to the payload type. As a predicate on
threads with budgets per point, fuel composes. It replaces `fuel_run` of
16.5, the run-level ticking of §7 and the N of §10.3 (17.3). The judgment
then has one order (W with the gates), one fuel (per held end), the costs of
the live relation for internal steps, and syntactic points for placement.
The oracle is gone.

### 17.1  Five ways to starve

| Pattern | Programs | Handled by | Status |
|---|---|---|---|
| circular wait | Padovani's (1), the reversed Cycle | the gates (`below_rest`, `above_offered`) and local progress, unchanged | checked (deadlock freedom, LocalProgress.v) |
| a chain of waits that grows over time | C1, C1′, KobForwarder | Rank on a placement that is the same at every index, that is `well_founded (w_lt W)` with syntactic points. (B) alone fails (17.2) | facts checked (`c1_rank_fails`, `kob_cworld_not_wf`), the rest argued |
| holder postponement | the program of liveness.md §9, the first two lock-freedom rows of §8 | fuel. A held end's counter drops at every channel step of its holder on another end | argued |
| endless delegation | the starving server, Padovani's (2), C3 | fuel. A message passes the counter minus one and asks a floor of the carrier's point. A link asks the peer's budget to lie below the counter | argued |
| internal divergence | KobForwarder's τ loop, `div_main` | the least fixpoint of the live relation (`no_tau_divergence`), unchanged | checked (`live_adequacy`) |

Internal steps stay out of the fuel. A thread that receives a closure and
runs it before it acts on a held end takes a number of internal steps that
the guard makes finite and nothing bounds, because O-Recv is universal over
the payload. A fuel that burned on internal steps would reject such threads.
`lf_criterion` does not need it either. Its admin measure (`thread_acc`,
TauThread.v) orders the internal steps of a holder. (argued)

### 17.2  (B) without uniform placement fails

The claim was this. If a thread may block only at a point of height at most
h, then at every index the chain of waiting threads below that point has at
most h links, a bound that no index can move. The bound holds at each index.
But the waited point is placed per index as well, so h depends on the index.

**Counterexample, C1 without a ceiling.** W is `Wpo [a]`, program order on one
constant a and no other fact. Main creates its own channel at run time.

```
main     = let (c0, c0′) = new in spawn (λ_. spawner c0′); recv c0      blocks forever
spawner  = rec f. λprev. let (ck, ck′) = new in let (dk, dk′) = new in
             spawn (λ_. recvclose ck; close prev);                      T_k blocks on ck
             spawn (λ_. recvclose dk′); sendclose dk;                   one chatter step
             f ck′
```

At index n, O-New places main's c0 at a+(2n+1), c_k at a+(2(n−k)+1) and d_k
at a+2(n−k), for k ≤ n. T_k offers at a+(2(n−k)+1) and holds the partner end
of c_{k−1}, whose dual point is a+(2(n−k+1)+1). The spawner offers d_k below
the dual point of the c_k end it holds. Every gate is a program-order fact.
Each round costs at least one, so index n ends before round n. Fuel 2
suffices, because a blocked thread takes no step and the spawner hands each
end on after one chatter step. Every point a+m has height m, so (B) holds at
every index. W is well founded. Main starves in every fair run.

Checked in Rocq, in a scratch file that compiles against this branch and is
not committed (C1World.v, no axioms). The lemmas are `Wpo1_wf` (W is well founded), `Wpo_rank` (x ≺ y gives
`pt_size x < pt_size y`), `Wpo_finite_height` (every x has height at most
`pt_size x`) and `c1_gate` (both gates of round k at index n are facts of
`Wpo [a]`). Argued, as in 14.1: the live relation accepts this placement at
index n.

The counterexample needs no ceiling. §14.1 used one only because main's
channel was top level. So no condition on heights in W rejects C1 while O-New
places per index. A condition read at index n sees fewer than n rounds,
placed in an initial segment of program order, and every bound that may
depend on n accepts that segment.

**Uniform bounds do not help.** Three index-free bounds come from the
obligations view, and each loses examples.
- A constant H on the height of every waited point, Lawyer's finite set of
  levels (namakonov2026lawyer, p8). Program order is part of every world
  (`wf_lt_po`, a field of `world_wf`), so the point of a recursive server's
  channel in round k has height at least k. H rejects every infinite server.
  (checked against `world_wf`)
- A separate level map with values below H that falls along every gate fact
  in use. GrowRing uses the fact Y ≺ Y[0]‾ at every node (`rg_F`, first
  disjunct), and the child pair (X[1], Y[0]‾) of `rr_r` makes Y[0]‾ the next
  node's Y. The levels must then rise along the ancestry without bound.
  Padovani types the ring with priorities that grow without bound, through
  shifting (padovani2014deadlock, p6, p8). (argued from GrowRing.v)
- A constant D on the length of the actual waiting chains. It is a fact of
  each configuration, but it does not compose (14.3, option 4).

Lawyer meets the same wall. Its levels and degrees must be finite sets,
because otherwise the transitions that create signals and exchange fuel
branch infinitely, and the step-indexed refinement needs finite branching
(namakonov2026lawyer, p24). O-New picking a point per index is exactly such
infinite branching. Fuel escapes it, rank does not. A cap on fuel bounds
every value a per-index choice can take, so per-index choices cannot
prolong a delegation chain past the cap. Ranks have no cap, because program
order raises them along every recursive channel.

**The criterion.** Per-index placement gives no stable `we`, so
`rank_bound` cannot be instantiated from (B). A criterion by induction on
the depth of the waiting chain is provable from the existing proof, but it
needs a uniform depth bound, which (B) does not supply. With the placement of
§16, `lf_criterion` applies unchanged, with R = `w_lt W` and `we k t` the
point π_k of t's end (16.5). (argued)

**(B) with uniform placement.** It would be sound, and it would let R be `<`
on ℕ. But finite height is not preserved by the Kripke extensions of `Ebody`.
`wext W W'` asks only inclusion and strictness, so W′ may put infinitely many
points below a point of W. (checked against `wext`.) (B) would need a rank
map in the world, `rk : point → option nat`, monotone on facts and kept by
`wext` and `wjoin`, and a static premise "x is waitable" at every `new`. It
buys nothing over `well_founded (w_lt W)`. We do not adopt it. Its one good
idea, that an end nobody waits on needs no fuel, moves to budgets (17.3).

### 17.3  Fuel as a predicate on threads

Fuel becomes a second predicate on each thread of the soup, next to `LErel`.
It needs no type, because §16 names ends in terms (`fends`, labels on ends)
and fixes points outside the index (π). So `LiveRelation.v` keeps the form
§16 gives it, and every liveness statement keeps its form.

```
Notation fuel := (option nat).                 (* None is ∞, the end carries no obligation *)
Record budget := Budget {
  b_bud : point → fuel;                        (* refill and cap of an end at this point *)
  b_pay : point → nat;                         (* floor of an end that arrives on a carrier at this point *)
  b_val : point → nat }.                       (* floor of an end passed to a received closure *)

(* FuelE n B π φ e. π and φ map the ends of e (dom π = dom φ = fends e)
   to their points and counters. Indexed by all steps, admin steps included. *)
FuelE 0 B π φ e := True.
FuelE (S n) B π φ e :=
  (∀ o, o ∈ dom φ → φ o ≤ b_bud B (π o)) ∧                                  (* F-Cap *)
  (∀ σ e', tstep e (LSess σ) e' → ¬ is_link σ →
     b_bud B (pt_dual (π (aend σ))) ≠ None) ∧                               (* F-Wait *)
  for every step e →α e', with the counters φ' of the successor:
  - β: φ' = φ.
  - new c at x: π gains (c, pt_pol x) ↦ x and (c, negb (pt_pol x)) ↦ pt_dual x,
    φ gains their budgets.
  - an action on end o other than a link (send, receive, close, choice):
    every other o′ with φ o′ = Some m has m ≥ 1 and drops to m − 1 (F-Tick).
    o refills to b_bud B of its next point.
  - send on o at point k with payload w: every o₂ ∈ fends w has φ o₂ = None or
    φ o₂ = Some m with m − 1 ≥ b_pay B k. The ends of w leave π and φ.
  - receive on o at point k: for every value w and every π_in, φ_in on fends w
    with b_pay B k ≤ φ_in o₂ ≤ b_bud B (π_in o₂) and Vfuel n B π_in φ_in w,
    FuelE n B (π ∪ π_in) (φ' ∪ φ_in) e'.                                    (O-Recv stays universal)
  - spawn w: the ends of w go to the child with counter − 1 ≥ 0, and
    FuelE n B π_w φ_w (App w EUnit) holds for the child.
  - link of (c, b) and (d, negb b): φ (c, b) = None or
    b_bud B (pt_dual (π (d, negb b))) < φ (c, b), and the same with c and d
    swapped. Both ends leave. The peers keep their counters.
  and FuelE n B π' φ' e' for the successor.

Vfuel n B π φ w : Prop      (* untyped. An end needs φ o ≥ b_val B (π o). A closure,
                               applied at any j < n to arguments that satisfy Vfuel j,
                               satisfies FuelE j. Pairs and sums componentwise. *)
```

The counters live per held end, in φ, beside the points in π. Both sit in
the soup outside the index, as π does in 16.5.

```
Definition LFsoup n W B Σ T (π : gmap cend point) (φ : gmap cend fuel) (p : proc) : Prop :=
  ∃ ts, (the soup clauses of 16.3) ∧
        Forall (λ '(e, Θ, U), LErel n W Θ U ∅ e ∧ FuelE n B (π|e) (φ|e) e) ts.
Definition LFP W B Σ T p : Prop :=
  (∀ n, LPrel n W Σ T p) ∧ ∃ π φ, ∀ n, LFsoup n W B Σ T π φ p.
```

**What burns and what resets.** A channel step of the holder on another end
burns one unit. Internal steps, `new`, spawn and links burn nothing. Acting
on the end refills it to the budget of its next point. A message hands the
end on with the counter minus one, a spawn the same. A link hands the
obligation to the peer, whose own counter lies below the linker's by the link
clause and F-Cap. At zero the holder can neither step on another end nor hand
the end on, so its next channel step is on that end. (argued)

**§7 is dropped and replaced by F-Wait.** A thread cannot see whether its
partner offers, so the term level cannot tick "only while offered". Instead a
thread may act on an end only where its partner's budget is finite. Ends with
budget ∞ never tick, and nobody ever waits on their partner. In the
controller, ctl and ctl′ get budget ∞ at both points. The waited ends have
finite budgets, so the holder's counter is finite by F-Cap, and `fu` lands in
ℕ. This is the useful half of (B), in the budgets instead of the order, where
per-index placement cannot touch it because points are syntactic.

**No global N.** The budgets replace it, for two reasons. The link clause
reads the budget at the peer's point. With one constant N it would ask
N < φ ≤ N, so no waitable end could be linked. And ∞ carries the exemption
of §7. Budgets keyed by syntactic points are uniform. Without syntactic
points a uniform cap would be needed instead, because a budget read at a
point placed per index could be n at index n, and the postponement program
would pass.

**The payload bound sits on the carrier's point, not in the payload type.**
A forwarded end keeps its point, and the bound must fall at every hop. In the
Forwarder the end sits at ρ = (ι+k)[0] at both hops (Forwarder.v). So a floor
keyed by the end's own point cannot fall. A floor keyed by the carrier's point
k can, and a forward from carrier k to carrier m asks
b_pay k ≥ b_pay m + s + 1, with s the holder's channel steps in between.
Endless delegation asks this along infinitely many carrier points, an
infinite descent in ℕ. Tickets in the payload type are the type-level
alternative (padovani2014deadlock, p2, p7). They change `ty`, and higher-order
payloads would need them on every channel type. We reject them.

**The interfaces.** FuelE reads the thread's own term, so its own code has
no interface. The relation is universal over incoming ends only at O-Recv
(floor `b_pay`) and where a thread applies a value it received (floor
`b_val`). First-order programs never do the latter, and the fragment sets
`b_val` to 0. The fundamental theorem needs typed interfaces at λ and box
arguments for its compatibility lemmas. Those floors are proof devices of the
fragment (17.6), not clauses of the definition. (argued)

**Adequacy.** `lf_criterion` is unchanged. The instantiation of 16.5 keeps
placement and rank, and `fu k t` becomes φ_k of the partner of t's end, with
φ_k computed along the run like π_k. The receiver takes the sender's counter
minus one, a spawn does the same, a link leaves the peer's counter, and an
action refills. F-Wait at t makes the partner's budget finite. Hfuel follows from
F-Tick, the message and spawn clauses, and the link clause. The soup
preservation `lfsoup_step` gains the fuel conjunct. In a message the
receiver's O-Recv takes the sender's π and its counters minus one, which meet
the floor by the sender's clause and the cap because the point does not
change. (argued)

```
Theorem lf_adequacy W B T p :
  world_wf W → well_founded (w_lt W) → LFP W B ∅ T p → lock_free p.
Corollary lf_adequacy_ex W T p :
  world_wf W → well_founded (w_lt W) → (∃ B, LFP W B ∅ T p) → lock_free p.
Corollary lf_thread_progress W T p :
  world_wf W → well_founded (w_lt W) → (∃ B, LFP W B ∅ T p) →
  ∀ r l, erase (r 0) = p → maximal r l → wfair r l → thread_progress_run r l.
```

### 17.4  Composition

```
Definition fsem B (π : gmap cend point) (t : expr) : Prop :=
  ∀ n, FuelE n B π (b_bud B ∘ π) t.                         (* every held end starts full *)

Theorem LFP_term W B Σ ΘB C0 t T :
  prim T → strict W → dom ΘB = C0 → dom Σ ## C0 →
  (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
  lsem_typed W (tenv_of Σ ∪ ΘB) [] ∅ t T → tenv_fit (tenv_of Σ ∪ ΘB) t →
  fsem B (tenv_points (tenv_of Σ ∪ ΘB)) t →
  LFP W B Σ T (C0, {[+ t +]}).

Theorem LFP_connect W1 W2 B Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :
  (the hypotheses of LPrel_connect, with LPrel replaced by LFP W1 B and LFP W2 B) →
  LFP (wjoin W1 W2) B (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).

Theorem LFP_join W1 W2 B Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :
  (the hypotheses of LPrel_join, with LPrel replaced by LFP W1 B and LFP W2 B) →
  LFP (wjoin W1 W2) B (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
```

The three keep the form of `LPrel_term`, `LPrel_connect` and `LPrel_join`.
P-Connect and P-Join concatenate the soups and join π and φ, whose domains
are disjoint ends. FuelE of each thread is untouched, because it meets the
environment only through O-Recv, which is universal, and a link by another
thread leaves its counters alone. The ends of the cut keep their counters on
both sides. B is shared like T. It is not monotone (a larger `b_pay` helps
the receiver and burdens the sender), so composition asks one B rather than
a combination. The fundamental theorem computes B for the whole program, and
a direct semantic proof picks B for the composite. (argued)

**Approved statements that change form**, beyond 16.4.
1. 16.4 item 6. The adequacy family takes `LFP W B ∅ T p` (or `∃ B`) instead
   of `LFP W ∅ T p ∧ ∃ N, fuel_run N p`. `cnt`, `fuel_ok`, `fuel_run` and
   `fuel_run_mono` go.
2. 16.4 item 7. `LFP_term` gains `fsem`, and the three statements gain B.
3. Nothing else. `ty`, `sty`, the typing rules, `payload_at`, `LVrel`,
   `LErel` and `LPrel` (beyond §16), the live theorems, `lock_free`,
   `lf_criterion` and `thread_progress` keep their statements. The world
   record does not change, because B is a parameter of the fuel predicate.

### 17.5  The examples

Height is read in the world each example is typed in today
(`cworld`, Fragment.v). "Waits at infinite height" asks whether some action
happens at a point with infinitely long chains below it.

| Example | Waits at infinite height | Verdict under §17 | Why |
|---|---|---|---|
| Forwarder | no, `fw_rank` is a rank into ℕ (`fw_wf`, checked) | in | one hop, b_pay k₁ ≥ b_pay k₂ + s + 1 |
| TailCall | no, actions at ι+k and ῑ+k have finite height. The ceiling ι[0] has height ω and carries no channel (checked against `tc_C` and program order) | in | one channel, nothing ticks |
| CfstScheduler | no, the rank 9⌊k/2⌋ + b is finite on every instant. The ceiling z carries no channel (checked against `sch_C`) | in | every end acted on in each round of 6 steps |
| GrowRing | no, the rank 2·depth + offset is into ℕ (`rg0_rank`, checked) | in | z travels once, then is spawned (−1) into a call that receives on it first |
| ABP | no, the ladder rank is finite on every instant, the ceiling θ carries no channel (`abp_wf`, checked) | in | every end acted on in each round |
| ReceivedChain | no, the rank 2·depth + offset is into ℕ (checked against `ch_C`, `chs_C`) | in | the received end is acted on first by the spawned call |
| controller (§7) | its gates put ctl's dual points above every point of r, so they have height ω. Nobody acts there | in, with budget ∞ at ctl's points | F-Wait holds, ctl never ticks. Outside the fragment (R2) |
| postponement (liveness.md §9) | no, if the loop reuses one point (G3). C waits at a point of height 1 | out | fuel. A ticks on b at every round |
| KobForwarder | yes, an infinite descending chain lies below each ι[0]ⁿ (`kob_cworld_not_wf`, checked) | out | Rank, and the guard |
| C1 | yes with syntactic points (`c1_rank_fails`, checked). Never at a fixed point without them (17.2) | out with §16, in without it | Rank on a uniform placement |
| C1′ | as C1 | out with §16 | Rank |
| C3 | no | out | the link clause asks b_bud of b_k below the counter of y, which falls by one per round, an infinite descent |
| starving server | no | out | b_pay must fall along the carrier's points forever |
| Cycle, Sync | no recursion, finite heights | in | trivially |

No lock-free example in the list needs a wait under a ceiling. Every ceiling
(ι[0] in TailCall, z, θ, ζ) is an upper point of a future and carries no
channel. TreeSum's opened point κ′ is a program-order successor of κ at run
time, so its height is finite (argued). TreeSum stays outside the fragment by
R1.

### 17.6  The static fragment

- **Rank.** `wf_world` stays, with the `cworld` rank lemmas.
- **Hand-offs.** R4′ and the link clause of R2′ merge into one graph. A
  forward adds the edge of R4′. A link of ends at types A and B adds edges
  from A and from B to the types of the peers that take over. The graph must
  be acyclic, with depth d. C3 closes a cycle (y hands over to b, which is
  the next round's y). The starving server closes one through the fed slot.
  The guard, R1 and R2-recv stay.
- **Budgets.** b_bud x = (d − depth x + 1)·2L, with depth x the depth of the
  type that the derivation gives the end at x, the minimum over all such
  types when two channels share x. b_pay k = (d − depth k)·2L + L + 1 from
  the carrier's payload type. b_val = 0. The fragment never uses ∞, so
  F-Wait holds trivially. N = (d+1)·2L of §10.3 is the largest budget.
  (argued)
- **The fundamental theorem.**
  `lf_fundamental : lfptyped W ∅ p T → ∃ B, LFP W B ∅ T p`. The live part is
  P5 of 16.6. The fuel part is per thread. A typed fuel interpretation of
  the guarded derivation sets floors by position. Box arguments are acted on
  in the round (R2-recv), so they carry at least b_bud − L. Received payloads
  carry at least b_pay. A round has at most L channel steps (guard and R1).
  One compatibility lemma per typing rule gives `fsem B π t` for every
  thread, then `LFP_term` per thread and `LFP_connect`/`LFP_join` along
  `ptyped`. This replaces the preservation of a run budget in 16.6 P5 by a
  compositional proof. (argued)

### 17.7  Comparison and stages

| | §15 oracle | §16 syntactic points | §17 |
|---|---|---|---|
| placement | ω on closed runs | in the syntax | as §16 |
| rank | `well_founded (w_lt W)` | same | same |
| fuel | counters on annotated runs, N | `fuel_run N p` on closed runs | FuelE per thread, budgets B |
| composes | no | soup yes, fuel no | yes |
| choice principle | countable choice for ω | none | none |
| controller | no | closed judgment | compositional, budget ∞ |
| type syntax | unchanged | Pt, EPt, `Chan c b` | as §16 |

§17 is §16 with its open gap closed. (B) is rejected as a replacement for
placement, and kept only as the budget exemption.

Stages, one agent each, at most two at once.
- **L1, L2.** §16 P1 and P2.
- **L3a beside L3b.** §16 P3a and P3b.
- **L4a beside L4b.** L4a is §16 P4 without fuel (LFSoup.v, `pupd`,
  `lfsoup_step`, rank). L4b is the new file LFFuel.v with `budget`, `FuelE`,
  `Vfuel`, `fsem`, monotonicity in n, the fuel update `fupd` along steps and
  `lffuel_step`, the preservation of the fuel conjunct. L4b needs only P1.
- **L5.** `LFP` with B, `lf_adequacy` from `LFsoup` and `fupd` (`fu`, Hfuel),
  `LFP_term`, `LFP_connect`, `LFP_join`. The controller as a Rocq example,
  semantic, with budget ∞ at ctl.
- **L6.** The fragment. The hand-off graph, budgets from the derivation, the
  typed fuel interpretation, `lf_fundamental`. Rejection lemmas for C3 and
  the starving server by budgets, and for C1 with syntactic points, are
  optional.
- After L2 and after L5, a sharp edge and the update of gvsharp-orders.lagda.

Kept. Criterion.v unchanged (`lf_criterion`, `rank_bound` with R = `w_lt W`).
ThreadProgress.v unchanged. Fair.v, TauThread.v, Instr.v, Reach.v and
LocalProgress.v as adapted in §16. LFRelation.v is deleted. `snd_next`,
`rcv_next`, `sel_next` and `bra_next` move to LFSoup.v, `tick` to LFFuel.v.
`link_fuel` goes, because the peers now keep their counters and the linker
checks the peer's budget. LFAdequacy.v keeps the instantiation of the
criterion (`holder_one`, `holder_exists`, `sync_partner`, `nonpart_terms`,
`fuel_pos`, `c_waits_holder`, `rank_pt_eq`), moved to π_k and φ_k.

### 17.8  Budgets in the world (author, 2026-11-09)

The author approved §17 with one change. The budgets move from a shared
parameter B into the world, so that each component brings its own, as it
brings its own order facts. One shared B would be a global object.

```
Record world := World {
  w_names : gset pname;
  w_lt    : prel;
  w_bud   : point → option nat;   (* refill and cap; None is ∞, nobody waits *)
  w_pay   : point → nat }.        (* floor of an end arriving on a carrier at this point *)
```

`b_val` is dropped if the fragment keeps it at 0 and no example needs it.
Otherwise it becomes a third field. `wext` keeps budgets on the support of
the smaller world. `wjoin W1 W2` takes each component's budgets on its own
root names, and the components agree at the points of the cut, a condition
of the kind `strict (wjoin W1 W2)` already is. `FuelE n W π φ e` reads the
budgets from W. The judgment and the composition lemmas lose B.

```
Definition LFP W Σ T p : Prop :=
  (∀ n, LPrel n W Σ T p) ∧ ∃ π φ, ∀ n, LFsoup n W Σ T π φ p.
Theorem LFP_connect … : (the hypotheses of LPrel_connect, with LPrel replaced by LFP W1, LFP W2) →
  LFP (wjoin W1 W2) (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
Theorem lf_adequacy W T p : world_wf W → well_founded (w_lt W) → LFP W ∅ T p → lock_free p.
```

The world record changes form, an approved statement (item 3 of 17.4 is
superseded). Every lemma about worlds that builds a world (`wext_cc`,
`wjoin`, `cworld`, `Wpo`, `wgen`, BranchWorlds) gains the two fields. The
base and live relations ignore them. Stage L2 adds the fields.

## 18  Replacement against the send floor (design check, 2026-11-16)

No repair of the floors or of the replacement minimum saves option 2. The
mismatch of quirk A13b is one face of a deeper clash. The replacement clause
lets another thread lower the counter of any held end to the minimum, and
the link clause asks the linker for one unit more than that minimum on the
end it links. So a thread that links an end whose partner another thread
holds fails FuelE, whatever the budgets. The scheduler is such a thread, so
it fails `fsem` in every world. The repair recommended here drops
replacement and pays for links with a per-thread count of link tickets,
which only the linking thread spends. The fuel measure of adequacy becomes
the pair (tickets left in the configuration, counter), ordered
lexicographically. Scratch proofs are in
`/tmp/claude-1000/-home-mari-proglang-research-rocq-spo-lr-df/7697b606-e2a0-4025-b152-57610f751662/scratchpad/repcheck/RepCheck.v`,
compiled against HEAD 75ae03d, all closed under the global context.

### 18.1  The scheduler fails under option 2 in every world

`link_after_rep_absurd` takes a thread at `FuelE (S (S n))` whose next step
links o1 with o2, o1 at k with a counter. If `w_pay W k` lies under
`w_bud W k`, `frep` lowers the counter of o1 to `w_pay W k`, and `flink1`
then asks `w_pay W k + 1 ≤ w_pay W k`. `link_cap_absurd` covers the other
case. There F-Cap keeps the counter at or below a budget that lies under
the floor, and `flink1` fails again. ag₁ of the scheduler links r₁ at γ
with r₀′ at γ̄, so

```
Theorem sched_not_fsem_all W : ¬ fsem W ∅ Scheduler.sched_main.
Corollary sched_not_fsem_src : ¬ fsem (src_world Scheduler.sched_Ψ Scheduler.sched_main) ∅ Scheduler.sched_main.
```

The forwarder counterexample (`fw_not_fsem_roots`) needs floors keyed on
roots. This one needs nothing about the world. Stage L6 is false under
option 2 for the scheduler as well as for the forwarder.

The clash is arithmetic and holds for any minimum that depends on the point
or the world alone. Let R(k) be the least value replacement may write at k,
and let the link clause ask m ≥ X(k) of the linker's counter m on an end at
k. The soup hands m − 1 to the peer, and `fuel_link` needs that value inside
the range of replacement, so X(k) − 1 ≥ R(k). The linker's own end is
replaceable down to R(k), because its partner sits in another thread, and
it must still link. So R(k) ≥ X(k), a contradiction. The same argument
applies when the counter is replaced by a per-end link ticket, because the
linker's ticket is then replaceable in the same way.

### 18.2  The three candidates

Candidate 1 (exempt ends whose partner the holder holds) is sound for the
soup. At a link of i, the replaced end cdual o1 sits in the map `BP t` of
`fuel_link` before the renaming. For t ≠ i its partner o1 is in `A i`,
disjoint from `A t` by `lf_disj`. For t = i the linker's map has dropped o1
by `mrem`. So the soup never replaces an end whose partner the holder holds,
and the exemption costs `fuel_link` nothing. It reads only `dom π`. It fixes
the forwarder as written, because the producer holds e′ until after the
send. It fails the form where the producer spawns e′ away before the send,
because a link of e′ in the child can then lower e to `w_pay W γ̄[0]`. It
fails the scheduler, because r₁ has its partner r₁′ in ag₂, so
`sched_not_fsem_all` goes through unchanged.

Candidate 2 (floors that grow along payload fields) cannot help, because
`sched_not_fsem_all` holds at every world. It has two problems of its own.
A box may recur on π[0] and reach unbounded field depth, so a uniform B
needs a syntactic bound on that depth. An existential payload, as in fwd,
sits at a point unrelated to its carrier's, and a deep own root under a
shallow carrier breaks the order of the floors again.

Candidate 3 (a different minimum or a stronger link clause) is the case of
18.1. The floor at the carrier of the linked obligation is not visible to
FuelE, and any point-keyed or world-keyed choice meets the contradiction
there.

### 18.3  The repair: link tickets

What a link consumes has to be something no other thread can lower. Each
thread carries a ticket count tk, outside the index like its counters. A
link needs tk ≥ 1 and spends one. A spawn splits the count between parent
and child, and values carry none. Nothing writes into another thread's
counters, so the replacement clause, `frep`, `flink1`, `flr` and `fuel_rep`
go. A waiter whose partner the linker held now waits on the holder of the
other peer at that holder's own counter, which F-Tick bounds there. The
counter may rise at the link. The total of tickets in the configuration
falls by one at the same step, and nothing ever raises it.

```
(* LFFuel.v. V keeps the old fpred. E gains the ticket count. *)
Abbreviation epred := (world → gmap cend point → gmap cend fuel → nat → expr → Prop).

Definition Fobl (E : nat → epred) (V : nat → fpred) (n' : nat) (W : world)
    (π : gmap cend point) (φ : gmap cend fuel) (tk : nat) (α : tlabel) (e' : expr) : Prop :=
  match α with
  | LBeta | LNew _ _ => E n' W (fupd W π φ α).1 (fupd W π φ α).2 tk e'
  | LSpawn w =>
      fhand 0 (fends w) φ ∧
      E n' W (fchild π φ w).1 (fchild π φ w).2 (Nat.div2 (S tk)) (App w EUnit) ∧
      E n' W (fupd W π φ α).1 (fupd W π φ α).2 (Nat.div2 tk) e'
  | LSess σ =>
      (∀ o, sl_end σ = Some o → ftick_ok o φ) ∧
      match σ with
      | SSend o w =>
          (∀ k, π !! o = Some k → fhand (w_pay W k) (fends w) φ) ∧
          ftravel W π (fends w) ∧
          V n' W (mres (fends w) π) (ftick <$> mres (fends w) φ) w ∧
          E n' W (fupd W π φ α).1 (fupd W π φ α).2 tk e'
      | SRecv o w =>
          ∀ k j πi φi, π !! o = Some k → j ≤ n' →
            dom πi ## dom (fupd W π φ α).1 →
            fin_ok W (w_pay W (pt_dual k)) w πi φi →
            V j W πi φi w →
            E j W ((fupd W π φ α).1 ∪ πi) ((fupd W π φ α).2 ∪ φi) tk e'
      | SLink _ => 1 ≤ tk ∧ E n' W (fupd W π φ α).1 (fupd W π φ α).2 (tk - 1) e'
      | _ => E n' W (fupd W π φ α).1 (fupd W π φ α).2 tk e'
      end
  end.

Definition Fdef (E : nat → epred) (V : nat → fpred) (n' : nat) (W : world)
    (π : gmap cend point) (φ : gmap cend fuel) (tk : nat) (e : expr) : Prop :=
  ∀ W' g π' φ', wbext W W' → renk g π π' → renk g φ φ' →
    fcap W' π' φ' ∧ fwait W' π' (emap g e) ∧
    ∀ α e', tstep (emap g e) α e' → Fobl E V n' W' π' φ' tk α e'.

(* Vfdef: the two clauses that call E run the value at 0 tickets. *)
  | Lam eb =>
      ∀ j v πa φa, j < n → dom πa ## dom π → fin_ok W 0 v πa φa → V j W πa φa v →
        E j W (π ∪ πa) (φ ∪ φa) 0 (App (Lam eb) v)
  | EBox eb => ∀ j, j < n → E j W π φ 0 (App EForce (EBox eb))

Definition fsem (W : world) (π : gmap cend point) (t : expr) : Prop :=
  ∃ tk, ∀ n, FuelE n W π (w_bud W <$> π) tk t.

Lemma FuelE_tk_mono n W π φ tk tk' e : tk ≤ tk' → FuelE n W π φ tk e → FuelE n W π φ tk' e.
```

The split at a spawn is fixed, ⌈tk/2⌉ to the child and ⌊tk/2⌋ to the
parent, and the two add up to tk. An existential split would let the
witness depend on the index, and the soup fixes the counts of every thread
outside the index. Recovering one witness for all indices is a pigeonhole
over a finite range, which is classical. `FuelE_tk_mono` holds because
`div2` is monotone, and it lets a received value that runs at 0 tickets
run inside a thread that has more.

In the soup, `lf_fuelc` and `fstep` carry a third family `K : nat → nat`
beside P and F, and `lf_fuelc` asks `FuelE n W (P t) (F t) (K t) e`. A link
sets `K i` to `K i − 1` and leaves every counter except the linker's own
unchanged before `kren`. A spawn gives `div2 (S (K i))` to the child and
`div2 (K i)` to the parent. Every other step keeps K.

### 18.4  Checks

The forwarder passes in all three forms, because without replacement only
the holder moves its counters. Right after the new, e holds B, and after at
most L − 1 ticks it still has (d + 1)·L + 1, which meets every floor. That
holds whether e′ stays with the producer or has been spawned away. A
received end arrives at the floor of its carrier and is passed on along a
deeper root, as Fragment.v argues. The scheduler links once, in ag₁. main
starts with one ticket, and the first spawn hands it to ag₁.

C3 stays excluded, now by the relation. A link loop takes one ticket per
round, so FuelE fails at every finite tk once the index passes tk rounds,
and `fsem` asks for a finite tk. The variant where two threads take turns
linking the waiter's end is excluded too. Tickets are conserved at spawns
and spent at links, so a run performs at most as many links as the
configuration held tickets at its start.

Adequacy. `fu_at` stays. The criterion reads the pair `(Λ k, fu k t)` with
`Λ k` the sum of `K_k t` over the threads of `r k`. Λ never rises. A link
lowers it by one, and a thread that ends takes its tickets with it. At every
other step Λ stays or falls and the old analysis of fu applies unchanged.
`core` in Criterion.v inducts on fu with `lt_wf_ind`. The same induction
works for any well-founded order on the measure, here the lexicographic order on
pairs of naturals, and `Hdrop` and `Hfuel` keep their shape with that order
in place of `<`. `fe_link` shrinks to the fact that Λ falls.

Composition. Tickets live in the threads, not in the world, so `wbud_agree`
and the world record are untouched. `LFP_connect` and `LFP_join` take the
union of the per-thread families K as they do for P and F. `LFP_term` asks
`fsem`, which now hides the initial ticket count of the thread.

Semantics. The ticket count is thread state like the counters. The link
clause reads tk and nothing else, and no clause reads a term. The fragment
loses its link edges, because links no longer hand counters on.

Counterexample. None exists for soundness. Λ is conserved by every step
except links and the end of a thread, where it falls, and every clause that
fu relied on is unchanged at steps other than links. The repair costs
completeness at two places. A received closure that links fails, because
values run at 0 tickets. A box that links once per round fails, which the
fragment rejects already by its link self-loop.

### 18.5  What L6 then needs

- Fragment.v. Drop the link edges of `troots` and keep links out of boxes,
  stated as such rather than as a self-loop. A thread's ticket count bounds
  the link sites it can still run. Outside boxes every site runs at most
  once, so main starts with 2^s · ℓ tickets, with s the spawn sites and ℓ
  the link sites outside boxes, and `FuelE_tk_mono` absorbs the slack. A
  link may stop costing a unit in `scost`, which shortens L.
- LFFuel.v, LFSoup.v, LFAdequacy.v, Criterion.v, LFCompose.v as in 18.3 and
  18.4. `fuel_link` loses its replacement step and its level, so a link goes
  from index n + 1 to n like any other step.
- LFFuelTyped.v. `fw_fuel_floor`, `fw_not_fsem_roots`, `fw_not_fsem` and
  `lf_fuel_fundamental_fails` concern `frep` and go with it. The typed fuel
  interpretation proves `fsem (src_world Ψ t) ∅ t` with the ticket count of
  the fragment. Its send case needs the floor argument of Fragment.v for
  fresh, refilled and received ends, and its link case needs only tk ≥ 1.
- Decision for the author. This reverses the part of option 2 that hands
  counters on at a link. Links still move the obligation, and the bound on
  how often they do comes from tickets.

## 19  Higher-order lock freedom: cost-annotated arrows (design, 2026-11-17)

This section designs lock freedom for every program the static system
accepts, higher-order programs included, and gives the paper proof of
the fundamental theorem. It changes no Rocq file. "Checked" marks a claim
checked against a definition at d9e6ceb or in a scratch file, "argued" a
claim argued on paper. The scratch files are in
`/tmp/claude-1000/-home-mari-proglang-research-rocq-spo-lr-df/7697b606-e2a0-4025-b152-57610f751662/scratchpad/cost/`
(Tix.v and Frame.v stand alone, Merge.v and Collide.v compile against
d9e6ceb). All their lemmas are closed under the global context.

Verdict. The cost lives in a separate cost judgment over terms, not in
`ty`. Its types (`cty`) record what FuelE can observe. They give a
closure a bound on its channel actions before it returns, a ticket
transformer, and a floor for the counters it captures. They give an end
a protocol of payload cost types and budget bounds along its points.
FuelE gains three arguments, a result type, a ticket reserve and a
frame, and `Vfuel` becomes indexed by cost types. At the thread level
the three arguments are fixed, so `fsem`, `LFP` and every protected
statement keep their text. The world field `w_pay : point → nat` becomes
`w_pc : point → cta`, the payload cost type at a carrier point, which
subsumes the floor. The fundamental theorem is one compatibility lemma
per rule plus a bind lemma. Two holes in the current FuelE block any
bind lemma, and both are checked in Rocq. `Fdef` closes FuelE under
renamings that merge two held ends (Merge.v), and the new clause of
`Fobl` holds for names of held ends (Collide.v). The repairs are an
injectivity premise on renamings and a freshness premise on the new
label, both conditions on labels or renamings. Every check of
Fragment.v except Rank and the guard becomes a local rule or goes.

### 19.1  The problem

A thread holds an end o whose partner waits, receives a closure f, and
applies it. Every channel action of f's body is an action of the
thread, so it ticks o (F-Tick). The receive clause of `Fobl` is
universal over the incoming value, and `Vfuel` at a λ asks only that the
application satisfy FuelE on the closure's own ends and its argument.
It bounds nothing about the caller. For every counter m of o there is a
closure in `Vfuel` whose body acts m + 1 times on its own end before it
returns, so the receiving thread fails F-Tick at a high enough index and
has no `fsem`. This is the gap the progress log of 2026-11-17 leaves
argued, with the example
`let (c, d) = new ∗ in spawn (λu. let () = u in close (send ⟨λy. let () = y in ∗, c⟩)); let (f, d) = recv d in let () = f ∗ in close d`
once the closure acts on an end of its own. The same gap appears without
any message. A λ-bound argument `λf. … f ∗ …` applied while the body
holds an end has no bound either, and the compatibility lemma of E-Abs
needs one. (argued. Frame.v checks the composite failure in a toy model,
`bind_needs_bound`.)

No first-order restriction is acceptable (author, 2026-11-17). The
literature handles the case in three ways, none of which is lock freedom
for a higher-order session calculus by typing.
- Padovani's lock-free system is for the linear π-calculus. Messages are
  integers, names, pairs and injections, so no received code ever runs
  (padovani2014deadlock, p3). Tickets bound how often a channel travels,
  priorities order its use, and lock freedom needs both (p2, p7).
- Padovani and Novara port the deadlock-free system to a higher-order
  language with an effect system. An arrow t →^{ρ,σ} s carries the
  latent effect σ, the levels of the channels the function uses when
  applied (padovani2015types, p7, p8). A function with latent effect ⊤,
  like their pipe, can be used only in tail position (p13). The result
  is deadlock freedom (p14), not lock freedom. The cost of §19.3 is the
  quantitative counterpart of σ, and cost ∞ in tail position is their
  ⊤ in tail position.
- PGV puts a pair of priority bounds on the arrow, T ⊸^{p,q} U
  (kokke2021prioritise, p10), and proves no lock-freedom theorem (p24).
- Program logics state liveness of higher-order code in specifications.
  Lawyer keeps obligations with finite sets of levels and degrees in a
  logical transition system (namakonov2026lawyer, p8) and inherits a
  finiteness restriction from step-indexing (p24). Lilo avoids
  step-indexing altogether (lee2025lilo, p18). D'Osualdo et al. name a
  semantic, compositional logical relation for lock freedom an open
  problem (dosualdo2026logical, p24).

### 19.2  Where the cost lives

Two placements were compared.

(A) `ty` gains a cost on `TLolli` and `TBox`. `TLolli` and `TBox` occur
710 times in 77 files (checked by grep at d9e6ceb). Every function on
types, every typing rule, the base and live relations, the translations
and the examples change, although only the fuel layer reads the cost.
FuelE would also need the session type of each held end, because a
received closure's cost sits in the payload type of the carrier. FuelE
reads no type today (§17.3), and the soup would have to carry typing
environments into it.

(B) A separate cost judgment over terms, with its own cost types. FuelE
already observes only points, counters, tickets and world data keyed by
points. A cost type records exactly that, so the cost judgment needs no
session type and no point variable. It needs the positions of an end relative to
its current point, which the primitive fixes (send and receive shift,
select and branch move to fields). `ty`, `typed`, the base and live
relations are untouched. The checker builds a cost derivation by walking
the typing derivation, which supplies the shapes, and solves for the
numbers (§19.6). Soundness never relates the two derivations.

We take (B). The price is a second description of protocols, the cost
protocols of §19.3, which mirror session types with numbers in place of
types. The world record changes one field (19.10).

### 19.3  Cost types and the semantic clauses

```
(* relation/CostTypes.v, before Worlds.v. Coinductive, because protocols
   are infinite. Vfuel recurses on the value, never on the type, and the
   checker represents the types as regular trees. *)
Abbreviation tix := (fuel * nat).     (* (s, b) is r ↦ 2^s·r + b, s = None is ∞ with ∞·0 = 0 *)
CoInductive cty :=
  | CAny                                   (* any value, the result of a thread *)
  | CVal                                   (* the unit *)
  | CPt  (ρ : cprof)                       (* a point value whose point fits ρ *)
  | CEnd (P : cpro)                        (* an end whose positions fit P *)
  | CArr (c : fuel) (t : tix) (h : nat) (σ1 σ2 : cta)
  | CBox (c : fuel) (t : tix) (σ : cta)
  | CProd (σ1 σ2 : cta) | CSum (σ1 σ2 : cta)
with cta := CTa (τ : cty) (a : fuel)      (* τ^a: a is the credit *)
with cpro :=                              (* a protocol node at the current position x *)
  | PNode (n : nat) (b : cbody) | PTop
with cbody :=
  | PSnd (σ : cta) (P : cpro) | PRcv (σ : cta) (P : cpro)
  | PSel (P1 P2 : cpro) | PBra (P1 P2 : cpro) | PCls
with cprof := Prof (P Q : cpro) (fld : nat → cprof) (suc : cprof) | PrTop.
```

A closure of type `CArr c t h σ1 σ2`, applied to an argument at σ1,
performs at most c channel actions before it returns a value at σ2, it
runs at every ticket count tk ≥ t(r) and returns with at least r
tickets, and it works for every counter of its captured ends at or above
the floor h. A box of type `CBox c t σ` does the same per force. The
credit a of σ^a is how far the counters of the ends inside lie above
their floors. An end at floor 0 and credit a has counter at least a, a
closure at credit a has captured counters at least h + a. A node
`PNode n b` at position x says that the budget at x is at least n, that
the partner's budget is finite, and what the action at x does. A send
or receive moves to x + 1, select and branch to `sel_pt x i` and
`bra_pt x i`. A point profile `Prof P Q fld suc` gives the protocols at
x and at x̄, and the profiles at x[i] and at x + 1, for `new`, `KPay`
and `KSucc`.

```
(* relation/Worlds.v. w_pay is replaced. *)
Record world := World { w_names : gset pname; w_lt : prel;
                        w_bud : point → option nat; w_pc : point → cta }.

(* pfits W x P at every depth. *)
pfits W x PTop := True.
pfits W x (PNode n b) := pt_known W x ∧ fle (Some n) (w_bud W x) ∧ w_bud W (pt_dual x) ≠ None ∧
  match b with
  | PSnd σ P => σ ⊑ w_pc W x ∧ pfits W (pt_shift 1 x) P              (* the sender's floor, at x *)
  | PRcv σ P => w_pc W (pt_dual x) ⊑ σ ∧ pfits W (pt_shift 1 x) P    (* read at the sender's point *)
  | PSel P1 P2 => pfits W (sel_pt x false) P1 ∧ pfits W (sel_pt x true) P2
  | PBra P1 P2 => pfits W (bra_pt x false) P1 ∧ pfits W (bra_pt x true) P2
  | PCls => True end.
```

`⊑` is subtyping. On arrows c, t and h are covariant, the argument is
contravariant and the result covariant. On credits, σ^a ⊑ σ'^a' asks
the current lower bound not to rise (h + a ≥ h' + a' at a closure) and
the floor h not to fall. pfits reads only data at points with the root
of x, so it is stable under `wbext` once x is known. (argued)

**FuelE.** Three new arguments. σ is the type of the value the term
returns, r the tickets it must still hold then, d the frame, the channel
actions it may still perform before it returns (None is ∞).

```
FuelE n W σ r π φ tk d e.
Fdef … := ∀ W' g π' φ', wbext W W' → kinj g π → renk g π π' → renk g φ φ' →    (* kinj is new, 19.8 *)
  fcap W' π' φ' ∧ fwait W' π' (emap g e) ∧
  (is_val (emap g e) → r ≤ tk ∧ Vfdef below (S n') W' σ π' φ' (emap g e)) ∧    (* value clause, this level *)
  ∀ α e', tstep (emap g e) α e' → Fobl … n' W' σ r π' φ' tk d α e'.
Fobl changes against LFFuel.v:
  - an action (sl_end σ = Some o): also fle (Some 1) d, and every continuation at ftick d.
  - LNew c x: only when (c, true), (c, false) ∉ dom π (19.8).
  - SSend o w at k: Vfuel n' W (w_pc W k) (mres (fends w) π) (ftick <$> mres (fends w) φ) w.
    fhand goes, its floor is inside Vfuel. ftravel stays.
  - SRecv o w at k: fin_ok without its floor, then Vfuel j W (w_pc W (pt_dual k)) πi φi w.
  - LSpawn w: the child at (CAny, ∞), r = 0, frame None, Nat.div2 (S tk) tickets, as now.
  - SLink: as now. Every other continuation keeps σ, r and d.
fsem W π t := ∃ tk, ∀ n, FuelE n W (CTa CAny None) 0 π (w_bud W <$> π) tk None t.
```

**Vfuel.** By recursion on the value, with `below` for the levels
under n. `Vfuel n W σ π φ w` at σ = τ^a.

```
CAny       True.
CVal       w = EUnit ∧ π = ∅.
CPt ρ      w = EPt x ∧ π = ∅ ∧ pt_known W x ∧ pfitpt W x ρ.
CEnd P     w = Chan c b ∧ π = {[(c,b) := x]} ∧ pfitp W x P ∧ fle a (φ (c,b))  (* counter ≥ credit *)
CArr c t h σ1 σ2
           (w = Lam eb ∨ konst_cost k (CArr c t h σ1 σ2) ∧ w = Konst k ∧ π = ∅) ∧ dom π = fends w ∧
           (∀ o, o ∈ dom φ → fle (h + a) (φ o)) ∧
           ∀ W' j φ' v πa φa, wbext W W' → j < n → dom φ' = dom π → fcap W' π φ' →
             (∀ o, o ∈ dom φ' → fle (Some h) (φ' o)) →                   (* every counter above the floor *)
             dom πa ## dom π → fin_ok W' v πa φa → Vfuel j W' σ1 πa φa v →
             ∀ r tk, meets t r tk → FuelE j W' σ2 r (π ∪ πa) (φ' ∪ φa) tk c (subst1 v eb)
CBox c t σ w = EBox eb ∧ π = ∅ ∧ ∀ W' j r tk, wbext W W' → j < n → meets t r tk →
             FuelE j W' σ r ∅ ∅ tk c (subst1 (EBox eb) eb)
CProd σ1 σ2  w = Pair u v, the maps split along fends, credit a added to both.
CSum σ1 σ2   w = Inj1 u at σ1 or Inj2 u at σ2.
```

The arrow and box clauses read the body after the β step, as `Vfun` and
V-Box of the base relation do (LogicalRelation.v, checked), and a
primitive constant is in `Vfuel` at its cost signature, as `Vfun` treats
`Konst`. The closure clause quantifies over every counter φ' above the
floor and ignores the actual φ beyond the floor check. So `Vfuel` stays
true when the counters fall, as long as they stay above h + (new credit).
This is the property the context needs when it holds a closure while
other code runs (`Vfuel_recount`, 19.7). The Kripke quantifier in the
arrow and box clauses makes `Vfuel` monotone under `wbext` (argued).

**How the soup uses it.** Every thread runs at `(CTa CAny None)`, r = 0,
d = None, so F-Tick, F-Cap, F-Wait, the spawn split and the link ticket
are the clauses the soup reads today. `step_msg` takes the payload
from the sender's send clause at `w_pc W k` and hands it to the
receiver's receive clause at `w_pc W (pt_dual (pt_dual k))`, which is the
same type (`pt_dual_dual`). The floor of `fin_ok` and `fuel_send_floor`
drop out of `step_msg`, and adequacy never read the floor. (argued
against LFSoup.v lines 2016 to 2050, checked that the floor enters only
there.)

### 19.4  The cost judgment (T2)

`Θ; Γ ⊢_W0 e : σ ▷ c ; t`, indexed by a world W0 like `typed`. Θ maps
the ends of channel constants in e to `CTa (CEnd P) (Some a)`, Γ is a de
Bruijn list of `option cta`. c is the bound on channel actions before e
returns, t its ticket transformer. An entry whose type holds no end is
unlimited. The notation is as follows.
- Γ − c ages every entry by c. An entry τ^a with possible ends needs
  a ≥ c and becomes τ^(a − c). At c = ∞ it needs a = ∞. Entries without
  ends (boxes, points, the unit) are unchanged.
- t1 ∘ t2 runs t1 first, so a composite needs t1 (t2 r). It is defined
  when t1 has a finite slope or t2 (0) = 0 (`tseq`, `seq_sound`, Tix.v,
  checked).
- 1̂ = (Some 0, 0) is the identity, ⊕ is pointwise max.
- low(σ) is the least current lower bound of the ends in σ, ∞ if none.

```
C-Unit     ⊢ EUnit : CVal^∞ ▷ 0 ; 1̂
C-Pt       pt_known W0 x, pfitpt W0 x ρ  ⟹  ⊢ EPt x : (CPt ρ)^∞ ▷ 0 ; 1̂
C-Var      x : σ ⊢ Var x : σ ▷ 0 ; 1̂
C-Ch       o : σ ⊢ Chan o : σ ▷ 0 ; 1̂
C-Abs      Θ^h ; Γ^h, σ1 ⊢ e : σ2 ▷ c ; t,   h ≤ low of every entry,   a = min (low(Θ, Γ)) − h
           ⟹  Θ ; Γ ⊢ Lam e : (CArr c t h σ1 σ2)^a ▷ 0 ; 1̂
           (·)^h restates every captured entry with current lower bound exactly h
C-App      Θ1;Γ1 ⊢ e1 : (CArr c t h σ1 σ2)^a1 ▷ c1 ; t1
           Θ2−c1 ; Γ2−c1 ⊢ e2 : σ1 ▷ c2 ; t2,   a1 ≥ c2
           ⟹  Θ1⊎Θ2 ; Γ1⊎Γ2 ⊢ App e1 e2 : σ2 ▷ c1 + c2 + c ; t1 ∘ t2 ∘ t
C-Pair, C-LetU, C-LetP
           the second part is typed under the context aged by the cost of the first,
           the first result is aged by the cost of the second, costs add, transformers compose
C-Inj      as the operand
C-Case     Θ1;Γ1 ⊢ e : (CSum σa σb)^· ▷ c0 ; t0,   Θ2−c0 ; Γ2−c0, σa ⊢ e1 : σ ▷ c1 ; t1,  (same, σb, e2, c2, t2)
           ⟹  ⊢ Case e e1 e2 : σ ▷ c0 + max c1 c2 ; t0 ∘ (t1 ⊕ t2)
C-Box      Γ unlimited, Θ = ∅,   Γ, (CBox c t σ)^∞ ⊢ e : σ ▷ c ; t   ⟹  Γ ⊢ EBox e : (CBox c t σ)^∞ ▷ 0 ; 1̂
C-Force    ⊢ e : (CBox c t σ)^· ▷ c0 ; t0  ⟹  ⊢ App EForce e : σ ▷ c0 + c ; t0 ∘ t
C-New      ⊢ e : (CPt (Prof P Q _ _))^· ▷ c0 ; t0,   P = PNode n _,  Q = PNode n' _
           ⟹  ⊢ App ENew e : (CProd (CEnd P)^n (CEnd Q)^n')^∞ ▷ c0 ; t0
C-Pay      ⊢ e : (CPt ρ)^· ▷ c0 ; t0  ⟹  ⊢ App (KPay i) e : (CPt (fld ρ i))^∞ ▷ c0 ; t0
C-Succ     the same with suc ρ
C-Send     ⊢ e : (CProd σp (CEnd (PNode _ (PSnd σ P')))^·)^· ▷ c0 ; t0,
           σp ⊑ σ with one unit of credit to spare,   P' = PNode n' _
           ⟹  ⊢ App ESend e : (CEnd P')^n' ▷ c0 + 1 ; t0
C-Recv     ⊢ e : (CEnd (PNode _ (PRcv σ P')))^· ▷ c0 ; t0,   P' = PNode n' _
           ⟹  ⊢ App ERecv e : (CProd σ (CEnd P')^n')^∞ ▷ c0 + 1 ; t0
C-Close    PCls  ⟹  CVal^∞ ▷ c0 + 1 ; t0
C-Sel_i    PSel P1 P2  ⟹  (CEnd P_i)^(n_i) ▷ c0 + 1 ; t0
C-Bra      PBra P1 P2  ⟹  (CSum (CEnd P1)^n1 (CEnd P2)^n2)^∞ ▷ c0 + 1 ; t0
C-Link     ⊢ e : (CProd (CEnd _)^· (CEnd _)^·)^· ▷ c0 ; t0  ⟹  ⊢ App ELink e : CVal^∞ ▷ c0 ; t0 ∘ (Some 0, 1)
C-Spawn    ⊢ e : (CArr c' t' h CVal^· σ')^a ▷ c0 ; t0,   a ≥ 1
           ⟹  ⊢ App ESpawn e : CVal^∞ ▷ c0 ; t0 ∘ tspawn (t' 0) 1̂
C-Konst    a primitive constant as a value, at its cost signature (KForce at CArr c t 0 (CBox c t σ) σ)
C-Sub      σ ⊑ σ', c ≤ c', t ≤ t'
C-Weak, C-Contract   on unlimited entries only
```

The rules carry what T2 asked for. The bound per held end is the credit
of its entry. Acting resets it to the budget bound n of the next node,
every other action ages it by one, which is Γ − 1 at the redex and the
cost of a subterm in the rules that sequence. A hand-over checks the
floor and one unit to spare (C-Send, C-Spawn), a link spends a ticket
(C-Link) and a spawn splits them (C-Spawn, `tspawn`, Tix.v). Application
charges the arrow's cost to everything the context holds (C-App and the
aging of the enclosing rule), λ computes it (C-Abs). A box type carries
its cost per force, its transformer, and the profiles its point
arguments need, through `CArr c t h (CPt ρ) …` for the leading λs that
take points. Recursion goes through C-Box. The self has the box's own
type, so a self call in tail position has cost c = ∞ and needs a context
that holds nothing (Γ − ∞), and a self call with a finite c is allowed
only with no actions around it. Existentials have no rule. The cost
judgment carries no points, and a received existential end brings its
protocol in the payload cost type of its carrier.

**T1, liveness.** The guard stays what it is, a condition on boxes, but
written as rules. `glive L e` mirrors `okM` constructor by constructor.
The mark context L holds the later variables, a self is later, a
subterm that performs a primitive before it returns (`gd`) clears the
marks for what follows it, and a later variable may be forced only
after that. `okM_iff : okM L e = true ↔ glive L e` makes `guarded`
(Guard.v) its instance at the root, so `gtyped`, `gptyped`,
`live_fundamental_guarded` and `live_fundamental_proc` keep their text
and `typed_live` its proof. The guard cannot move into the cost
judgment. The live relation needs `noret` of the subterm (LiveGuard.v),
and a lower bound on the actions of a received closure would have to sit
in `LVrel`, which is protected and reads no cost. (argued)

### 19.5  What happens to the checks of Fragment.v

| Check | Replaced by | Why it closes the same counterexamples |
|---|---|---|
| R1, recursion in tail position | aging by ∞ at a call of cost ∞ (C-App) | a call that never returns may hold nothing whose partner waits |
| R2-recv and fed slots | the argument floor of the self call (C-App with σ1 of the box's arrow) | an end passed to the next round must have been acted on, or its credit falls below the floor |
| hand-off graph, root graph, `stab`, `foreign`, `bleak`, `troots` | floors inside `w_pc` and the check of C-Send | a forward from carrier k to carrier m asks floor(k) ≥ floor(m) + steps + 1 locally, and a loop over the same position asks f ≥ f + 1 |
| stretch bound `scost`, `seg_len`, `stretch_len` | the credits of the context | the bound is the cost of the code between two actions, read off the rules |
| annotation `ann` and its derivations | the cost derivation itself | |
| leading `TPt` count | `CPt` arguments | a point argument is an argument |
| box check (no links in boxes) | ticket transformers (C-Link, C-Box) | a box that links per round has no transformer (`link_loop_no_tix`, Tix.v, checked) |
| `src_tickets` = 2^s·ℓ | t(0) of the main thread | |
| Rank, `wf_world (cworld Ψ)` | stays (T3) | placement per index is outside fuel (17.2) |
| guard | stays, as rules (T1) | τ-divergence is outside fuel (17.1) |

Rank stays because it is a property of the world and not of code. The
guard stays because fuel ignores internal steps on purpose (17.1).

### 19.6  Inference

The checker walks the typing derivation and emits the cost derivation
with unknowns. The shapes come from the types, the protocols from the
session types (regular, so finitely many nodes per box), the points from
the syntactic points. The unknowns are the costs c ∈ ℕ ∪ {∞}, the slopes
s ∈ ℕ ∪ {∞} and offsets b of transformers, the budget bounds n of
protocol nodes, the floors h and the credits a.

- Costs. Sequencing adds, branches take the max, a call adds the arrow's
  cost, a box's cost appears in its own body. These are inequalities
  c_i ≥ max_j (c_j + w_ij) over (ℕ ∪ {∞}, max, +). The least solution is
  computed by Bellman–Ford. A cycle of positive weight, a recursion that
  acts before its self call, gets ∞. Payload costs in `w_pc` are the max
  over the senders, the least solution again, because a smaller cost
  helps every receiver.
- Transformers. Slopes add along sequencing and take the max over
  branches, the same max-plus system. With the slopes fixed, the offsets
  satisfy b ≥ 2^{s1}·b2 + b1 and b ≥ max (2b, 2b_c − 1) at spawns, linear
  with known coefficients. A recursion that spawns gets slope ∞ and needs
  offset 0 (`spawn_loop_no_finite`, `spawn_loop_tix`), a recursion that
  links has no solution (`link_loop_no_tix`). (checked in Tix.v)
- Budgets, floors, credits. With the costs fixed, every remaining
  constraint has the form x ≥ y + k or x ≥ k with integer k, plus the
  side condition a = ∞ where the cost is ∞. That is a system of
  difference constraints, feasible iff its constraint graph has no
  negative cycle, again Bellman–Ford. The world data at constants are
  then read off the solution.

All three phases are decidable and polynomial in the size of the
derivation (argued). Padovani reduces reconstruction for priorities and
tickets to integer programming (padovani2014deadlock, p11). Fixing
costs first keeps our system out of general integer programming. Costs
are monomorphic per box. A box called at two points with different
budgets needs one bound valid at both, which every example meets
(argued).

### 19.7  The fundamental theorem

**Semantic judgment.** `Θ; Γ ⊨_W0 e : σ ▷ c ; t` holds when for every
n, every W with `wbext W0 W`, every substitution γ of values for Γ and
every injective choice of points π and counters φ for the ends of Θ and
γ, such that every value is in `Vfuel n W` at its entry, every end of Θ
fits its protocol, the counters meet the credits and the cap, and the
maps are disjoint, we have for every r and tk with `meets t r tk`

```
FuelE n W σ r π φ tk c (subst γ e).
```

**Lemmas.** All argued, F1 checked in the toy model.
- F1 `FuelE_bind`. For an evaluation context K holding πK, φK disjoint
  from the hole, if the hole satisfies FuelE at frame `Some c1` and
  result type σ1 with reserve r1, every counter of φK is at least c1,
  `fle (Some c1) d`, and for every i ≤ c1, every value v at σ1 and every
  tk' ≥ r1 the continuation K[v] satisfies FuelE at counters
  `φv ∪ ftick^i φK` and frame d − i, then K[e] satisfies FuelE at frame
  d. The hole's steps are the composite's steps. Its actions tick the
  context's counters once each, which stay positive because the frame
  bounds them by c1. Tickets flow unchanged, a spawn's child is the
  hole's child, a receive adds ends to the hole. The proof is induction
  on n. `FuelE_bind` and `bind_needs_bound` in Frame.v check the
  arithmetic of frames and context ticks for deterministic threads
  without values or renaming (checked in the toy). The real lemma needs
  the two repairs of 19.8.
- F2 `FuelE_val`. A value in `Vfuel n W σ` satisfies FuelE at σ, every
  r ≤ tk and every frame.
- F3 `FuelE_beta`. If e has exactly one step, a β, to e', then FuelE j e'
  gives FuelE (S j) e. Head β redexes are deterministic in `tstep`.
- F4 monotonicity. In the frame (`fle d d'`), the result type (⊑), the
  reserve (smaller r), the tickets (`FuelE_tk_mono`), and the index
  (`FuelE_down`).
- F5 for `Vfuel`. Subsumption (⊑), `Vfuel_wbext`, `Vfuel_down`,
  `Vfuel_rename` under injective renaming, and `Vfuel_recount`. Counters
  may change to any φ' above floor plus a smaller credit, because only
  the floor check reads φ.
- F6 `pfits` moves. A node gives the profile of its successor, and the
  refill at the successor position meets its bound n.

**Cases.** One per rule, each by F1 to F6 over the interpretation.

| Rule | Proof | Verdict |
|---|---|---|
| C-Unit, C-Var, C-Ch, C-Pt | F2. C-Pt reads `pfitpt` in W0, stable under `wbext` at a known point | holds (argued) |
| C-Abs | Floors from the captured credits, a ≤ low − h. For W' ⊒ W, j < n, counters φ' ≥ h and an argument at σ1, the body's interpretation at index j with γ extended by v gives FuelE j of `subst1 v eb`. The captured values meet their entries at φ' by F5 (`Vfuel_recount`), because Θ^h, Γ^h assume exactly the lower bound h | holds (argued) |
| C-App, closure | F1 with K = App [] e2, then F1 with K = App v1 [] and v1's ends as the context (a1 ≥ c2 keeps them positive), then the redex App v1 v2. Its Vfuel at the remaining index m gives FuelE (m − 1) of the body at the actual counters of v1, which lie above h by a1 − i2 ≥ 0. F3 lifts to m. Frames add up to c1 + c2 + c, tickets by `seq_sound` | holds (argued) |
| C-App, received closure while holding ends | the same case. The held ends are in the context of the enclosing rule, which ages them by c1 + c2 + c, so F1 there asks their credit to be at least that sum. The receive clause gives the closure at `w_pc`, whose cost is c | holds (argued) |
| C-App, primitive value | the per-constant lemma at `konst_cost`, as `Vfun` treats `Konst` | holds (argued) |
| C-Pair, C-LetU, C-LetP, C-Inj, C-Case | F1 for the first part, F3 for the β of let and case, the branch interpretations at the same index. Case takes max cost and ⊕ of transformers by F4 | holds (argued) |
| C-Box | Löb by induction on n. For j < n the body's interpretation at j with the self at `Vfuel j` (induction hypothesis) gives FuelE j of `subst1 (EBox eb) eb`, which is what the box clause asks | holds (argued) |
| C-Force | F1 for e, then the redex App EForce v. The box clause at the remaining index gives FuelE of the body one index lower, F3 lifts it | holds (argued) |
| C-New | F1 for e, then the new step with a fresh c (19.8). F2 on the pair of ends. Their counters are `w_bud W x` and `w_bud W x̄`, at least n and n' by pfits, points known by pfits | holds after the freshness repair (argued). Without it the case fails, Collide.v |
| C-Send | F1 for e, then the redex. F-Tick for the payload ends by the spare unit. The frame of the redex is 1. The payload at the ticked counters is in `Vfuel` at σ by F5 and at `w_pc W k` by pfits (σ ⊑ w_pc W k). F-Wait from the finite partner budget in the node. The end at x + 1 refilled to `w_bud W (x+1)` ≥ n', F2 | holds (argued) |
| C-Send of a closure | the same case. The closure's captured counters lose one unit at the hand-over, which the spare credit covers, and the receiver gets them at `w_pc W k` | holds (argued) |
| C-Recv | F1, then the receive clause. For every incoming value at `w_pc W (pt_dual k)`, which is ⊑ σ by pfits, and every index j ≤ n', the result pair is a value at (σ, CEnd P'^n') by F2 and F5 | holds (argued) |
| C-Close, C-Sel, C-Bra | as C-Send without payload. Branch by the generic clause of `Fobl` | holds (argued) |
| C-Link | F1, then the link clause. `link_split` (Tix.v) gives 1 ≤ tk and the reserve at tk − 1 | holds (argued, arithmetic checked) |
| C-Spawn of a closure | F1, then the spawn clause. `fhand 0` by credit a ≥ 1. The child at ⌈tk/2⌉ ≥ t'(0) by `spawn_split` (Tix.v). Its FuelE at index n' comes from the closure's Vfuel at the current index, the body at counters φ − 1 ≥ h, lifted by F3, its frame weakened from c' to None and its result type to CAny by F4. The parent at ⌊tk/2⌋ meets the reserve | holds (argued, arithmetic checked) |
| C-Pay, C-Succ | F3 on the β step, F2 with the field or successor profile | holds (argued) |
| C-Konst | the per-constant lemma, each primitive one redex | holds (argued) |
| C-Sub, C-Weak, C-Contract | F4, F5. Unlimited entries carry no ends, so duplicating or dropping them changes no map | holds (argued) |
| existentials | no rule. The payload's protocol is in its carrier's `w_pc` | nothing to check |

**Assembly.** `ctyped_fsem`. From `Θ; [] ⊢_W0 t : σ ▷ c ; t0` and a world
W ⊒ W0 in which the ends of Θ sit at known points that fit their
protocols, with credits at most the budgets, the semantic judgment at
γ = id, r = 0 and the full counters `w_bud W <$> π` gives FuelE at frame
c, result σ and tk = t0(0). F4 weakens to frame None and result CAny,
which is `fsem W π t`. Then

```
Inductive lfptyped : world → senv → proc → ty → Prop :=
  | lf_term W Σ ΘB C0 t T Θc σ c t0 :
      (the premises of pt_term) → guarded t →
      ctyped W Θc [] t σ c t0 → cfits W Θc (tenv_points (tenv_of Σ ∪ ΘB)) →
      lfptyped W Σ (C0, {[+ t +]}) T
  | lf_connect … (the premises of pt_connect over lfptyped)
  | lf_join …    (the premises of pt_join over lfptyped) → wbud_agree W1 W2 → lfptyped (wjoin W1 W2) …
Theorem lf_fundamental W Σ p T : lfptyped W Σ p T → strict W → LFP W Σ T p.
Theorem lf_soundness W T p : lfptyped W ∅ p T → world_wf W → well_founded (w_lt W) → lock_free p.
```

`lf_fundamental` is induction on `lfptyped`. `lf_term` gives `LFP_term`
with `lsem_typed` from `live_fundamental_guarded`, the known points from
`cfits`, and `fsem` from `ctyped_fsem`. `lf_connect` and `lf_join` give
`LFP_connect` and `LFP_join`. `lf_soundness` is `lf_fundamental` and
`lf_adequacy`. (argued)

### 19.8  Holes found

1. **Merging renamings (checked, Merge.v).** `renk g π π'` lets g send
   two held ends with the same bit, point and counter to one name. `Fdef`
   then asks FuelE of the merged thread, which acts twice on one end and
   so reads world data at x + 1 that the thread never reads.
   `merge_no_fuel` shows a thread that holds c1 and c2 at x and sends a
   payload on each has no fuel at any index from 2 on whenever
   `w_pay W (x+1) ≥ 4`.
   Its own runs read only `w_pay W x`. Each half of that thread is the
   hole or the continuation of the other, so no bind lemma holds for the
   current `Fdef`. The soup renames only injectively (`kinj`, LFSoup.v,
   checked). Repair. `Fdef` quantifies over g with `kinj g π`.
   `FuelE_rename` gains that premise, which the soup's only use already
   supplies.
2. **New with a held name (checked, Collide.v).** `Fobl` at `LNew c x`
   holds for every c, also a c the thread already holds. The fresh end
   then overwrites the held one in π, and a later action on the held end
   reads the data at x. `collide_no_fuel` shows a thread that holds
   (c, pt_pol x) at y and runs new@x before a send on it has no fuel
   whenever `w_pay W x ≥ 5`. The C-New case of 19.7 fails without a
   repair. The soup creates only fresh channels. Repair. The new clause
   asks `(c, true) ∉ dom π ∧ (c, false) ∉ dom π`, a condition on the label
   against the thread's own map. The soup's freshness gives it, through
   `lf_closed` and the side condition of the process rule for new
   (argued, to be confirmed in stage H1).
3. **Off by one at the value and the call (argued).** The value clause
   must read `Vfuel` at the level of the expression, not one below, or
   F1 loses an index each time a hole returns. The arrow and box clauses
   must give FuelE of the body after the β step, or C-App and C-Force
   lose an index at each call. Both are definitional, 19.3 fixes them,
   and the base relation already has the second form.

Hole 1 and 2 are in today's LFFuel.v, independent of costs. Any
compositional proof of stage L6 meets them.

### 19.9  The examples

Costs as the rules compute them, at budgets uniform per program. B is
the least uniform budget bound, f the floors in `w_pc`, tk the main
thread's tickets t(0). Not checked against Rocq, read off the example
headers and the rules.

| Example | Costs | Verdict | Rule |
|---|---|---|---|
| Forwarder | boxes `fwd`, `fprod`, `fcons` have arrows of cost ∞, called by spawn in tail position. B = 2, f = 1 on a, f = 0 on b | types | the forward on b asks 1 − 1 ≥ 0 at C-Send |
| TailCall | both boxes cost ∞, tail calls, no other held end. B = 1, no floors | types | |
| CfstScheduler | each end is acted on within a round of 6 actions (17.5). B = 6 | types | |
| Scheduler (links) | ag₁ is a spawned λ with transformer (Some 0, 1). main's need is tspawn 1 (tspawn 0 1̂) at 0, which is 1 ticket. ag₂ holds r₂ across two actions on r₁ after a hand-over, B = 3 | types | C-Link, C-Spawn |
| ABP | three boxes of cost ∞, tail calls. bob's second end waits two actions, so its argument floor is 2, and main hands it over once, B = 3 | types | |
| GrowRing | ring calls are spawned, cost ∞. z arrives at the floor, is ticked by the close of x and handed to a call that receives on it first, so f = 2. a waits one hand-over and its own send, B = 4 | types | |
| ReceivedChain | the received end is ticked by the close of c and spawned into a call that acts on it first, f = 2. The sender's e′ waits two actions and a hand-over, B = 3 | types | |
| callback server | `srv = !(f = λc. let (cb, c) = recv c in let () = cb ∗ in (force f) c)`, clients send `λu. let () = u in close (send ⟨∗, k⟩)` with k fresh. The callback has cost 2, floor 0, sent at credit 1. srv's c is refilled at the receive and aged by 2 before the next round, B = 2 | types | C-App charges 2 to c |
| server running a callback of cost ∞ | the same server with `w_pc` at cost ∞ | rejected | aging by ∞ at C-App. Spawning the callback types |
| Sync | one receive, one spawned send. B = 1 | types | |
| controller (§7) | budget ∞ at ctl, semantic proof only | outside the static system, as today | |
| KobForwarder | | rejected | Rank (`kob_cworld_not_wf`) and the guard |
| C1, C1′ | | rejected | Rank on syntactic points (`c1_rank_fails`) |
| C3 | a link per round | rejected | no transformer (`link_loop_no_tix`) |
| starving server | the same end forwarded every round along the same position of one carrier | rejected | C-Send asks f ≥ f + 1 at that position |
| postponement (liveness.md §9) | A acts on b every round and holds a | rejected | a passed to the self call loses credit every round below the argument floor, or, held across a call of cost ∞, fails aging by ∞ |

### 19.10  Stages and statements

One agent per stage, at most two at once.

- **H1, definitions (one agent).** relation/CostTypes.v (`cty`, `cta`,
  `cpro`, `cprof`, `tix`, `meets`, `tseq`, `tspawn`, ⊑, aging, `pfits`,
  `pfitpt`). In Worlds.v `w_pay` becomes `w_pc`, `wext_bud` and `wbext`
  keep `w_pc` on known names, and the world builders in BranchWorlds.v,
  Creation.v, PointRenaming.v, PNWorld.v, DropCounter.v change one
  argument (about 50 lines, checked by grep). In LFFuel.v, FuelE with σ, r,
  d, `kinj` in `Fdef`, freshness at new, the value clause at its level,
  `Vfuel` typed with the clauses of 19.3, the old lemmas restated.
  LFSoup.v, LFAdequacy.v, LFCompose.v at σ = CAny, r = 0, d = None,
  `step_msg` without the floor, `wbud_agree` over `w_pc`.
- **H2, the cost judgment, beside H1 once CostTypes.v is fixed.**
  static/CostTyping.v (`ctyped`, the rules of 19.4), the cost
  derivations of the examples of 19.9 in examples/LockFree.v, and the
  rejections of C3 and the starving server as non-derivability lemmas.
- **H3, the semantic lemmas.** lockfree/LFFuelBind.v with F1 to F6.
- **H4, the compatibility lemmas, beside T1.** lockfree/CostFund.v, one
  lemma per rule of the table in 19.7, and `ctyped_fsem`.
- **T1, beside H4.** liveness/GuardRules.v with `glive` and `okM_iff`.
- **H5, assembly.** lockfree/LFTyped.v with `lfptyped`, `lf_fundamental`,
  `lf_soundness`, the example theorems. Fragment.v keeps only `cworld`,
  `wf_world` and the rank lemmas (`kob_cworld_not_wf`, `c1_rank_fails`),
  moved to lockfree/Rank.v. The rest of Fragment.v goes (`pcall`, `r1`,
  `r2x` and its three instances, `box_ok`, `hops`, `bleak`, the root
  graph, `scost`, `seg_len`, `stretch_len`, `with_budgets`, `src_world`,
  `src_tickets`, `tk_cover`, `ann`, `lfsource`, the old `lfptyped`), and
  LFFuelTyped.v goes whole.
- **H6, optional.** The checker of 19.6 in theories/algorithmic.

Protected statements. None changes its text. `lf_adequacy`, `LFP_term`
(as at d9e6ceb, with the known-points premise), `LFP_connect`,
`LFP_join`, `lf_criterion`, `lock_free`, `thread_progress`, the live
theorems, `fundamental`, `adequacy` and the soundness family stay as
they are. What changes under them is the world record (`w_pay : point →
nat` becomes `w_pc : point → cta`, as 17.8 changed it before), the
meaning of `wbext`, `wext_bud` and `wbud_agree` (they also keep `w_pc`),
and the definitions of FuelE, `Vfuel` and `fsem`, whose types stay the
same at the thread level. `lf_fundamental` and `lf_soundness` are new.
Decision for the author. The world field, and the two repairs of 19.8,
which are conditions on renamings and labels and read no syntax.

### 19.11  Deviations (H1)

Stage H1 states the definitions of 19.3 in Rocq. Where the text above
does not typecheck or leaves a choice open, the Rocq files decide as
follows.

1. **Where pfits lives.** relation/CostTypes.v comes before Worlds.v,
   because the world record holds a `cta`. It cannot mention a world,
   so it states `pfits_at kn bud pc` and `pfitpt_at` over the three
   functions they read. LFFuel.v instantiates them as `pfits W` and
   `pfitpt W` with `pt_known W`, `w_bud W` and `w_pc W`.
2. **Subtyping.** ⊑ is `cst` (notation `⊑c`), coinductive and mutual
   with `cst_ty`, `cst_pro`, `cst_body` and `cst_prof`. The name `csub`
   is taken by Instr.v. Credits follow 19.3. A target `CAny` ignores
   the credit, an arrow asks h ≤ h' and h' + a' ≤ h + a, every other
   type asks a' ≤ a. On protocols the budget bound of a node may fall,
   a send payload is contravariant and a receive payload covariant.
   Aging is the relation `cage c σ σ'`, with `cfree τ` as finite
   evidence that τ holds no end.
3. **Constants.** `Vfuel` reads no `konst_cost` table. A constant is in
   `Vfuel` at an arrow type when its map is empty and the arrow clause
   holds for the redex `App (Konst k) v`, its own step, in place of the
   body after a β. The cost signature of each constant is then a lemma
   of H4, not a syntactic premise of the relation.
4. **Shape of the clauses.** `Vfuel` has no ticket argument. The end
   clause reads `φ !! (c, b) = Some f ∧ fle a f`. The send clause of
   `Fobl` reads `∀ k, π !! o = Some k → Vfuel n' W (w_pc W k) …`. The
   frame check sits with F-Tick, `ftick_ok o φ ∧ fle (Some 1) d`, and
   `dupd d α` is the frame after a step. The value clause is
   `is_val (emap g e) = true → r ≤ tk ∧ Vfdef … (S n') …`. The new
   clause is an implication with the two freshness premises.
5. **Thread level.** `FuelT n W π φ tk e` abbreviates
   `FuelE n W cany 0 π φ tk None e`, with `cany = CTa CAny None`. The
   default `w_pc` of `wgen` is `cany`, which constrains no payload.
6. **Soup.** The freshness of the new clause comes from the soup's
   invariant that no thread holds an end of a channel outside `C`
   (`Hnm`, from `lf_closed`), confirming 19.8 hole 2. `step_msg` reads
   the payload at `w_pc W k` from the sender and hands it to the
   receiver at `w_pc W (pt_dual (pt_dual k))` by `pt_dual_dual`.
   `fhand_fin_ok` becomes `fchild_fin_ok` without a floor.
   `fuel_zero_nosend` goes. It read the send floor, and F-Tick alone
   does not exclude an end at 0 sent on itself. Nothing used it.
7. **Fragment.v and LFFuelTyped.v.** `with_budgets` sets `w_pc` to
   `cany`. The floor of 17.6 stays a function of the program,
   `src_pay t k`, and the budget theorems of the examples state
   `src_pay` where they stated `w_pay`. These parts go in H5.
   LFFuelTyped.v builds with the new arities.

### 19.12  Deviations (H2)

Stage H2 states the cost judgment of 19.4 in static/CostTyping.v and
the derivations of 19.9 in examples/CostEx.v. The judgment is
`ctyped W Θ Γ e σ c t`, with Θ a `gmap cend cta`, Γ a `list (option
cta)`, c a `fuel` and t a `tix`. It has one constructor per rule,
named `C_Unit` to `C_Contract`. Where the text of 19.4 does not
typecheck or leaves a choice open, the Rocq file decides as follows.

1. **Leaves and structure.** C-Unit, C-Pt, C-Var, C-Ch, C-Konst and
   C-Box allow unlimited entries beside the ones they read, which is
   weakening at the leaves. A split may send an unlimited entry to both
   sides, as `lenv_split` of Typing.v does. C-Weak and C-Contract stay
   as rules.
2. **Capture.** "h ≤ low of every entry, a = min low − h" and the
   restatement (·)^h are one relation `ccap h a σ σ'`. It asks h + a
   to lie below the current lower bound of σ and restates σ at lower
   bound h. An end gets credit h, a closure with floor h0 ≤ h gets
   credit h − h0, a pair restates its components. a is any credit with
   h + a below every lower bound, not the largest one, because C-Sub
   lowers it anyway. There is no function low. The cost types are
   coinductive, so `ccap` recurses on the finite top of a type.
3. **Credits of results.** C-Pair, C-Inj, C-New, C-Recv and C-Bra give
   their product or sum the credit 0, not ∞. The credit of a pair is
   added to both components (`cadd`, the pair clause of `Vfuel`), so ∞
   there would give the ends credit ∞.
4. **Aging and CAny.** Γ − c is `cage_env`, built from `cagex`, which
   is `cage` of CostTypes.v plus one condition. An entry whose type may
   hold a `CAny` value ages only by 0 (`cheld`). `Vfuel` at `CAny` is
   `True`, so the credit of such an entry bounds no counter, and `cage`
   alone would let a context hold it across an action. H4 meets this
   hole if the condition goes.
5. **Composition.** Every rule that composes transformers carries
   `tok t1 t2`, the premise of `seq_sound`. `tseq` is total, and it is
   sound only there. C-Case uses `fmax` for the costs and `tmax` for ⊕.
6. **Nodes and profiles.** The rules read a protocol node by
   `pnode P = Some (n, b)` and a profile by `pprof`, `pfld` and `psuc`.
   An equation P = PNode n b does not follow by computation for a
   cofixpoint constant, and `pnode` unfolds it. C-Pay and C-Succ at
   `PrTop` give `PrTop`.
7. **Small choices.** C-Spawn reads t′(0) as `snd t′`, which is the
   need at 0 for every transformer. C-Sel is one constructor over the
   bit, C-Inj two. C-Pt reads `cpfitpt W`, which is `pfitpt W` of
   LFFuel.v by definition, so that CostTyping.v does not import the fuel
   layer. `konst_cost` is a relation from constants to arrow types, one
   constructor per constant, with the conditions of the matching rule.
   C-Konst gives a constant credit ∞. C-Force and the other rules for an
   applied constant stay beside C-Konst and C-App.

**Examples.** The derivations are built by the tactic `ct` from the box
types and the protocols. Each lemma takes as hypotheses that the world
knows each point literal and that it fits its profile, the premise of
C-Pt. The numbers differ from the estimates of 19.9 in two places.

| Example | Lemma | c, t of main | Budgets |
|---|---|---|---|
| sync | `sync_ctyped` | 2, (1, 0) | 1 |
| tail call | `tc_ctyped` | ∞, (1, 0) | 1 |
| forwarder | `fw_ctyped` | ∞, (3, 0) | B = 3, payload channel 2, floors 1 and 0 |
| received chain | `rc_ctyped` | ∞, (2, 0) | B = 3, floor 2 |
| ABP | `abp_ctyped` | ∞, (2, 0) | B = 3, bob's floors 0 and 2 |
| cyclic scheduler (CFST) | `cs_ctyped` | ∞, (5, 0) | B = 6 (5 suffices), follower floors 0, 2, 3 |
| scheduler with a link | `sched_ctyped` | 4, (2, 1) | B = 3, main needs 1 ticket |
| callback server | `cb_ctyped` | ∞, (1, 0) | B = 2, client transformer (∞, 0) |
| GrowRing, by C-SpawnLam | `rg_ctyped` | ∞, (3, 0) | B = 4, payload floor 2, floors 0 and 1 |

The forwarder needs B = 3, not 2. Its spawned call captures a after one
action and b just refilled at a single floor, B − 2, and the next round
needs b at credit 1 for the receive on a. The callback client spawns
before its tail call, so its transformer has slope ∞ and offset 0, as
19.6 predicts for a recursion that spawns. The callback server is new,
`cb_main` in CostEx.v. It has no ordinary typing derivation yet.

**GrowRing does not type under C-Spawn.** This is structural. A closure has one floor
h for every end it captures (`farr`, 19.3), and inside its body each
captured end has credit exactly h. The second spawned call of `ring`
captures z, received at the payload floor fd and aged by the close of
x, together with the fresh b′, and passes b′ as the next y. So the
floor fy of the y argument is at most fd − 2. The first spawned thunk
captures the fresh a with y and sends a on y, so fy ≥ fs + 2, where fs
is the payload credit of the send. `pfits` gives fd ≤ fs. Together
fy ≤ fs − 2 < fs + 2 ≤ fy. Every end of the ring acts, so no budget is
∞ and no credit escapes the arithmetic.

**Decision, C-SpawnLam (2026-11-17, under the author's overnight
delegation).** A literal λ under spawn gets its own rule beside C-Spawn.

```
C-SpawnLam   Θ − 1 ; (Γ − 1), CVal^a ⊢ e : σ′ ▷ c′ ; t′
             ⟹  Θ ; Γ ⊢ App ESpawn (Lam e) : CVal^∞ ▷ 0 ; tspawn (t′(0)) 1̂
```

The rule is `C_SpawnLam` in CostTyping.v. Its premises read the body of
the λ and the context only. The child runs the body at the counters of
the hand-over, one below the parent's (`fchild`), so the body sees each
end at its own credit minus one and no common capture floor arises.
Aging by one also gives `fhand 0`. C-Spawn stays for spawned values of
arrow type, and the derivations of the other examples keep it. GrowRing
types with it (`rg_ctyped`, B = 4 as 19.9 estimated). Per-end floors on
arrows are the general alternative, for closures that are stored or
sent before they run. They are left for later.

**Obligations of H4 from H2.** H4 proves the compatibility lemma of
C-SpawnLam. The child's FuelE at index n′ is built from the derivation
of the body at the ticked counters, lifted over the β step of
`App (Lam e) EUnit` by F3, weakened to frame None and result `cany` by
F4. H4 also handles deviation 4. An entry that may hold a `CAny` value
ages only by 0 (`cheld` in `cagex`), and the compatibility lemmas of
the sequencing rules rely on that condition.

**Rejections.** Non-derivability of a whole term needs inversion
modulo C-Sub, C-Weak and C-Contract, which H2 does not prove. The
lemmas state the rejection at the rule that rejects.
`c3_link_loop_not_tix` shows that no transformer t with
link ∘ t ≤ t has a finite need at 0 (C3). `cb_inf_not_aged` shows that
no end with finite credit ages by ∞ (the server running a callback of
cost ∞). `starve_not_spare` shows that C-Send cannot hand an end on at
the floor it arrived at (the starving server).

### 19.13  Deviations (H3)

Stage H3 proves F1 to F6 in lockfree/LFFuelBind.v. F1 is false for the
definitions of H1, and so is `Vfuel_rename`, on which F2 rests. Four
repairs make them hold. Each is a condition on a step label or on the
value a label carries, read against the thread's own map, and none
reads a type or a term.

1. **A send hands on held ends and not its subject.** The send clause
   of `Fobl` gains `fends w ⊆ dom π ∖ {[o]}`. Without it a hole may send
   an end that its context holds and its own map does not. The
   composite drops that end from its map, and the continuation acts on
   an end it no longer holds. A send of the subject on itself makes
   `fact` skip the tick of the other counters while the frame still
   falls, so the context's counters would no longer match the ticks the
   continuation is given. Linearity excludes both in typed programs.
2. **A spawn and a link hand on held ends.** The spawn clause gains
   `fends w ⊆ dom π` and the link clause `cd ⊆ dom π`, for the same
   reason.
3. **Select and branch need `fsolo`.** The continuation of a select or
   branch on o is asked only when the thread holds no other end of the
   channel of o (`fsolo π o`), a premise like the freshness of new.
   Select moves its end to bit false and branch to bit true. When the
   context holds the partner end, the moved end takes the partner's
   name and overwrites its entry in the map. A select or branch never
   synchronises with its own thread, so the soup supplies the premise
   from `st_disj`. `lffuel_step` and `fuel_one` gain the hypothesis,
   `step_sel` proves it in four lines per side.
4. **A pair splits its points.** The pair clause of `Vfuel` gave the
   components `mres (fends u) π`. A renaming injective on the held ends
   may map an unheld end inside a box onto a held end of the other
   component. The box then receives a nonempty map and fails `π = ∅`,
   so `Vfuel_rename` fails. The clause now splits π into disjoint parts
   `π1 ∪ π2`, one per component, and restricts the counters to each
   part (`mres (dom π1) φ`). H4 builds pairs with `Vfuel_pair`.

The H1 lemmas keep their statements except `lffuel_step`. New in
LFFuel.v are `fsolo`, `fuel_send_held`, `fuel_spawn_held` and
`fuel_link_held`. In CostTypes.v H3 adds `cst_refl`, `cst_trans`,
`tle_refl`, `tle_trans`, `cst_cadd`, `pfits_at_mono`, `pfitpt_at_mono`,
`pfits_at_cst` and `pfitpt_at_cst`.

Three choices of form matter for H4.

- **The continuation of F1 is closed under renamings.** FuelE
  quantifies over renamings injective on the held ends, so `fkont`
  asks the continuation for every such renaming of the context,
  `efill (kemap g K) v`. The semantic judgment of H4 should therefore
  quantify over injective renamings of the ends of Θ, or be proved
  closed under them, so that the continuation of each rule meets
  `fkont`.
- **Recount is a relation.** `Vfuel_recount` restates a value at a
  lower bound m through `clow m σ σ'`, which sets an end's credit to m,
  a closure's credit to m − h, and leaves types without ends alone. It
  is the restating Θ^h of C-Abs. `Vfuel_minus` pays i ticks of the
  counters from i units of credit, for the spare unit of C-Send and
  C-Spawn.
- **F3 is stated for head β steps in a context.** `FuelE_beta` lifts
  FuelE of `efill K e'` at n to `efill K e` at n + 1 when e head-steps
  by β to e′, and `head_beta_det` shows that such a redex has exactly
  this step under every renaming.

`Vfuel_rename` at a closure renames the argument out of the way of the
closure's channels by a fresh prefix (`sprefix`, `sunfix`), runs the
body there and renames it back with `FuelE_rename`. F4 and the
subsumption half of F5 are one induction on the index (`sub_mono`),
because the closure clause reads FuelE below its level and the value
clause of FuelE reads `Vfuel` at its own level.

### 19.14  Deviations (H4)

Stage H4 proves the fundamental theorem of the cost judgment in
lockfree/CostFund.v. The semantic judgment is `csem W Θ Γ e σ c t`. It
holds when FuelE n holds of `subst γ (emap g e)` at result σ, frame c
and every reserve and ticket count that meet t. This must hold for
every index n, every W′ ⊒ W, every renaming g of channels injective on
the ends of Θ, every substitution γ, and all points and counters that
fit Θ and Γ. The ends of Θ fit by `thsem`, which places each renamed end
at one point in `Vfuel` at its entry. The values of Γ fit by `gsem`,
with one disjoint part of the points per entry and the counters of that
part. The counters cover exactly the points and lie under the cap in
every extension. Five changes to H1 to H3 and one removal from H2 make
the case lemmas hold. A lemma that is false, or that has no proof,
forced each of them.

1. **Closure arguments and captures (relation).** `farr` asked `fin_ok`
   of the argument and `fcap` of the captured counters. An application
   cannot supply `fin_ok`. The value a hole returns comes with `Vfuel`
   only, with neither its points known nor its map equal to its ends.
   The body's FuelE needs the cap in every extension, and `fcap` at one
   world does not give it. The arrow clause now asks `farg`, a value
   with counters on exactly its points under the cap in every
   extension, and `fcap_ext` of the captured counters. Both premises
   are what a caller holds. `fcap_ext` moved from LFFuelBind.v to
   LFFuel.v.
2. **Ends at known points (relation).** The send clause asks
   `ftravel`, finite partner budgets for the ends of the payload. An end
   at protocol `PTop` and the ends a closure captures carried no such
   fact. `Vfuel` at an end and at a closure now asks `fpts W π`, every
   held end at a known point whose partner has a finite budget. New,
   receive and the refill after an action provide it. `Vfuel_end` gains
   the two premises.
3. **Boxes hold no end (relation).** C-Abs must show that the map of a
   closure is its ends, and a captured box could hide channel constants
   under its empty map. The box clause now asks `fends eb = ∅` beside
   `π = ∅`, as the closure clause asks `dom π = fends w`. Typed boxes
   hold no channel constant, because C-Box types the body with Θ = ∅.
4. **No constant at an arrow type (relation and typing).** The constant
   clause of 19.11 item 3 gave the redex `App (Konst k) v` FuelE only
   below the level of the value, one index short of what an application
   needs, and C-App is false for it. Take Γ with x at an arrow to `CVal`
   of cost 1 and y at a pair of the unit and a sending end. The
   substitution x ↦ send meets `Vfuel 2`, while `App send y` has no
   `FuelE 2`, because the end it returns is no unit. Reading the redex
   one step later fails for force, whose box argument then sits one
   level too low. So `Vfuel` holds no constant at an arrow type, and
   C-Konst and `konst_cost` go. A constant passed as a function is
   written λx. k x and typed by C-Abs over the rule of k, so no program
   is lost up to η. There are no per-constant soundness lemmas. The
   redex of each constant has its own lemma (`send_redex`, `recv_redex`
   and so on), which the rules for applied constants share.
5. **The continuation of F1 gets the cap in every extension (lemma).**
   `fkont` gave the returned value `fcap` at one world, and the
   continuation must prove FuelE, which asks the cap in every extension.
   `FuelE_bind` supplies `fcap_ext` from the hole's FuelE, and `fkont`
   now asks for it. No file outside LFFuelBind.v reads `fkont`.
6. **Syntactic facts at C-Abs, C-Box and C-SpawnLam (proof).** The map
   of a closure or a box must equal its ends, and `csem` cannot see
   them, because it reads no term. The three lemmas take
   `cfacts Θ Γ e`. The ends of e are those of Θ, its free variables have
   entries, and every entry that may hold an end occurs. Every
   derivation gives these facts (`ctyped_cfacts`), and `csem` stays free
   of syntax.

The proof follows 19.7. Three bind lemmas carry the sequencing.
`sem_bind0` runs a hole that holds the whole environment, `sem_bind1` a
hole beside the rest of the environment, which ages by the hole's cost,
and `sem_bind2` a hole beside a value an earlier hole returned. Each is
F1 with the context renamed, moved to the later world and aged
(`env_cont`). A value whose type has no `CAny` at its top holds exactly
its ends, at known points, with counters at least its credit
(`Vfuel_held`). This is where the `cheld` condition of 19.12 item 4
enters. C-Box is Löb by induction on the index. C-SpawnLam builds the
child from the body's judgment at the ticked counters, lifts it over the
β step and weakens it to frame ∞ and result `cany`, as 19.12 asked.

`ctyped_fsem W0 Θ e σ c t W π` turns `ctyped W0 Θ [] e σ c t`,
`wbext W0 W` and `cfits W Θ π` into `fsem W π e`. `cfits` asks that π
covers Θ and that every end, refilled to its budget, is in `Vfuel` at
its type at every index. `cfits_end` derives it for an end whose
protocol fits at a known point with credit at most the budget.
examples/CostFsem.v gives sync and the callback server `fsem W ∅` from
their derivations (`sync_fsem`, `cb_fsem`).

### 19.15  Deviations (H5)

1. **`lf_term` asks H4's `cfits` (premise).** The prep branch stated
   `cfits` in protocol form. Each end has a type `CTa (CEnd P) a` whose
   protocol fits at its point, with credit at most the budget. That form
   misses the finite partner budget that `Vfuel` asks of every end
   (`fpts`), because `pfits` gives it only below a node and `PTop` fits
   everywhere. `lf_term` therefore asks `cfits` of lockfree/CostFund.v,
   as 19.7 wrote it, and the separate premise of known points goes,
   because `cfits` contains it. The protocol form is `cfits_pf`, with
   `w_bud W (pt_dual x) ≠ None` added, and `cfits_pf_cfits` derives
   `cfits` from it and known points through `cfits_end`.
2. **Two-world composition only (rule).** As the prep branch recorded,
   `lfptyped` has one composition rule, `lf_connect`, in the form of
   P-Join with `wbud_agree`. `LFP_connect` lands in `wjoin W1 W2`, and
   `LFP` has no lemma from `wjoin W W` back to W.

`lf_fundamental` is induction on `lfptyped`, and `lf_soundness` is
`lf_fundamental` with `lf_adequacy`, as 19.7 argued. Neither takes a
hypothesis.
