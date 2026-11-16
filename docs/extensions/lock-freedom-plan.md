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
