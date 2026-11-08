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
