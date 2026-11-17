# Redesign proposal: deadlock and lock freedom from one order and one fuel

State read on 2026-11-17, branch `lock-freedom` at f3dd2fa with LFTyped.v
and Rank.v from lf-h5prep. This document changes no Rocq file. It is the
basis for a rewrite from the ground up. "Checked" marks a claim checked
against a definition or a Rocq lemma of that state, "argued" a claim argued
on paper here or in the plan, "to prove" a lemma the rewrite has to supply.

Notation. Ends c⁺ and c⁻ of a channel c. Points x, the dual point x̄, the
shift x⁺, the field x.κ. World W with order ≺_W. Term environment Θ,
process interface Σ, future F. N is the refill of the fuel layer.

## 0  The proposal in brief

The development carries one idea. An order on points rules out circular
waiting, and a well-founded order with a uniform placement also rules out
waiting chains that grow forever. A counter per held end, refilled when the
holder acts on it, rules out endless postponement and endless hand-over.
Everything else is either one of these two devices or an artefact of how an
earlier decision forced them into the mechanization.

The redesign keeps the two devices and cuts every coupling between them.

1. Points carry the order and nothing else. Budgets leave the world. The
   fuel layer reads no point and no world.
2. Programs never mention a point. A `new` either creates at a fresh
   generated root, whose facts are the fixed laws of the world, or creates
   at a field x.κ of the point x of an end the thread holds (anchored
   creation). Placement is a function of the run, so it is the same at every
   step index, which is what lock freedom needs (§4).
3. Channels and points are disconnected. A channel has two named ends c⁺ and
   c⁻. The environment maps an end to a session type at a point. `new` is the
   only place where an end receives a point.
4. The relation reads no syntax except one fact about steps. The operational
   semantics labels a send and a spawn with the set of ends the step moves.
   Every other syntactic clause goes, and with it the constant cases of V.
   Constants are derived λ-values, so a constant passes as a function.
5. One generic relation, parametric in a cost table, gives both the
   deadlock-freedom relation and the live relation.
6. Fuel is one per-thread predicate with a single refill constant N, per-end
   counters, per-thread link tickets, and cost protocols that carry the
   payload floors. Cost protocols are chosen per index like session types,
   because adequacy never reads them.
7. The lock-free judgment is a soup of threads, each in the live relation
   and in the fuel predicate, with ownership, points, counters and tickets
   fixed outside the index. Adequacy is the existing type-free criterion.

## 1  Inventory of decisions

Verdicts. **E** essential. **C(X)** consequence of decision X, revertible as
the last column says. **Q** quirk, to remove. File references are to
theories/ unless they name docs/.

### 1.1  Calculus and semantics

| # | Decision | Where | Verdict |
|---|---|---|---|
| K1 | GV calculus with `new`, `spawn`, send, receive, close, link, select and branch as constants, de Bruijn terms, channels as names | lang/Syntax.v:128-150 | E, except that constants are values (K2) |
| K2 | Primitive constants are values of arrow type and step as `App (Konst k) v` | lang/Syntax.v:128, lang/Semantics.v:62 | Q. Make primitives saturated operators and define each constant as the λ-value λx. op x (§3.2) |
| K3 | Both ends of a channel share the name c and a value carries a polarity bit, `Chan c b` with b = `pt_pol` of the end's point | lang/Syntax.v:145, relation/LogicalRelation.v:146-149 | Q (quirk A2). Two end names c⁺, c⁻ independent of points |
| K4 | Point values `EPt x`, `KPay i`, `KSucc`, and `new` takes a point value | lang/Syntax.v:136-148, lang/Semantics.v:62-70 | C(F5, uniform placement). Replaced by placement rules (§2.5) |
| K5 | Scope extrusion in the semantics, `sentc` removes `fchans v` from C at an external send | lang/Semantics.v | E. The relation agrees with it through transfer sets (§2.7) |
| K6 | Instrumented semantics with thread identifiers, labels are sets of participants, the event is read back off the redexes | lockfree/Instr.v, LFSoup.v:388-432 | thread ids E. Read-back Q (quirk F2). Labels carry the event |
| K7 | Weak fairness per thread, no select and no mixed choice | lockfree/Fair.v:31 | E (scope, plan §11) |
| K8 | Two notions of waiting, `waits` by mention and `hwaits` by ownership | lockfree/Fair.v, LFSoup.v:2654 | Q (quirk A3). Keep only the run criterion with an ownership dependency |

### 1.2  Points and worlds

| # | Decision | Where | Verdict |
|---|---|---|---|
| W1 | End points. Each end has its own point, x and x̄, and the gate asks u ≺ v̄ | lang/Syntax.v:33-37, relation/Readiness.v:79-92 | E |
| W2 | No aliases (no-eq). `w_eq` is equality | relation/Worlds.v:41 | E. The abbreviation and the eight `wf_eq_*` lemmas go (quirk G5) |
| W3 | Points are roots with offsets and fields, (p,b)[i] | lang/Syntax.v:28-37 | E. Fields are labelled x.κ |
| W4 | A world is a support of root names and a transitive order containing x ≺ x⁺ and x ≺ x̄⁺ | relation/Worlds.v:30, 106 | E |
| W5 | Constant world. O-New never extends W | plan §6.4, decision 2026-11-08 | C(F5). Kept in spirit. Generated roots are known up front through laws (§2.4) |
| W6 | Budgets `w_bud` and payload cost types `w_pc` live in the world | relation/Worlds.v:30-35, plan §17.8, §19.3 | C(F10). Remove. N and cost protocols replace them |
| W7 | Two-world composition, result in W1 ⊔ W2, `strict (wjoin W1 W2)` | composition/, LFCompose.v:245 | E (author 2026-11-17). Restate strictness by the interface (cleanup R7) |
| W8 | `pbot`, a point no world knows, stands for the ⊥ flag of futures | relation/Worlds.v:189 | E as a proof device |
| W9 | Pending-choice worlds | relation/BranchWorlds.v | prototype, outside this proposal |

### 1.3  Static typing

| # | Decision | Where | Verdict |
|---|---|---|---|
| S1 | ∀ over points and session variables only directly under □ | types/Types.v:111-160, memory forall-only-under-box | E |
| S2 | Box constraints as predicates over facts, possibly infinite | types/Types.v:76 | E |
| S3 | Existential payloads with a lower bound ℓ ∈ {none, ⊥, point} | types/Types.v:87, 140 | E |
| S4 | Futures F and arrow bounds ⊸^{ub}_{lb} | static/Typing.v:44-56 | E |
| S5 | `TPt x`, `t_pt`, `KTNewAt`, `KTPay`, `KTSucc` | types/Types.v:160, 1807-1816, static/Typing.v:44 | C(K4). Remove |
| S6 | `created` hypotheses introduce one constant per top-level channel | static/Typing.v:224, relation/Creation.v | C(K4). Remove. Fresh roots replace them |
| S7 | E-Const types a constant by the table `konst_ty` | static/Typing.v:32 | C(K2). Becomes a derived lemma (E-Abs plus E-Op) |
| S8 | Guard as rules, `glive`, E-Exp unguarded, a guarded sub-system for liveness | liveness/GuardRules.v:72, 330 | E (PN subsumption, decision 2026-11-06) |

### 1.4  Base relation (deadlock freedom)

| # | Decision | Where | Verdict |
|---|---|---|---|
| B1 | V, E, P step-indexed by course-of-values levels | relation/LogicalRelation.v:510-531 | E. One generic `sfix` for every fixpoint (cleanup P15) |
| B2 | Readiness and future as one gate, `ready_t`, `ready_p` | relation/Readiness.v:100-108 | E |
| B3 | Giving steps (send, select, close, link) cost 0 and recur on term size | relation/LogicalRelation.v:180-245, 318 | E as a cost table entry. The size recursion becomes the least fixpoint of the generic relation |
| B4 | V-Const reads `konst_ty` and `teqW` inside V | relation/LogicalRelation.v:132-133 | C(K2). Remove |
| B5 | V at ⊸ asks `fends eb = tenv_ends Θ` | relation/LogicalRelation.v:123 | C(ownership at transfers). Move to transfer sets |
| B6 | V-Box asks `fchans eb = ∅` | relation/LogicalRelation.v:160 | C(B5). Remove |
| B7 | `term_wf` as a separate premise of E-Abs and E-Box | relation/LogicalRelation.v:1116 | C(B5). Remove |
| B8 | Q-Send asks `dom Θe = fchans w ∩ C` | relation/LogicalRelation.v:396 | E. Read from the transfer set of the label |
| B9 | Θ may hold both ends, `One` and `Both`, entries keyed by a side bit | types/Types.v:1238-1258 | C(K3). One entry per end |
| B10 | O-New picks session types per index, the point comes from the label | relation/LogicalRelation.v:269-275 | session types E, point C(K4) |
| B11 | E has no Kripke quantifier, receive quantifies over W′ ⊒ W | relation/LogicalRelation.v:279 | to unify with L3 (decision Q9) |

### 1.5  Live relation

| # | Decision | Where | Verdict |
|---|---|---|---|
| L1 | τ steps (β, new, spawn, link) cost 0 and are read inductively, channel steps cost 1, a synchronization 2 | liveness/LiveRelation.v:1-20, 283 | E |
| L2 | A link is a τ step of cost 0 | decision 2026-11-08 | E |
| L3 | Every clause of `Ebody` holds in every W1 with `wext_r W W1` | liveness/LiveRelation.v:265 | to unify with B11 (decision Q9) |
| L4 | `tenv_fit` in the arrow and in `Vspawn`, with `tenv_bipol` | liveness/LiveRelation.v:111, 246, 343 | C(K3, B5). Remove |
| L5 | E-Fit in `Ebody` | removed 2026-11-16 (a5b45db) | gone |
| L6 | The live relation is a copy of the base one | quirk A4 | Q. One relation with a cost table |
| L7 | Forcing the self only under the λs of a box body | sharp edge 161 | E (guard) |

### 1.6  Lock freedom

| # | Decision | Where | Verdict |
|---|---|---|---|
| F1 | Criterion over the untyped instrumented semantics, by rank, measure and admin depth | lockfree/Criterion.v:118-298 | E |
| F2 | Rank is `well_founded (w_lt W)`, no number | plan §10.2-10.3 | E |
| F3 | A ceiling of height ω is fine when nobody waits there | plan §17.5 | E (consequence of F2) |
| F4 | Postponement, delegation and growing chains need two bounds, fuel and rank | plan §1, §17.1 | E |
| F5 | Placement must be the same at every index | plan §14, §17.2 | E (C1 counterexample, §4.2) |
| F6 | Placement oracle ω | plan §15 | superseded |
| F7 | Syntactic points | plan §16 | superseded by placement rules (§2.5) |
| F8 | Fuel per held end, ticking at the holder's channel actions on other ends, refilled at an action on the end | plan §17.3, lockfree/LFFuel.v:119-131 | E |
| F9 | Budget ∞ and F-Wait replace "ticks only while the partner offers" | plan §7, §17.3, LFFuel.v:161 | C(W6). No proved result uses ∞ (quirk A12). Drop, or idle protocols (decision Q5) |
| F10 | Budgets keyed by points, floors keyed by the carrier's point | plan §17.3, §17.8 | C(F7). Remove. One refill N, floors in cost protocols |
| F11 | `ftravel` | LFFuel.v:175 | C(F9). Remove |
| F12 | F-Cap, `fcap_ext`, `farg`, `fin_ok`, `fpts`, `wbext` | LFFuel.v:156, 183, 301-325 | C(W6). Remove |
| F13 | Link tickets, spawn splits ⌈tk/2⌉ and ⌊tk/2⌋ | plan §18.3, LFFuel.v:243-247 | tickets E. The fixed split is the only index-free split (§3.4) |
| F14 | Lexicographic measure (tickets left, counter) | LFAdequacy.v:1175 | E |
| F15 | `Fdef` closed under injective renamings (`kinj`) | LFFuel.v:285, 396 | E (links rename) |
| F16 | `new` fresh against the thread's own map | LFFuel.v:236-238 | E |
| F17 | Send, spawn and link hand on only held ends, a send not its subject | plan §19.13.1-2 | E. One clause over transfer sets |
| F18 | `fsolo` at select and branch | plan §19.13.3, LFFuel.v:212 | C(K3). Remove |
| F19 | A pair splits its points into disjoint parts | plan §19.13.4 | E |
| F20 | Soup fixes q, P, F, K outside the index, environments and types inside | LFSoup.v:306 | E. P becomes derived (determinism, cleanup R3) |
| F21 | `LFP` has a first conjunct `∀ n, LPrel n` | LFSoup.v:306-307, quirk A6 | Q. Derive no τ-divergence per thread |
| F22 | `prim T`, `lf_sig`, `lf_own` | LFSoup.v:257-279 | E (honest side conditions) |
| F23 | `lf_known`, and the premise of `LFP_term` that W knows the environment's points | LFSoup.v:279, decision 2026-11-17 | C(W6). Remove |
| F24 | `wbud_agree W1 W2` in `LFP_connect` and `LFP_join` | decision 2026-11-16 | C(W6). Remove |
| F25 | A soup step goes from index n + 2 to n, two clocks | quirk A9, G4 | accept, or unify the clocks (§2.10) |

### 1.7  Cost types

| # | Decision | Where | Verdict |
|---|---|---|---|
| T1 | A separate cost judgment, not costs in `ty` | plan §19.2 | E |
| T2 | Arrow `CArr c t h σ1 σ2` with cost, ticket transformer and floor, box `CBox c t σ`, credits | relation/CostTypes.v:156 | E |
| T3 | Cost protocols with a budget per node, point profiles `CPt`, `pfits` against the world | CostTypes.v:156-181, LFFuel.v:191 | C(W6, K4). Protocols keep only payload cost types |
| T4 | `CAny` with the aging condition `cheld` | CostTypes.v:157, static/CostTyping.v:169-180 | Q (plan §19.12.4). Remove `CAny` |
| T5 | No constant at arrow type, `konst_cost` deleted | plan §19.14.4 | Q. Removed by K2 |
| T6 | `C-SpawnLam` beside `C-Spawn` | plan §19.12 | decision Q8 |
| T7 | `cfacts` premises at C-Abs, C-Box, C-SpawnLam | plan §19.14.6 | C(B5). Only C-Send and C-Spawn need a typing lemma |
| T8 | `tok` premises, `tseq` sound only there | plan §19.12.5 | E (arithmetic of 2^s·r + b) |
| T9 | Credit 0 on pairs and sums built by rules | plan §19.12.3 | E |
| T10 | `pnode` and `pprof` to unfold cofixpoints | plan §19.12.6 | Q. Cost protocols as μ-terms like session types |

## 2  The concepts of the proposed design

### 2.1  Layers

```
  semantics       ends c⁺ c⁻, events with transfer sets, thread ids, weak fairness
      │
  points, worlds  roots (constants, generated), x⁺, x.κ, x̄, order ≺_W, laws Λ
      │
  environments    Θ : end ⇀ S@x        placement at new        readiness, futures
      │
  R^κ             one step-indexed relation (V, E, P), cost table κ
      ├── κ_DF  → deadlock freedom      (adequacy: no stuck closed process)
      └── κ_L   → live relation         (adequacy: DF and no τ-divergence)
                    │
  fuel            FuelE^N  per thread, counters, tickets, cost protocols, no points
      │
  soup            ∀ thread: R^{κ_L} ∧ FuelE^N, ownership and points fixed outside the index
      │
  rank            well_founded ≺_W         criterion → lock freedom
```

Deadlock freedom uses the first four layers. Lock freedom adds fuel, soup
and rank and changes nothing below them.

### 2.2  Channels and ends

**Job.** Identity of communication.

A channel c has two ends c⁺ and c⁻, and c̄⁺ = c⁻. A value `Chan o` names one
end o. `new` returns ⟨c⁺, c⁻⟩. A message on o synchronizes with an action on
ō. A link of o1 and o2 renames the channel of the partner as now. The end
name never depends on a point, so select and branch keep their end, and the
runtime reads no point at all.

### 2.3  Points

**Job.** Positions in protocols, ordered by the world.

```
root   r ::= a            a constant, known to W with its own facts
           | g            a generated root, from an infinite supply G
point  x ::= r | x⁺ | x.κ | x̄
```

`x̄` flips the polarity, fields ignore it (x̄.κ = x.κ), shift keeps it. An
action moves an end from x to x⁺, select to (x.κ_i)‾, branch to x.κ_i, and
the channels a message carries sit at the fields x.κ of the carrier's point.
These laws exist today (lang/Syntax.v:72-117). Point variables exist only in
types, bound by □ ∀ and by payload ∃.

### 2.4  Worlds

**Job.** The order. Nothing else.

```
W = (A, ≺_A, Λ)
  A       finite set of constants
  ≺_A     facts between points with constant roots
  Λ(r)    laws, facts between points with the root variable r and constants
≺_W = transitive closure of  ≺_A ∪ ⋃_{g ∈ G} Λ(g) ∪ { x ≺ x⁺ } ∪ { x ≺ x̄⁺ }
```

Every generated root is known and obeys the same laws, so W is constant along
every run although runs create roots. `world_wf` keeps the fields of
relation/Worlds.v:106. `strict W` asks ≺_W irreflexive. The lock-free world
asks in addition `well_founded ≺_W`, one record instead of three names
(quirk A14). The join W1 ⊔ W2 unions constants, facts and laws.

No budget, no payload cost type and no alias relation sits in W (removes
W6, quirks A11, A13, A13c, F8, G5).

### 2.5  Environments and placement: how `new` connects channels and points

**Job of Θ.** The only link between ends and points.

```
Θ : end ⇀ S@x        one entry per end, no One/Both, no side bits
Σ : end ⇀ S@x        the interface of a process, one end per channel
```

**Job of placement.** Give the ends of a new channel their points, as a
function of the step and of Θ.

```
new          →  c⁺ : S@g,    c⁻ : S̄@ḡ       g a generated root fresh for Θ
new_κ o      →  o unchanged, c⁺ : S@x.κ, c⁻ : S̄@(x.κ)‾      where Θ(o) = _@x
```

`new_κ o` is anchored creation. It takes a held end o, returns it untouched,
and creates the channel at the field κ of o's point. The anchor is threaded
linearly, so the term mentions o and gives it back, and no point occurs in
the program. κ is a label like a branch label. The static types are

```
new   : 1 ⊸ ∃ρ. Λ(ρ). (S@ρ ⊗ S̄@ρ̄)
new_κ : S0@x ⊸ S0@x ⊗ (S@x.κ ⊗ S̄@(x.κ)‾)
```

A fresh root needs facts only from the laws. A channel that must sit below
or above a held end is created at a field of that end, and the box
constraint or W supplies the facts about x.κ. This covers every current use
of `new (EPt x)`. A box parameter `TPt ι` disappears, because the box
receives an end at ι and anchors there, or creates at a fresh root. The
recursion of a box at x⁺ needs no instance either. The self call receives
the ends that the round moved to x⁺, and typing instantiates the box there.

The semantic clause is deterministic. For `new` it is universal over the
generated roots fresh for Θ, which is harmless because all generated roots
obey the same laws (renaming invariance of generated roots, to prove from
static/PointSubst.v). The soup picks the least root that no thread uses.
For `new_κ` there is nothing to pick. So the point of every end at every
position of a run is a function of the initial points and the run, the same
at every index. This is what lock freedom needs (§4) and what syntactic
points provided.

### 2.6  Readiness and futures

**Job.** The gate that excludes circular waiting.

Unchanged from relation/Readiness.v. A term with future F that is stable and
reducible offers some held ends, every offered end lies below the partner
point of every held end it does not offer, and below every point of F. A
process offers some interface end, and every interface end it holds and does
not offer has an offered end below its partner point. A link redex compares
nothing. Entries are per end, so `selects` loses its polarity tests
(Readiness.v:38-56).

### 2.7  Transfers: the one fact about syntax

**Job.** Make the ownership that a spawn or a send hands over agree with the
ends the step physically moves.

The semantics labels `spawn w` and `send o w` with the transfer set
M = ends(w), the ends that leave the thread with w. It already computes the
same set for scope extrusion (`sentc`). The relation reads M from the label
at three clauses (O-Spawn, O-Send, Q-Send) and nowhere else. Ownership has to
follow M, because lock freedom reads the holder of an end as the thread that
will act on it, and only the thread whose term holds the end can act on it.
The split at a hand-over must also be the same at every index, and M is the
only index-free source of it. No V clause reads a term. The closure
condition `fends eb = tenv_ends Θ`, `tenv_fit`, `tenv_bipol`, `fchans eb = ∅`
of V-Box, `fends eb = ∅` and `dom π = fends w` of `Vfuel`, and `term_wf`
go. A closure that owns an end it does not mention cannot act on it and
cannot hand it over, so the relation rejects it by itself (argued). The
compatibility lemmas of C-Send and C-Spawn use the typing fact that a typed
value's ends are its environment's ends, as a lemma about derivations
(`ctyped_cfacts` today), not as a premise of any relation.

### 2.8  The base relation R^κ

**Job.** One step-indexed definition for every relation on protocols.

A cost table κ assigns each step a cost. Steps of cost 0 are read
inductively inside a level, steps of cost c > 0 at level n − c.

| Step | κ_DF | κ_L |
|---|---|---|
| β, force | 1 | 0 |
| new, spawn | 1 | 0 |
| link | 0 | 0 |
| send, select, close | 0 | 1 |
| receive, branch | 1 | 1 |
| synchronization of two threads | κ(send) + κ(recv) = 1 | 2 |

In κ_DF the cost-0 steps shrink the term (`tstep_giving_size`,
relation/LogicalRelation.v:232), so the least fixpoint is the size recursion
of `Efuel` today. In κ_L they are τ steps, and the least fixpoint is the
content of liveness. The value relation at level n follows.

```
V_n⟦1⟧(Θ, v)            ⇔ Θ = ∅ ∧ v = ∗
V_n⟦S@x⟧(Θ, v)          ⇔ v = Chan o ∧ Θ = {o ↦ S'@x} ∧ S' ≃ S
V_n⟦T ⊸^u_l U⟧(Θ, v)    ⇔ v = λe ∧ l ≼ heads Θ ∧
                          ∀ W' ⊒ W, j < n, Θ', w ∈ V_j⟦T⟧_{W'}(Θ'), F with u ≺ F.
                            e[w] ∈ E_j⟦U ≺ F⟧_{W'}(Θ ⊎ Θ')
V_n⟦T ⊗ U⟧(Θ, v)        ⇔ v = ⟨v1, v2⟩, Θ = Θ1 ⊎ Θ2, componentwise
V_n⟦T ⊕ U⟧(Θ, v)        ⇔ an injection into one side
V_n⟦□∀ῑ.C.T⟧(Θ, v)      ⇔ Θ = ∅ ∧ v = !e ∧ ∀ W' ⊒ W, instances xs known in W' meeting C.
                            the thunk of e ∈ V_n⟦1 ⊸ T[xs]⟧_{W'}(∅)
V_n⟦∃^ℓ ῑ.C.T⟧(Θ, v)    ⇔ ℓ ≼ heads Θ ∧ some known instance xs meets C ∧ v ∈ V_n⟦T[xs]⟧(Θ)
```

The live arrow reads levels j ≤ n, so a β is free
(liveness/LiveRelation.v:343-348). That is the κ_L instance of "body at the level after the β step".
There is no constant case, because constants are λ-values (§3.2).

E at level n is the least X such that for every W′ ⊒ W (decision Q9)

```
(stop)  e irreducible  ⇒ e ∈ V_n⟦T⟧(Θ)
(gate)  e reducible    ⇒ ready_{W'}(Θ | F, e)
(step)  e →α e'        ⇒ Obl_α,  where "e' at Θ'" means X(Θ', e') if κ(α) = 0
                                          and e' ∈ E_{n−κ(α)}(Θ') otherwise
Obl β, force        e' at Θ
Obl new             ∀ g ∈ G fresh for Θ. ∃ S S' dual. e' at Θ, c⁺ : S@g, c⁻ : S'@ḡ
Obl new_κ o         Θ(o) = _@x, ∃ S S' dual. e' at Θ, c⁺ : S@x.κ, c⁻ : S'@(x.κ)‾
Obl spawn w, M      Θ = Θ_M ⊎ Θ_r, ends Θ_M = M, w ∈ V_n⟦1 ⊸ 1⟧(Θ_M), e' at Θ_r
Obl send o w, M     Θ = o : !P.S@x ⊎ Θ_M ⊎ Θ_r, ends Θ_M = M,
                    w ∈ V⟦P[x]⟧(Θ_M), e' at Θ_r, o : S@x⁺
Obl recv o w        Θ = o : ?P.S@x ⊎ Θ_r, ∀ W' ⊒ W, j ≤ n − κ, Θ_in,
                    w ∈ V_j⟦P[x]⟧_{W'}(Θ_in) ⇒ e' ∈ E_j(Θ_r ⊎ Θ_in, o : S@x⁺)
Obl close o         Θ = o : end@x ⊎ Θ_r, e' at Θ_r
Obl select_i o      Θ = o : ⊕(S1,S2)@x ⊎ Θ_r, e' at Θ_r, o : S_i@(x.κ_i)‾
Obl branch_i o      Θ = o : &(S1,S2)@x ⊎ Θ_r, e' at Θ_r, o : S_i@x.κ_i
Obl link o1 o2      Θ = o1 : S@x ⊎ o2 : S̄@x̄ ⊎ Θ_r, e' at Θ_r
```

P at level n is the same scheme over process steps with interface Σ,
P-Stop, `ready_p`, Q-Admin at cost κ(τ), Q-Comm at κ(send) + κ(recv), Q-Send
with `dom Θe = M ∩ C`, and Q-Recv with `recv_back` as in
relation/LogicalRelation.v:443-490. Instances.

```
DF   = R^{κ_DF}      adequacy:  ∀ n, P_n⟦∅ ⊢ T⟧_W(p) ⇒ deadlock_free p
Live = R^{κ_L}       adequacy:  ∀ n, P_n ⇒ deadlock_free p ∧ no_tau_divergence p
```

### 2.9  The live part

**Job.** Exclude internal divergence.

Liveness is the instance κ_L, nothing more. The guard stays a static
judgment (`glive`, liveness/GuardRules.v:72) whose fundamental theorem lands
in κ_L. E-Exp stays unguarded in the deadlock-freedom system, so PN's
`⟨fix λx.x⟩` keeps its typing there. `live ⊆ DF` becomes one lemma about
cost tables (to prove, quirk G2).

### 2.10  Fuel

**Job.** Exclude endless postponement and endless hand-over by a waiter's
partner.

Per thread, outside the index. Counters φ : end ⇀ ℕ on the held ends,
tickets tk ∈ ℕ. Per index, inside the predicate. Cost protocols Π : end ⇀ P
(§2.11). One constant N, the refill. No point, no world.

```
FuelE^N_0 = ⊤
FuelE^N_{n+1}⟦σ, r, d⟧(Π, φ, tk, e)  ⇔  for every renaming g injective on dom φ,
  (val)   e value ⇒ r ≤ tk ∧ e ∈ Vfuel^N_{n+1}⟦σ⟧(Π, φ)
  (step)  for every e →α e'
    β, force     e' at the same state, level n
    new          ∃ P Q dual. e' at Π + {c⁺ ↦ P, c⁻ ↦ Q}, φ + {c± ↦ N}
    new_κ o      the same
    act on o     (F-Tick) every other counter ≥ 1 and d ≥ 1.
                 e' at φ' = (φ − 1 off o)[o ↦ N], Π advanced at o, frame d − 1
    send o w, M  M ⊆ dom φ ∖ {o}, w ∈ Vfuel^N_n⟦pay(Π o)⟧(Π|M, (φ − 1)|M),
                 e' without M, plus the tick of "act on o"
    recv o w     ∀ j ≤ n, Π_in, φ_in, w ∈ Vfuel^N_j⟦pay(Π o)⟧(Π_in, φ_in).
                 e' at level j with Π_in and φ_in added, plus the tick
    spawn w, M   M ⊆ dom φ, φ|M ≥ 1. The child satisfies FuelE^N_n⟦thread⟧
                 at (Π|M, (φ − 1)|M, ⌈tk/2⌉, w ∗). e' at ⌊tk/2⌋ without M
    link M       M ⊆ dom φ, tk ≥ 1, e' at tk − 1
fsem^N(φ0, e) ⇔ ∃ tk, ∀ n, ∃ Π. FuelE^N_n⟦thread⟧(Π, φ0, tk, e)
```

`act on o` covers send, receive, close, select and branch. `⟦thread⟧` is the
result of a thread, reserve 0, frame ∞, holding no end at the end (this
replaces `CAny`). Ticket counts and counters are functions of the run.
Session-type-like protocols are chosen per index, which adequacy never reads
(§4.4).

What goes. F-Cap and the cap in every extension (counters are ℕ and only
lower bounds matter), F-Wait and `ftravel` (no ∞), `fin_ok` and known points
(no budgets at points), `wbext` (no world), `fsolo` (ends keep their names),
`fhand` as a separate clause (the floor is the credit inside the payload's
cost type). `Fobl` becomes one side condition per event and one continuation
(cleanup P4).

FuelE^N is monotone in the counters and in N (to prove). Injective renamings
make the obstacle of quirk G3 disappear, because no two held ends share an
image. Composition takes the larger N.

Optional, one clock (quirk G4). FuelE can read β at j ≤ n like the live
arrow. Then fuel and the live relation share the cost table κ_L and the soup
loses the same number of levels at every step.

### 2.11  Cost types and the cost judgment

**Job.** A static, compositional source of fuel for every program, higher
order included.

```
τ ::= 1 | End P | Arr c t h σ1 σ2 | Box c t σ | σ ⊗ σ | σ ⊕ σ
σ ::= τ^a                         a ∈ ℕ ∪ {∞} the credit
P ::= !σ.P | ?σ.P | ⊕(P,P) | &(P,P) | end | μα.P | α
t ::= (s, b)                      r ↦ 2^s·r + b
```

A cost protocol is a session type whose payloads are cost types. It carries
no budget and no point. Credits are lower bounds on counters. `End P` at
credit a holds an end with counter at least a and protocol below P. A
closure `Arr c t h σ1 σ2` performs at most c actions before it returns, runs
at every ticket count above t(r), and works for every captured counter at or
above h. `Box c t σ` does the same per force.

```
Vfuel^N_n⟦1^a⟧(Π, φ, v)          ⇔ v = ∗ ∧ dom φ = ∅
Vfuel^N_n⟦(End P)^a⟧(Π, φ, v)    ⇔ v = Chan o ∧ dom φ = {o} ∧ Π o ⊑ P ∧ φ o ≥ a
Vfuel^N_n⟦(Arr c t h σ1 σ2)^a⟧    ⇔ v = λe ∧ φ ≥ h + a ∧ ∀ j < n, φ' ≥ h on dom φ,
                                     u ∈ Vfuel_j⟦σ1⟧(Π_u, φ_u), r, tk meeting t.
                                     e[u] ∈ FuelE^N_j⟦σ2, r, c⟧(Π ∪ Π_u, φ' ∪ φ_u, tk)
Vfuel^N_n⟦(Box c t σ)^a⟧         ⇔ v = !e ∧ dom φ = ∅ ∧ ∀ j < n, r, tk meeting t.
                                     e[!e] ∈ FuelE^N_j⟦σ, r, c⟧(∅, ∅, tk)
⊗, ⊕                              disjoint split of the maps, credit added to the parts
```

The judgment Θ; Γ ⊢_N e : σ ▷ c ; t keeps the rules of plan §19.4 and
static/CostTyping.v, with these changes. C-Pt, C-Pay, C-Succ, C-Konst and
`konst_cost` go. C-New gives both ends credit N and dual protocols. C-NewAt
types the anchor and returns it unchanged. One rule C-Op per primitive
operator types its saturated form. Aging needs no `cheld` condition, because
no entry has an unconstrained type. The world index W0 becomes N.

### 2.12  The lock-free judgment

**Job.** Tie each thread's live relation and fuel to one ownership that is
the same at every index.

```
a = (q, P0, φ0, K0)      q an instrumented configuration with thread ids,
                         P0 the points of the ends held at the start,
                         φ0 counters, K0 tickets, per thread

Soup^N_n(W, Σ, T, a)  ⇔ ∃ A, U, Π per thread (chosen at this index) such that
  per thread t      e_t ∈ E^{κ_L}_n⟦U_t ≺ ∅⟧_W(A_t),  e_t ∈ FuelE^N_n⟦thread⟧(Π_t, φ_t, K_t),
                    ends A_t = dom φ_t,  points A_t = P_t,  U_t ∈ {T, 1}
  pairwise          ends A_t ∩ ends A_s = ∅
  per channel       an internal end's partner is held, at the dual point,
                    with the dual session type and the dual cost protocol
  interface         an end of Σ is held at Σ's entry, every entry of Σ is held
  result            prim T

LF(W, Σ, T, p)  ⇔  ∃ N a. erase q = p ∧ ∀ n, Soup^N_n(W, Σ, T, a)
```

Along a run, P, φ and K follow the events deterministically. Placement gives
new points, actions move points, transfers move entries with counter − 1,
links spend a ticket and rename. The preservation lemma is today's
`lfsoup_step` (LFSoup.v:2592). The first conjunct `∀ n, LPrel n` of today's
`LFP` goes. No τ-divergence follows from the per-thread least fixpoints,
because a spawned thread's τ prefix belongs to its parent's fixpoint
(`Vspawn`, LiveRelation.v:242-252, to prove as `soup_no_tau_divergence`).

### 2.13  Rank and adequacy

**Job of rank.** Exclude waiting chains that grow forever.

```
lf_adequacy : world_wf W → well_founded ≺_W → LF(W, ∅, T, p) → lock_free p
```

The proof is today's instantiation of `lf_run_criterion` (Criterion.v:287).
The rank of a pending thread is the point of the end it offers, at the
current position, ordered by ≺_W. The measure is (tickets left, counter of
the partner end). The dependency is ownership in the soup. `lf_criterion` and
`waits` go (quirk A3).

### 2.14  Composition

**Job.** Build every judgment from components, each in its own world.

```
DF/Live   P-Term  : Θ-typed thread                              ⇒ P⟦Σ ⊢ T⟧_W(C0, {t})
          P-Connect, P-Join : P in W1 and P in W2, cut dual, strict (W1 ⊔ W2)
                                                                ⇒ P in W1 ⊔ W2
LF        LF-Term : the P-Term premises ∧ fsem^N(N on the ends, t)
          LF-Connect, LF-Join : LF in W1 and LF in W2, the same cut ⇒ LF in W1 ⊔ W2
```

The soups concatenate, P0, φ0, K0 union, and N is the larger of the two.
No budget agreement is asked. The strictness of the join is stated by the
interface orders (cleanup R7).

### 2.15  Shared and layered

| Concept | DF | Live | LF |
|---|---|---|---|
| ends, events, transfer sets | uses | uses | uses, plus thread ids and fairness |
| points, worlds, placement | uses | uses | uses, plus `well_founded ≺_W` |
| environments, readiness, futures | uses | uses | uses through Live |
| R^κ | κ_DF | κ_L | κ_L per thread |
| composition shape | two-world | two-world | two-world, soups concatenate |
| fuel, cost types, tickets | none | none | new |
| static side | typing | typing + guard | typing + guard + cost judgment |

Lock freedom adds three definitions (FuelE, the soup, the rank premise) and
one judgment (costs). It changes no definition of the layers below it.

## 3  Quirks and deviations

### 3.1  Quirks of docs/extensions/lock-freedom-quirks.md

| Quirk | Fate | How |
|---|---|---|
| A1 value-level syntax | reduced to one | transfer sets in labels (§2.7). No V clause reads a term |
| A2 polarity bit | removed | end names c⁺, c⁻ (§2.2) |
| A3 two kinds of waiting | removed | only `lf_run_criterion` with ownership |
| A4 base and live are copies | removed | R^κ (§2.8) |
| A5 links cost 0 | stays | one entry of κ_L, a decision of the author |
| A6 `LFP` has two conjuncts | removed | `soup_no_tau_divergence` (§2.12) |
| A7 q, P, F fixed before the index | reduced | P and φ follow the run from P0, φ0. q with ids stays, fairness names threads |
| A8 `prim T`, `lf_sig`, `lf_own` | stays | honest interface conditions, grouped (I4) |
| A9 index loss | reduced | optional single clock (§2.10) |
| A10 fuel on ends | stays | correct with tickets (plan §18). Counters belong to held ends, only the holder writes them |
| A11 two budget maps | removed | N and cost protocols |
| A12 budget ∞ and `ftravel` | removed | no ∞. Idle protocols as an option (Q5) |
| A13 Kripke closure needs names | removed | FuelE reads no world |
| A13b replacement against floor | gone | already lifted by link tickets |
| A13c incoming ends at unknown points | removed | no budgets at points |
| A14 three world predicates | removed | one lock-free world record |
| B1-B5, B7-B9 fragment checks | gone | already lifted by the cost judgment |
| B6 recursion with a point argument | removed | no point values |
| C1 points in terms | removed | placement (§2.5) |
| C2 source soundness misses creation | removed | `new` at a fresh root needs no hypothesis, so `soundness_source` covers creation again |
| C3 choice not derivable | removed | ChoiceTranslate creates at the carrier's point, which is `new_κ` on the carrier |
| C4 TreeSum's result has no point | moot | no `TPt`. SegmentInterleave anchors at an end or uses a fresh root (to check) |
| C5 constant world holds every point | stays | the facts of anchored points come from box constraints and W. Needed by C1 (§4.2) |
| D1-D4 scope | stays | |
| D5 SemFlag | open | outside this proposal |
| F1 two point maps | removed | P derived |
| F2 events read back | removed | events in labels |
| F3 defaulted measures | reduced | measures from the soup's partner clause |
| F4 two renamings | removed | one `emap` and one `csub` in lang |
| F5 nine-way `Fobl` | removed | side condition per event plus one continuation |
| F6 three hand-over clauses | removed | one transfer clause |
| F7 `frep` | gone | |
| F8 budgets in the world | removed | |
| F9 dead code | gone | rewrite |
| G1 soup to `LPrel` | replaced | per-thread no τ-divergence |
| G2 live ⊆ base | to prove | one lemma over cost tables |
| G3 monotone in counters | to prove | needed for N by maximum, unblocked by `kinj` |
| G4 two clocks | optional | §2.10 |
| G5 no-eq leftovers | removed | `=` in every statement |
| H1-H5 proof engineering | rewrite rules | one `sfix`, `simpl never` on FuelE, scoped `set_solver`, generic soup lemmas |
| I1-I4 generality | adopted | one per-thread scheme, soups as products |
| J1-J3 names | adopted | fields, x⁺, one meaning per letter |

### 3.2  Constants at arrow type (plan §19.14.4)

**Why it arose.** `Vfuel` treated a constant k at an arrow type by asking
the arrow clause of its own redex `App k v` at every level j < n (plan
§19.11.3). A λ-value takes a β step before its body runs, so the body at
level n − 1 gives the application at level n (F3, `FuelE_beta`). A constant
has no β step. Its redex is the application itself, so the clause gives
`App k v` one level short, and C-App fails. The counterexample of §19.14.4
makes it concrete. Take x at an arrow of cost 1 into the unit and y at a pair
of the unit and a sending end. The substitution x ↦ `send` is in `Vfuel 2`,
because at level 1 the redex is checked only trivially, while `App send y`
has no `FuelE 2`, because it returns an end and not the unit. Reading the
redex at j ≤ n instead breaks force, whose box argument then sits one level
too low. H4 therefore removed constants from arrow types, so a constant
passed as a function had to be written λx. k x.

**How the redesign avoids it.** The calculus has no constant values.
Primitives are saturated operators (`send e`, `recv e`, `close e`,
`select_κ e`, `branch e`, `link e`, `spawn e`, `force e`, `new`, `new_κ e`),
and the constant `send` is defined as the value λx. send x. Every value of
arrow type is then a λ, the arrow clause of V and of `Vfuel` has one case,
and the application of a constant takes a β step like any other. The
programmer still writes `f send`. Nothing is η-expanded by hand, because the
constant is the λ. The same change deletes V-Const with `konst_ty` and
`teqW` from the base relation (relation/LogicalRelation.v:132-133), the
constant disjunct of `Vspawn` (LiveRelation.v:251-252) and of the live arrow
(LiveRelation.v:349-350), and turns E-Const into a derived lemma. The cost
is one β step per primitive call, free in κ_L and harmless in κ_DF.

### 3.3  Deviations of plan §19.11 to §19.14

| Deviation | Fate | How |
|---|---|---|
| 19.11.1 `pfits_at` over three functions | removed | no `pfits` |
| 19.11.2 subtyping `cst`, credits | stays | renamed ⊑, credit rules unchanged |
| 19.11.3 constant runs its own redex | removed | §3.2 |
| 19.11.4 clause shapes, frame tick | stays | the frame is the bound c of the result |
| 19.11.5 `FuelT` | stays | the ⟦thread⟧ instance |
| 19.11.6 freshness of new from the soup | stays | fresh against the thread's own ends, the soup supplies it |
| 19.11.7 Fragment.v floors | gone | |
| 19.12.1 weakening at the leaves | stays | standard |
| 19.12.2 `ccap` | stays | the restatement Θ^h of C-Abs |
| 19.12.3 credit 0 on built pairs | stays | |
| 19.12.4 `CAny` and `cheld` | removed | no `CAny`, a thread has its own result marker |
| 19.12.5 `tok` | stays | arithmetic of transformers |
| 19.12.6 `pnode` | removed | cost protocols as μ-terms |
| 19.12.7 small choices, `konst_cost` | reduced | `konst_cost` goes (§3.2) |
| C-SpawnLam | decision Q8 | |
| 19.13.1-2 transfer held ends, not the subject | stays | one clause over the transfer set |
| 19.13.3 `fsolo` | removed | ends keep their names at select and branch |
| 19.13.4 disjoint split of a pair | stays | |
| 19.14.1 `farg`, `fcap_ext` | removed | no cap |
| 19.14.2 `fpts` | removed | no points and budgets in fuel |
| 19.14.3 boxes hold no end, `fends eb = ∅` | removed | `dom φ = ∅` on the map stays, the term condition goes (§2.7) |
| 19.14.4 no constant at arrow type | removed | §3.2 |
| 19.14.5 `fkont` cap in every extension | removed | no cap |
| 19.14.6 `cfacts` at C-Abs, C-Box, C-SpawnLam | reduced | used only at C-Send and C-Spawn, as a typing lemma |

### 3.4  What stays and why

- **The fixed ticket split.** The child's share must be the same at every
  index, and any split read from a cost type is chosen per index. ⌈tk/2⌉
  and ⌊tk/2⌋ is the simplest index-free split. Its price is the 2^s·r + b
  form of transformers and the `tok` premise.
- **Anchored facts in W (C5).** A run's points must have index-free facts.
  Anchoring fixes the point, so its facts must already be in W or in the box
  constraint. C1 below shows that facts chosen at run time are unsound.
- **One condition on transfers.** Without it the split at a spawn is a free
  choice per index, and the soup's ownership has no index-free value.
- **`prim T`.** A main thread that returns an end holds a partner forever
  (plan §8).

## 4  The points question

### 4.1  What the adequacy proof reads

`lf_adequacy` (lockfree/LFAdequacy.v:1162) instantiates `lf_run_criterion`
(Criterion.v:287) along one fair maximal run r. The criterion takes a
well-founded R on some type E and a function we(k, t), and asks two things
of it (Criterion.v:136-138).

- `Hstab`. we(k + 1, t) = we(k, t) while t is pending and does not step.
- `Hrank`. If t is pending at k and the pending thread s holds the partner
  of t's end, then t is enabled or R(we(k, s), we(k, t)).

Adequacy takes we(k, t) = π_k(o_t), the point of the end t offers at
position k, and R = `w_lt W` (LFAdequacy.v:1173-1177). `Hrank` comes from the
gate of s at position k read at index 1 (`s_rank`, LFAdequacy.v:229).
`Hstab` comes from the soup step at index 3 (`stab_step`, LFAdequacy.v:306).
The measure reads the counters φ_k and the tickets K_k. Nothing reads a
budget, a floor or a cost protocol (checked, plan §19.3 notes that the floor
entered only `step_msg`).

### 4.2  Uniform across indices: yes

we must be one function of position and thread. The soup at position k
comes from the soup at position k + 1 only through a step from index n + 2 to
n, so a placement chosen per index gives one finite sequence π_0, …, π_{n/2}
per index n, and different n give different sequences. Plan §17.2 shows that
no index-dependent placement can be repaired by a condition on W. In C1
without a ceiling (W = program order on one constant a), index n places
main's channel at a + (2n + 1) and round k's channels at a + (2(n − k) + 1)
and a + 2(n − k). Every gate holds in program order, W is well founded,
every point has finite height, fuel 2 suffices, and main starves in every
fair run (world facts checked in the scratch file C1World.v, the placement
argued). So the rank of every end that a pending thread offers must be fixed
outside the index.

### 4.3  Uniform across time: no

The criterion reads R only inside one position and never compares positions
except through `Hstab`. So the order may grow along a run, W_0 ⊑ W_1 ⊑ …,
with R the union, provided that

1. the growth is the same at every index (§4.2), and
2. the union is well founded.

Condition 2 is not local in general. Facts chosen at a step for a fresh
point can descend forever (C1 again, now as a growing world). It becomes
local when a fresh point receives only instances of fixed laws. Then the
union is W_0 plus the laws at every generated root, which is well founded iff
the laws and W_0 are. Such a world is constant in effect, because it knows
every generated root up front (§2.4). So points can be runtime-fresh names.
What may not be chosen at run time is a fresh point's position in the order,
that is, its facts. The proposal fixes it by laws (generated roots) or by
the anchor (fields of held ends).

### 4.4  Budgets: uniform, but not per point

The counters φ_k must be functions of the run, which holds when a fresh end
starts at N, an action refills to N, a tick subtracts one and a hand-over
passes the counter minus one. A refill chosen per index (a budget per point
placed per index, or per protocol node chosen per index) breaks this. A
single N does not. Floors, in contrast, are contracts between sender and
receiver inside FuelE and are never read by adequacy, so they may be chosen
per index. They ride on cost protocols, which the soup pairs at each index
like session types. Per-point budgets added nothing. Every example of
CostEx.v uses one budget B per program, and a thread that is fueled at
refill B is fueled at every N ≥ B (monotonicity, to prove). The
author's conjecture therefore holds in this form. Points can be
runtime-fresh, budgets uniform as one N, floors in cost protocols. The order
must still be uniform, as a function of the run, and that is what placement
by laws and anchors provides.

### 4.5  Options compared

| | O1 point values (now) | O2 box-bound point expressions | O3 anchors and generated roots (proposed) | O4 fresh extension per index | O5 finite choice and König | O6 oracle from derivations |
|---|---|---|---|---|---|---|
| program text | `new (EPt x)`, `KPay`, `KSucc`, `TPt` parameters | `new@p`, `force[ps] b`, p over box variables | `new`, `new_κ o` | `new` | `new` | `new` |
| points at runtime | yes | yes, substituted at force | no | no | no | no |
| index-free placement | yes | yes | yes | no | yes, classically | yes |
| lock freedom | sound | sound | sound | unsound (C1) | sound with an axiom | closed runs only (plan §15.7) |
| DF expressiveness against today | same | same | same, plus creation without hypotheses (C2) and ChoiceTranslate (C3) | more (facts chosen freely) | less (bounded ranks) | same |
| extra concepts | point type, values, two constants | point expressions, instances at every force (453 lines in 83 files, plan §16.2), runtime point variables under E-Open | laws Λ, one anchored primitive | none | ranks, König | ω, preservation |
| author's constraints | violates (point values) | acceptable (box-bound), syntactic at force | met | met, but unsound | axiom | rejected 2026-11-09 |

Two further shapes were considered and fold into these. Ranks separate from
points (a rank per end in the soup) have the same problem at `new`, because
a fresh rank is a choice, and reduce to O3 or O5. A home point per thread,
advanced at each force, is O2 with the instance computed from thread state.
It needs a lexical rule for closures that are spawned, which makes it O2.

### 4.6  Recommendation

O3. Fresh generated roots with laws, and anchored creation at fields of held
ends. It keeps every program point-free, makes placement a function of the
run, removes the point type, the point values, the creation hypotheses and
the box point parameters, and restores ChoiceTranslate and source-level
creation. Lock freedom keeps `well_founded ≺_W` as its only premise on W. DF
loses nothing against today's constant world. The cost is one primitive
variant and the law component of W. Four box types that create at a
parameter point (FactoryEx, FreshBetween, FreshMany, GuardCex) have to
anchor at an end or use a fresh root, and their typings are to be checked
first, in stage S2.

## 5  Open decisions for the author

**Q1. Placement.** (a) O3 anchors and generated roots. (b) O2 box-bound
point expressions with instances at force. (c) Keep point values.
Recommended (a).

**Q2. Laws of generated roots.** (a) W carries laws Λ(r), one family for all
generated roots. (b) Only the built-in laws x ≺ x⁺ and x ≺ x̄⁺, so every fact
about a fresh channel comes through an anchor. (c) No generated roots, every
runtime `new` is anchored and top-level channels are process-level
restrictions at constants. Recommended (a). (b) cannot type a cycle created
by main, (c) changes how examples are written.

**Q3. The transfer condition.** (a) Transfer sets in the labels of spawn and
send (§2.7). (b) The relation reads `fends w` at the same two clauses. (c)
Drop C from the semantics and keep scope only in the relation (quirk A1),
which still needs (a) for lock freedom. Recommended (a).

**Q4. Budgets.** (a) One refill N per judgment, maximum at composition.
(b) A refill per thread, fixed in the soup. (c) Budgets per point in the
world (today). Recommended (a).

**Q5. Ends nobody waits on (the controller of plan §7).** (a) Drop, as no
proved result uses ∞ today. (b) Idle cost protocols. An idle end does not
tick and may not be acted on, and pairing makes both views agree at each
index. Recommended (a) now, (b) as an extension.

**Q6. One relation.** (a) R^κ with a cost table for DF and Live.
(b) Two copies as today (decision 2026-11-16 for the current development).
Recommended (a) for the rewrite, because the copies are an artefact of
Rocq (quirk A4) and the paper already presents liveness as the DF relation
with the τ clause made inductive.

**Q7. Constants.** (a) Saturated operators, constants as derived λ-values.
(b) Constants as values with a β-like step `App k v → op v`. (c) Today's
η-restriction. Recommended (a). (b) is the same up to one definition.

**Q8. Spawn in the cost judgment.** (a) C-SpawnLam and C-Spawn both.
(b) Per-end floors on arrows, so C-Spawn alone types GrowRing. (c) Only
C-SpawnLam, with `spawn v` sugar for `spawn (λ_. v ∗)`. Recommended (a).

**Q9. Kripke quantifier in E.** (a) In every unfolding, as the live relation
does. (b) Only at receive, with monotonicity as a lemma, as the base
relation does. Recommended (a), because it costs nothing in a least fixpoint
and gives monotonicity by definition.

**Q10. One clock.** (a) FuelE reads β at the same level, cost table κ_L.
(b) Every step costs one in FuelE. Recommended (a) if the bind lemma F1
survives it, otherwise (b).

## 6  Rewrite plan

Each stage ends with a full build, no `Admitted`, no axiom and a regenerated
CheckAll. At most two stages run at once.

| Stage | Content | Proves | Reuse |
|---|---|---|---|
| S1 language | ends c⁺ c⁻, saturated operators, derived constants, `new`, `new_κ`, events with transfer sets and thread ids as one semantics with erasure, one `emap` and `csub` | safety, harmony, thread simulation, `act_offer` once | lang/ (Syntax, Semantics, Safety, Harmony, ThreadSim, ChannelSwap), lockfree/Instr.v, Fair.v, Reach.v, TauThread.v |
| S2 points, worlds, types | point algebra with generated roots, worlds with laws, join, restriction, amalgamation, interface strictness (R7), `ty` without `TPt`, typing with E-New, E-NewAt, E-Op, two-world `ptyped`. Check FactoryEx, FreshBetween, FreshMany, GuardCex, SegmentInterleave | world lemmas, `PointSubst` without `TPt`, renaming of generated roots | relation/Worlds.v without budgets, Creation.v reduced to the laws, types/, static/Typing.v, PointSubst.v, FactTheory.v |
| S3 generic relation | `sfix`, cost tables, V, E, P of §2.8, readiness | `adequacy` (DF), `live_adequacy`, downward closure, monotonicity | LogicalRelation.v and LiveRelation.v as templates, Readiness.v unchanged |
| S4 generic compatibility | bind, operator redexes, Internalize, P-Connect, P-Term, P-Join, renaming, all over κ | the composition lemmas for both instances, `live ⊆ DF` | liveness/Live*.v (the newer proofs) as the template, composition/ for the base specifics |
| S5 static fundamental theorems | E-rules into R^{κ_DF}, guarded rules into R^{κ_L} | `fundamental`, `live_fundamental_guarded`, `soundness`, `live_soundness`, source soundness with creation | static/Fundamental.v, liveness/GuardRules.v, LiveGuardFund.v |
| S6 fuel | FuelE^N, Vfuel by cost types, F1 to F6, monotonicity in counters and N, renaming | `FuelE_bind`, `Vfuel_recount`, `FuelE_mono` | lockfree/LFFuel.v and LFFuelBind.v minus points, caps and `wbext` |
| S7 cost judgment | rules of §2.11, compatibility per rule | `ctyped_fsem` | static/CostTyping.v, lockfree/CostFund.v minus C-Pt, C-Pay, C-Succ, C-Konst, `pfits` |
| S8 soup and adequacy | `Soup^N`, the deterministic update, `lfsoup_step`, `soup_no_tau_divergence` | `lf_adequacy`, `lf_thread_progress` | Criterion.v unchanged, LFSoup.v and LFAdequacy.v without π, `pupd`, `pev`, `fsolo` |
| S9 lock-free composition and soundness | LF-Term, LF-Connect, LF-Join, `lfptyped` | `lf_fundamental`, `lf_soundness`, examples | LFCompose.v, LFTyped.v, examples/CostEx.v and CostFsem.v, Rank.v |
| S10 paper | one relation, two cost tables, a fuel layer and a soup | | paper/ |

Ordering. S1 and S2 first, alone. S3 and S6 can run in parallel, because
fuel reads no relation. S4 and S7 in parallel. S5 after S4. S8 after S5 and
S6. S9 last. Translations (PGV, PN, MP) stay out until S5 and need only the
removal of point values from their targets.

Statements that change form, for the author's approval. `LFP` loses its first
conjunct and gains N. `LFP_connect` and `LFP_join` lose `wbud_agree`.
`LFP_term` loses the known-points premise. `lf_criterion` goes, and
`lf_run_criterion` keeps its text. Every typing lemma of an example loses
`created` and point literals.
