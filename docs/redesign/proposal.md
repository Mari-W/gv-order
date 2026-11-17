# Redesign proposal: deadlock and lock freedom from one order and one fuel

Version 2. State read on 2026-11-17, branch `lock-freedom` at f3dd2fa with
LFTyped.v and Rank.v from lf-h5prep. Version 1 is commit ee664e2. This document changes no Rocq file. It is the
basis for a rewrite from the ground up. "Checked" marks a claim checked
against a definition or a Rocq lemma of that state, "argued" a claim argued
on paper here or in the plan, "to prove" a lemma the rewrite has to supply.

Notation. Ends c⁺ and c⁻ of a channel c. Points x, the dual point x̄, the
shift x⁺, the field x.κ. World
W with order ≺_W. Term environment Θ, process interface Σ, future F. N is
the refill of the fuel layer. Appendix A fixes the notation of every judgment
and theorem for Rocq and the paper alike, and Appendix B lists every known
counterexample with the part of the design that handles it.

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
2. Programs never mention a point. A `new_ℓ` creates at a fresh generated
   root of the family ℓ, whose facts are the fixed laws Λ_ℓ of the world, and
   a `new_κ o` creates at the field x.κ of the point x of an end o
   the thread holds (anchored creation). ℓ and κ are labels, like a branch
   label. Placement is a function of the run, so it is the same at every
   step index, which is what lock freedom needs (§4).
3. Channels and points are disconnected. A channel has two named ends c⁺ and
   c⁻. The environment maps an end to a session type at a point. `new` is the
   only place where an end receives a point.
4. The relation reads no syntax except one fact about steps. The operational
   semantics labels a send and a spawn with the set of ends the step moves.
   The spawn half of this needs the author's explicit agreement (Q3). Every
   other syntactic clause goes, and with it the constant cases of V.
   Constants are derived λ-values, so a constant passes as a function.
5. One generic relation, parametric in a cost table, gives both the
   deadlock-freedom relation and the live relation.
6. Fuel is one per-thread predicate with a single refill constant N, per-end
   counters, per-thread link tickets, and cost protocols that carry the
   payload floors. Cost protocols are chosen per index like session types,
   because adequacy never reads them.
7. The lock-free judgment mirrors deadlock freedom. It is the live process
   relation together with a soup of threads, each in the live relation and
   in the fuel predicate, with ownership, points, counters and tickets fixed
   outside the index. Adequacy is the existing type-free criterion.
8. The Rocq statements read as the paper's statements, with the same
   judgment forms, notation and names (Appendix A).

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
| W1 | End points. Each end has its own point, x and x̄, and readiness asks u ≺ v̄ | lang/Syntax.v:33-37, relation/Readiness.v:79-92 | E |
| W2 | No aliases (no-eq). `w_eq` is equality | relation/Worlds.v:41 | E. The abbreviation and the eight `wf_eq_*` lemmas go (quirk G5) |
| W3 | Points are roots with offsets and fields, (p,b)[i]. A payload field and the continuation of choice i share x.κ_i by design (K11) | lang/Syntax.v:28-37, 112-117 | E. Fields are labelled x.κ. Anchored creation uses the same fields on purpose (§2.3) |
| W4 | A world is a support of root names and a transitive order containing x ≺ x⁺ and x ≺ x̄⁺ | relation/Worlds.v:30, 106 | E |
| W5 | Constant world. O-New never extends W | plan §6.4, decision 2026-11-08 | C(F5). Kept in spirit. Generated roots are known up front through family laws (§2.4) |
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
| B2 | Readiness and future as one condition, `ready_t`, `ready_p` | relation/Readiness.v:100-108 | E |
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
| F21 | `LFP` has a first conjunct `∀ n, LPrel n` | LFSoup.v:306-307, quirk A6 | E for now. It mirrors "DF = process relation" (author, 2026-11-16). Dropped only once `soup_no_tau_divergence` is proved (§2.12) |
| F22 | `prim T`, `lf_sig`, `lf_own` | LFSoup.v:257-279 | E (honest side conditions) |
| F23 | `lf_known`, and the premise of `LFP_term` that W knows the environment's points | LFSoup.v:279, decision 2026-11-17 | C(W6). Remove |
| F24 | `wbud_agree W1 W2` in `LFP_connect` and `LFP_join` | decision 2026-11-16 | C(W6). Remove |
| F25 | A soup step goes from index n + 2 to n, two clocks | quirk A9, G4 | accept, or unify the clocks (§2.10) |

### 1.7  Cost types

| # | Decision | Where | Verdict |
|---|---|---|---|
| T1 | A separate cost judgment, not costs in `ty` | plan §19.2, decided under overnight delegation | open again (Q11, §2.16) |
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
  points, worlds  roots (constants, generated), x⁺, x.κ, x̄, order ≺_W, laws Λ_ℓ
      │
  environments    Θ : end ⇀ S@x        placement at new        readiness, futures
      │
  R^κ             one step-indexed relation (V, E, P), cost table κ
      ├── κ_DF  → deadlock freedom      (adequacy: no stuck closed process)
      └── κ_L   → live relation         (adequacy: DF and no τ-divergence)
                    │
  fuel            FuelE^N  per thread, counters, tickets, cost protocols, no points
      │
  LF              Live process relation ∧ soup (∀ thread: R^{κ_L} ∧ FuelE^N), ownership fixed outside the index
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
           | g_ℓ          a generated root of family ℓ, from an infinite supply G_ℓ
point  x ::= r | x⁺ | x.κ | x̄
```

`x̄` flips the polarity, fields ignore it (x̄.κ = x.κ),
shift keeps it. An action moves an end from x to x⁺, select to (x.κ_i)‾,
branch to x.κ_i, and the channels a message carries sit at the fields x.κ of
the carrier's point. These laws exist today (lang/Syntax.v:72-117). Point
variables exist only in types, bound by □ ∀ and by payload ∃.

**Anchored creation shares the payload fields, on purpose.** x.κ names the
channels a message on x carries and the continuation of choice i, and the
two share a point by design (K11). `new_κ o` creates at the same x.κ. That
is what the common pattern needs. A channel created to be sent on o must sit
at the payload field of o's point, because V at the payload type places a
carried end at x.κ (`payload_at`). The reply channel of a request and reply,
the reply channel of KobForwarder, and the channel ChoiceTranslate creates
at the carrier's point (quirk C3) all follow this pattern. A separate field
sort, considered in review, would place those channels away from the field
where the message has to deliver them and lose these programs. A created end
and an unrelated carried end at one point are harmless. Points need not be
linear (plan §2, G3), and readiness between two ends at one point fails,
because x ≺ x̄ is no fact and ≺_W is strict. So a coincidence costs at most a
typing, never soundness, and it touches no counterexample of Appendix B.

**Two creations at one anchor and one label.** Two `new_κ o` before o acts
give two channels at x.κ. Typing admits it, for the reason above, and then
no thread may wait on one of the two while it holds the other. No example
of CostEx.v or of the deadlock-freedom examples needs this (to confirm in
S2). Distinct labels, or an action on the anchor in between, give distinct
points.

### 2.4  Worlds

**Job.** The order. Nothing else.

```
W = (A, ≺_A, (Λ_ℓ)_{ℓ ∈ L})
  A       finite set of constants
  ≺_A     facts between points with constant roots
  L       finite set of family labels
  Λ_ℓ(r)  laws of family ℓ, facts between points whose root is the variable r
≺_W = transitive closure of  ≺_A ∪ ⋃_{ℓ, g ∈ G_ℓ} Λ_ℓ(g) ∪ { x ≺ x⁺ } ∪ { x ≺ x̄⁺ }
```

Every generated root is known and obeys the laws of its family, so W is
constant along every run although runs create roots. `world_wf` keeps the
fields of relation/Worlds.v:106. `strict W` asks ≺_W irreflexive. The
lock-free world asks in addition `well_founded ≺_W`, one record instead of
three names (quirk A14).

**Laws per family, not per program.** A law speaks of one root variable and
of nothing else, so two generated roots are never ordered against each
other, and a law never meets a constant. Then ≺_W restricted to generated
roots is the disjoint union of the families, and W is strict (well founded)
iff ≺_A and every Λ_ℓ are. The join W1 ⊔ W2 unions constants, facts and
families after renaming the families of one side apart. Family labels never
reach the runtime, so relabelling a component is a renaming lemma like the
one for channel names (to prove). Two components whose laws contradict
therefore never meet in one family, and P-Connect asks only the strictness
of the constant part at the interface (cleanup R7). Version 1 had one global
Λ, under which such a pair made every join non-strict (review point 3).

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
new_ℓ        →  c⁺ : S@g,    c⁻ : S̄@ḡ       g ∈ G_ℓ a generated root fresh for Θ
new_κ o      →  o unchanged, c⁺ : S@x.κ, c⁻ : S̄@(x.κ)‾      where Θ(o) = _@x
```

`new_κ o` is anchored creation. It takes a held end o, returns it untouched,
and creates the channel at the field κ of o's point. The anchor
is threaded linearly, so the term mentions o and gives it back, and no point
occurs in the program. ℓ and κ are labels like a branch label. A program
with one family writes `new` for `new_ℓ`. The static types are

```
new_ℓ : 1 ⊸ ∃ρ. Λ_ℓ(ρ). (S@ρ ⊗ S̄@ρ̄)
new_κ : S0@x ⊸ S0@x ⊗ (S@x.κ ⊗ S̄@(x.κ)‾)
```

A fresh root needs facts only from the laws of its family. A channel that must sit below
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

**A cycle created by main, under each option of Q2.** The client sends on a
and then receives on b, the server receives on a and then sends on b, both
forever.

```
main   = let (a, a') = new in let (b, b') = new in spawn (λ_. srv a' b'); cli a b
cli    = !(f = λa b. let a = send ⟨∗, a⟩ in let (_, b) = recv b in (force f) a b)
srv    = !(g = λa b. let (_, a) = recv a in let b = send ⟨∗, b⟩ in (force g) a b)
```

Round i of the client blocks on b at β + i while it holds a at α + i + 1.
Round i of the server blocks on a at α + i while it holds b at β + i. In the
hat shorthand (every polarity combination) readiness needs
α̂ + i ≺ β̂ + i ≺ α̂ + i + 1 for every i. The boxes are
`cli : □∀ι κ. C(ι,κ). S@ι ⊸ S'@κ ⊸ ∗` with C(ι,κ) = {κ̂+i ≺ ι̂+i+1 | i} and
`srv : □∀ι κ. C'(ι,κ). …` with C'(ι,κ) = {ι̂+i ≺ κ̂+i | i}, and each self
call instantiates at (ι⁺, κ⁺), where C and C′ reappear shifted.

- (a) global laws, version 1. main writes `new` and then `new_κ a`, so b sits
  at ρ.κ with Λ(r) = {r̂+i ≺ (r.κ)^+i ≺ r̂+i+1 | i}. Opening `new`
  gives ρ with Λ(ρ), and the forces at (ρ, ρ.κ) meet C and C′ from Λ(ρ).
  It types, but Λ holds for every generated root of the whole program and
  of every component it is joined with.
- (b) built-in laws only. ρ and ρ.κ are related by nothing beyond
  x ≺ x⁺ and x ≺ x̄⁺, so C(ρ, ρ.κ) fails. A plain second `new` gives a
  second root, and two roots are never ordered. Does not type.
- (c) anchors only, top-level channels as restrictions at constants. The
  program is written as the configuration ({a, b}, {cli a b, srv a' b'}),
  the derivation places a at α and b at β with the facts above in W, and
  the soup fixes these points once outside the index (P0). Types, but main's
  two `new`s become process-level restrictions.
- (d) family laws, proposed. As (a), with `new_ℓ` and the laws Λ_ℓ of that
  family. The same typing, and composition renames ℓ apart (§2.4).

**What `new_ℓ` writes into a program.** `new_ℓ` adds one label ℓ, drawn from
a finite set of names, to an anchorless `new`. It is no point, no offset and
no field, and it never appears in a type as a point. The runtime erases it,
because the step of `new_ℓ` is the step of `new`. The label is read by the
typing rule E-New, which opens the fresh root ρ with the hypotheses Λ_ℓ(ρ),
and by the relation, which places the channel at a root of G_ℓ. The closest
relative is a select label. The difference is that the runtime reads a
select label to pick a branch and never reads ℓ. A program with
one family writes plain `new`, so ℓ appears only in programs that need two
families with different laws. Q2 (c) writes no label at all, and in exchange
the channels whose facts relate them to one another are created by the
process syntax, as restricted names of the initial configuration, whose
points the derivation picks. Side by side, for the client and server cycle:

```
(d) families                                   (c) restrictions at constants
main = let (a, a') = new_ℓ in                  ({a, b},
       let (a, ⟨b, b'⟩) = new_κ a in             { cli a b,
       let () = spawn (λ_. srv a' b') in          srv a' b' })
       cli a b
W :  Λ_ℓ(r) = { r̂+i ≺ (r.κ)^+i ≺ r̂+i+1 | i }    W :  constants α, β with
                                                    { α̂+i ≺ β̂+i ≺ α̂+i+1 | i }
points:  a at a fresh ρ ∈ G_ℓ, b at ρ.κ          points:  a at α, b at β, fixed once in P0
```

The program text of (d) differs from today's source program only in the
anchor of b. The text of (c) is no longer an expression but a configuration.
A factory that creates related channels at run time, with no end to anchor
at, has no form under (c) (FactoryEx, Appendix B.1).
### 2.6  Readiness and futures

**Job.** Readiness, ready_W, excludes circular waiting.

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
at three clauses (O-Spawn, O-Send, Q-Send) and nowhere else.

**What the author has agreed to, and what not.** The author allowed syntax
in the relation at a send, where the semantics extrudes scope by syntax
(decision 2026-11-16). The transfer set at a spawn is a new syntactic fact
read by the relation. Under the standing rule it needs the author's explicit
agreement, and this proposal asks for it (Q3). It replaces `tenv_fit` in
`Vspawn`, which reads the closure's ends today (LiveRelation.v:246), so the
amount of syntax read at a spawn does not grow. It reads the label instead
of the term.

**Why a spawn needs it.** The soup fixes which thread owns which end outside
the index (§2.12), because the rank and the counters of adequacy are read
off owners. O-Spawn splits Θ into the child's part and the parent's part.
Without a fact that fixes the split, the split is an existential inside each
index, and a thread that holds an end that neither the child nor the parent
mentions can give it to either side at different indices. Then no ownership
is the same at every index (the problem of §4.2, for owners instead of
points). The transfer set is the one index-free source of the split.

**An alternative without it, and why it is worse.** A spawn moves no
ownership. The typing rule of `spawn` asks a thunk that holds no end, and a
thread hands ends to a child by a message on a fresh channel, `spawn⟨X⟩ e`
being sugar for `let (c, d) = new in spawn (λ_. let ⟨X, _⟩ = recv d in e);
send ⟨X, c⟩`. Only the send reads its transfer set. The price is one
channel and one synchronization per spawn, a counter unit per handed end,
and readiness facts for the parent's send on c against every end it keeps,
which a fresh root cannot supply without an anchor. GrowRing and every
example that spawns a closure over ends would change. Unchecked against the
examples. Ownership has to
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

What the transfer sets replace. `fends eb = tenv_ends Θ` of the base arrow
(LogicalRelation.v:123), `tenv_fit` and `tenv_bipol` of the live arrow and
`Vspawn` (LiveRelation.v:246, 343), `fchans eb = ∅` of V-Box
(LogicalRelation.v:160), `dom π = fends w` and `fends eb = ∅` of `Vfuel`
(LFFuel.v:360, 366), the reading of `fends w` in `fchild` and in the spawn
and send clauses of `Fobl` (LFFuel.v:149, 233, 243), `term_wf` (LogicalRelation.v:1116),
and the `cfacts` premises of C-Abs, C-Box and C-SpawnLam (plan §19.14.6).

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

**One arrow for both tables.** The arrow reads its body at every level
j ≤ n − κ(β). κ_DF gives j < n, today's base arrow
(LogicalRelation.v:119-131). κ_L gives j ≤ n, today's live arrow
(LiveRelation.v:343-348). At j = n the argument and the result are read at
the current level, so V_n recurses on the size of the type inside a level,
as `LVdef` does with its fuel on `tsize` (instantiation keeps the size,
`tsize_sinst`, so the box clause stays inside the recursion). The generic V
recurses on the pair (n, size T) for both tables, and for κ_DF the second
component is never needed. There is no constant case, because constants are
λ-values (§3.2).

**The bind lemma, once.** For an evaluation context K,

```
e ∈ E_n⟦T ≺ F ∪ F_K⟧(Θ1)
∀ W' ⊒ W, j ≤ n, Θv, v ∈ V_j⟦T⟧_{W'}(Θv).  K[v] ∈ E_j⟦U ≺ F⟧_{W'}(Θv ⊎ Θ2)
───────────────────────────────────────────────────────────────────────────
K[e] ∈ E_n⟦U ≺ F⟧(Θ1 ⊎ Θ2)
```

with F_K the heads of Θ2. It holds for every κ, because a step of the hole
is a step of K[e] at the same cost, so the levels the hole reaches are the
levels the composite reaches, and a value of the hole arrives at some level
j ≤ n. The proof is induction on n and, inside it, on the least fixpoint.
`LErel_bind` (liveness/LiveBind.v) is this lemma at κ_L.

E at level n is the least X such that for every W′ ⊒ W (decision Q9)

```
(stop)  e irreducible  ⇒ e ∈ V_n⟦T⟧(Θ)
(ready) e reducible    ⇒ ready_{W'}(Θ | F, e)
(step)  e →α e'        ⇒ Obl_α,  where "e' at Θ'" means X(Θ', e') if κ(α) = 0
                                          and e' ∈ E_{n−κ(α)}(Θ') otherwise
Obl β, force        e' at Θ
Obl new_ℓ           ∀ g ∈ G_ℓ fresh for Θ. ∃ S S' dual. e' at Θ, c⁺ : S@g, c⁻ : S'@ḡ
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
    new_ℓ        ∃ P Q dual. e' at Π + {c⁺ ↦ P, c⁻ ↦ Q}, φ + {c± ↦ N}
    new_κ o      the same
    act on o     (F-Tick) every other counter ≥ 1 and d ≥ 1.
                 e' at φ' = (φ − 1 off o)[o ↦ N], Π advanced at o, frame d − 1
    send o w, M  M ⊆ dom φ ∖ {o}, φ|M ≥ 1, w ∈ Vfuel^N_n⟦pay(Π o)⟧(Π|M, (φ − 1)|M),
                 e' without M, plus the tick of "act on o"
    recv o w     ∀ j ≤ n, Π_in, φ_in, w ∈ Vfuel^N_j⟦pay(Π o)⟧(Π_in, φ_in).
                 e' at level j with Π_in and φ_in added, plus the tick
    spawn w, M   M ⊆ dom φ, φ|M ≥ 1. The child satisfies FuelE^N_n⟦thread⟧
                 at (Π|M, (φ − 1)|M, ⌈tk/2⌉, w ∗). e' at ⌊tk/2⌋ without M
    link M       M ⊆ dom φ, tk ≥ 1, e' at tk − 1
fsem^N(φ0, e) ⇔ ∃ tk, ∀ n, ∃ Π. FuelE^N_n⟦thread⟧(Π, φ0, tk, e)
```

`act on o` covers send, receive, close, select and branch.

**No hand-over at counter 0.** Subtraction on ℕ truncates, so a hop at 0
would pass 0 again for free, and an end could travel forever while its
partner waits (endless delegation, plan §1 pattern 2, Padovani's Example (2),
`starve_not_spare`). The send clause therefore states φ|M ≥ 1. It is implied
by F-Tick, because a send is an action on o and M ⊆ dom φ ∖ {o}, so the
clause that enforces it is F-Tick, and the explicit conjunct only makes the
hand-over rule read the same at send and at spawn. A spawn is no action, so
there the conjunct φ|M ≥ 1 is the only enforcement. A link hands on no
counter (it spends a ticket). Every counter passed on is therefore the
holder's counter minus one with no truncation, which is what `fuel_step` of
adequacy uses (LFAdequacy.v). `⟦thread⟧` is the
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

LF(W, Σ, T, p)  ⇔  (∀ n, p ∈ P[live]^W_n⟦Σ ⊢ T⟧)  ∧  ∃ N a. erase q = p ∧ ∀ n, Soup^N_n(W, Σ, T, a)
```

Along a run, P, φ and K follow the events deterministically. Placement gives
new points, actions move points, transfers move entries with counter − 1,
links spend a ticket and rename. The preservation lemma is today's
`lfsoup_step` (LFSoup.v:2592).

**The process conjunct stays.** LF is the live process relation and the fuel
soup, the structure the author approved (2026-11-16), so lock freedom reads
as deadlock freedom plus a per-thread view. Adequacy takes no τ-divergence
from the first conjunct (`live_no_tau_divergence`, as today) and
composition composes it by the live P-Connect and P-Join. The conjunct may
go only when a Rocq proof of

```
soup_no_tau_divergence : (∀ n, Soup^N_n(W, ∅, T, a)) → no_tau_divergence (erase q)
```

exists. The argument for it is that a spawned thread's τ prefix belongs to
its parent's least fixpoint (`Vspawn` reads the child at the parent's level,
LiveRelation.v:242-252), so the τ steps between two channel steps of the
soup form a finite tree. Until then the design keeps both conjuncts.

**The infinite spawn chain.** Each thread creates a channel, spawns a child
that does the same, and waits.

```
f = !(f = λu. let (c, d) = new in spawn (λ_. let () = (force f) ∗ in close d); close c)
```

The run is new, spawn, β, new, spawn, β, … with no channel step, and main
waits on c forever. The live relation rejects it at the first thread. O-Spawn
asks the child at the parent's level inside the parent's least fixpoint, and
the child asks its own child there too, so no finite derivation exists at any
level n ≥ 1. This is `kob_not_live` and `kob_tau_diverges` for
KobForwarder (liveness/LiveKob.v), which has this shape. The soup's
per-thread conjunct rejects it the same way, so the example does not need
the process conjunct. Fuel and rank play no part, because no thread that
holds a waited end is ever pending.

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

The live process conjuncts compose by the live P-Connect and P-Join, the
soups concatenate, P0, φ0, K0 union, families are renamed apart, and N is
the larger of the two.
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

### 2.16  Merges considered

- **The guard as an instance of the cost judgment. Rejected.** The guard asks
  a lower bound, at least one channel action of a round before the self is
  forced, and its soundness lands in the live relation (`noret`,
  liveness/LiveGuard.v). The cost judgment carries upper bounds, at most c
  actions before a return, read only by FuelE. A merged judgment would carry
  both bounds, and the live fundamental theorem would then read cost
  derivations, so the live layer would depend on the lock-freedom layer.
  The bound for a received closure would also have to sit in the live value
  relation, which reads no cost (plan §19.4, T1).
- **Cost protocols as session types with credits, one judgment. Open (Q11),
  recommended.** Types carry the cost annotations (credits, the arrow's c, t
  and h, credits on payloads), and one judgment Θ ; Γ ; Δ ⊢^F t : T ▷ c ; t
  replaces typing and the cost judgment. DF and live ignore the annotations.
  FuelE then reads each end's protocol from the session type that the soup's
  environment A_t already gives it at that index, so Π, the pairing of cost
  protocols and the inference walk of plan §19.6 disappear. DF typing is the
  instance N = ∞ with every annotation ∞. Fresh ends get credit ∞, aging by
  ∞ keeps ∞ and a hand-over at ∞ meets its floor, so every DF derivation
  annotates (checked on paper in §2.17). The price is annotations on every type
  constructor, which the paper hides as the default ∞, and FuelE then reads
  the live environments, so stage S6 waits for S3. Plan §19.2 chose a
  separate judgment because `TLolli` and `TBox` occur 710 times, a cost of
  porting that a rewrite does not pay.
- **Futures and the arrow's upper point as one concept. Adopted as
  presentation.** A future F is the set of points the context still acts on
  after the term. The upper point u of T ⊸^u U is a lower bound on the
  futures under which the closure may run (u ≺ F, `ub_below`), and the static
  system already names that future by a variable φ with u ≺ φ (E-Abs). The
  paper presents one concept, the future, with arrows that bound their
  caller's future. The lower point l bounds the held heads (l ≼ heads Θ). F
  is a set and u a point, so the two stay distinct in Rocq.

### 2.17  The merged judgment of Q11, checked on paper

Types carry credits, T^a, and the arrow and the box carry a cost c, a
ticket transformer ϑ and, for the arrow, a floor h. A session payload
carries its credit, !(∃ῑ. T^b).S. The judgment is

```
Θ ; Γ ; Δ ⊢^F_{W,N} e : T^a ▷ c ; ϑ
```

with the readiness and future premises of today's rules unchanged and the
cost premises of static/CostTyping.v added. Γ − c ages every entry that
holds an end by c. The rules for send, receive, λ, application, spawn and
the two forms of `new` follow.

```
E-Send    ⊢ e : (T^a ⊗ (!(T'^b).S)@x) ▷ c ; ϑ       T ⊑ T'    a ≥ b + 1
          ──────────────────────────────────────────
          ⊢ send e : (S@x⁺)^N ▷ c + 1 ; ϑ

E-Recv    ⊢ e : (?(T^b).S@x) ▷ c ; ϑ
          ──────────────────────────────────────────
          ⊢ recv e : (T^b ⊗ (S@x⁺)^N)^0 ▷ c + 1 ; ϑ

E-Abs     Θ^h ; Γ ; Δ^h, x : T ⊢^{φ}_{W,N} e : U ▷ c ; ϑ    h + a ≤ every captured credit
          ──────────────────────────────────────────
          Θ ; Γ ; Δ ⊢^F_{W,N} λe : (T ⊸^u_l[c ; ϑ ; h] U)^a ▷ 0 ; 1̂

E-App     ⊢ e1 : (T ⊸^u_l[c ; ϑ ; h] U)^{a1} ▷ c1 ; ϑ1    (context − c1) ⊢ e2 : T ▷ c2 ; ϑ2    a1 ≥ c2
          ──────────────────────────────────────────
          ⊢ e1 e2 : U ▷ c1 + c2 + c ; ϑ1 ∘ ϑ2 ∘ ϑ

E-Spawn   Θ − 1 ; Γ ; Δ − 1 ⊢ e : 1 ▷ c' ; ϑ'
          ──────────────────────────────────────────            (C-SpawnLam)
          Θ ; Γ ; Δ ⊢ spawn (λ_. e) : 1^∞ ▷ 0 ; tspawn(ϑ'(0)) 1̂

          ⊢ e : (1 ⊸[c' ; ϑ' ; h] 1)^a ▷ c0 ; ϑ0    a ≥ 1
          ──────────────────────────────────────────            (C-Spawn)
          ⊢ spawn e : 1^∞ ▷ c0 ; ϑ0 ∘ tspawn(ϑ'(0)) 1̂

E-New     ⊢ new_ℓ : (∃ρ. Λ_ℓ(ρ). (S@ρ)^N ⊗ (S̄@ρ̄)^N)^0 ▷ 0 ; 1̂

E-NewAt   ⊢ e : (S0@x)^a ▷ c ; ϑ
          ──────────────────────────────────────────
          ⊢ new_κ e : ((S0@x)^a ⊗ ((S@x.κ)^N ⊗ (S̄@(x.κ)‾)^N)^0)^0 ▷ c ; ϑ
```

The counterexamples it touches.

- `cb_inf_not_aged`. A server that runs a callback of cost ∞ while it holds
  its client end ages that end by ∞ at E-App, and an end created by E-New or
  refilled after an action has credit N, finite for lock freedom. Rejected,
  by the same lemma on aging.
- `c3_link_loop_not_tix`. Transformers and their composition are unchanged,
  so a box that links once per round has no transformer with a finite need
  at 0. Rejected.
- `starve_not_spare`. E-Send asks a ≥ b + 1 between the credit of the
  payload and the floor b in the carrier's session type. An end that arrived
  at floor b and is forwarded at the same position asks b ≥ b + 1. Rejected.
- GrowRing with one floor per closure. E-Spawn keeps the C-SpawnLam form,
  so the derivation of `rg_ctyped` carries over. Types.
- The constant at arrow type of plan §19.14.4. `send` is λx. send x and E-Abs
  types it at its true result type, an end, so the substitution of the
  counterexample is ill-typed, and the semantic side is §3.2. Rejected.

**DF typing is the instance N = ∞.** Annotate a DF derivation with N = ∞,
every credit ∞, every cost ∞, floor 0 and every transformer (∞, ∞). Each cost
premise holds. Aging by ∞ keeps ∞, a ≥ b + 1 holds at ∞, a1 ≥ c2 holds at ∞,
E-Abs takes h = 0 and a = ∞. One change to the transformer domain is needed.
The offset of a transformer ranges over ℕ ∪ {∞} as its slope already does,
and `tok` holds when the first offset is ∞, which is sound because a need of
∞ is met at no finite ticket count. Without it, E-Link's ϑ ∘ (0, 1) violates
`tok` at slope ∞. Erasing the annotations of any derivation gives a DF
derivation. So the merged judgment is conservative over DF typing. Cycle.v
types this way, its two channels created by `new` and `new_κ` (Appendix
B.1), with every annotation ∞. GrowRing types this way after the reordering
of B.1. Both argued, no Rocq.

**Verdict.** Recommended. It replaces two judgments and the cost protocols Π
by one judgment whose DF instance is today's typing. It needs offset ∞ in
transformers and a conservativity lemma in S2.

## 3  Quirks and deviations

### 3.1  Quirks of docs/extensions/lock-freedom-quirks.md

| Quirk | Fate | How |
|---|---|---|
| A1 value-level syntax | reduced to one | transfer sets in labels (§2.7). No V clause reads a term |
| A2 polarity bit | removed | end names c⁺, c⁻ (§2.2) |
| A3 two kinds of waiting | removed | only `lf_run_criterion` with ownership |
| A4 base and live are copies | removed | R^κ (§2.8) |
| A5 links cost 0 | stays | one entry of κ_L, a decision of the author |
| A6 `LFP` has two conjuncts | stays for now | kept as the author's structure. Dropped once `soup_no_tau_divergence` is proved (§2.12) |
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
| G1 soup to `LPrel` | open | either this lemma or `soup_no_tau_divergence` lets A6 go |
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
readiness of s at position k, read at index 1 (`s_rank`, LFAdequacy.v:229).
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
and a + 2(n − k). Every readiness fact holds in program order, W is well founded,
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
union is W_0 plus the laws of its family at every generated root, which is
well founded iff W_0 and every family's laws are. Such a world is constant in effect, because it knows
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
| extra concepts | point type, values, two constants | point expressions, instances at every force (453 lines in 83 files, plan §16.2), runtime point variables under E-Open | family laws Λ_ℓ, a family label on `new`, one anchored primitive | none | ranks, König | ω, preservation |
| author's constraints | violates (point values) | acceptable (box-bound), syntactic at force | met | met, but unsound | axiom | rejected 2026-11-09 |

Two further shapes were considered and fold into these. Ranks separate from
points (a rank per end in the soup) have the same problem at `new`, because
a fresh rank is a choice, and reduce to O3 or O5. A home point per thread,
advanced at each force, is O2 with the instance computed from thread state.
It needs a lexical rule for closures that are spawned, which makes it O2.

### 4.6  Recommendation

O3. Fresh generated roots with family laws, and anchored creation at fields
of held ends. It keeps every program point-free, makes placement a function of the
run, removes the point type, the point values, the creation hypotheses and
the box point parameters, and restores ChoiceTranslate and source-level
creation. Lock freedom keeps `well_founded ≺_W` as its only premise on W. DF
loses nothing against today's constant world. The cost is one primitive
variant, a family label on anchorless `new`, and the law component of W.
Four box types that create at a
parameter point (FactoryEx, FreshBetween, FreshMany, GuardCex) have to
anchor at an end or use a fresh root, and their typings are to be checked
first, in stage S2.

## Decisions taken (author, 2026-11-17)

- Q3. Transfer sets in the labels of send and spawn. The relation reads the
  moved ends from the label at O-Spawn, O-Send and Q-Send and reads no other
  syntax.
- Q2. Family labels. `new_ℓ` carries a label from a finite set, plain `new`
  when a program has one family. W gives laws per family, and composition
  renames families apart.
- Q5. Idle ends now, in the corrected form of §5 Q5 (b). An idle end keeps
  ticking, its "≥ 1" checks drop, and no thread acts on it. The rewrite
  builds this into the fuel layer from stage S6 on. One refill N otherwise
  (Q4).
- Q11. One judgment for session types and costs,
  `Θ ; Γ ; Δ ⊢^F_{W,N} e : T^a ▷ c ; ϑ`, with transformer offsets in ℕ ∪ {∞}.
  Deadlock-freedom typing is the instance N = ∞. The judgment is defined in
  stage S2, and S7 proves its cost half.
- Q13 (2026-11-17, after S2). A primitive `let x = e1 in e2` with its own
  τ step replaces the S2 rule that typed the redex (λx. e2) e1 as a let.
  A let is not a closure, so E-Let carries no lower point and captures
  every end of its context. No typing rule matches a redex shape.
- Q14 (2026-11-17, after S4.3). V at a λ asks dom Θ = the ends v mentions,
  and V at a box asks that v mentions no end. The author agreed to this
  syntactic clause explicitly. It is the clause V already has at a channel
  value. Without it Q3 is unsound, see `send_gap` (v2/compat/SendGap.v): a
  closure that mentions an end only in dead code is in V, and no send can
  hand it on. Q3 stays.
- The remaining questions take the recommendations of §5: Q1 (a), Q4 (a),
  Q6 (a), Q7 (a), Q8 (a), Q9 (a), Q10 (a) if the bind lemma survives it,
  Q12 as stated.

## 5  Open decisions for the author

**Q1. Placement.** (a) O3 anchors and generated roots. (b) O2 box-bound
point expressions with instances at force. (c) Keep point values.
Recommended (a). **Checked.** Index-free placement (§4), C1 (B #1-3), the
client and server cycle (§2.5), Cycle.v and the choice encoding with anchors
(B.1), FactoryEx with two variants of mk (B.1), the C2 pipeline (B.1),
GrowRing after one reordering (B.1), all on paper. **Not checked.** FreshMany,
GuardCex and SegmentInterleave, which create at a box parameter that no held
end carries, and every derivation in Rocq.

**Q2. Laws of generated roots** (§2.4, §2.5, review point 3). (a) One global
Λ, as in version 1. (b) Only the built-in laws x ≺ x⁺ and x ≺ x̄⁺. (c) No
laws, every runtime `new` that must be related to something is anchored, and
top-level channels are process-level restrictions whose points the
derivation picks and the soup fixes once (P0). (d) Laws per family, with a
family label on anchorless `new`, families renamed apart at composition.
Recommended (d). (a) makes joins fail for components whose laws contradict.
(b) cannot type the client and server cycle created by main (§2.5). (c)
needs no laws and no label but turns main's top-level `new`s into
restrictions in about 34 example files (plan §10.4). The family label is a
label like κ or a branch label and never names a point (§2.5). **Checked.**
The client and server cycle under all four options (§2.5), FactoryEx under
(d), where it types, and under (c), where it fails (B.1), strictness of joins
under (d) (§2.4). **Not checked.** The renaming lemma for family labels,
FreshMany, GuardCex and SegmentInterleave.

**Q3. The transfer condition** (§2.7, review point 7). The relation reads
the ends a step moves. At a send this is the syntax the author already
allowed for scope extrusion. At a spawn it is new syntax in the relation,
and the standing rule asks for the author's explicit agreement, which this
proposal does not assume. It replaces `tenv_fit` in `Vspawn` and in the
arrow, `fends eb = tenv_ends Θ`, `fchans eb = ∅` of V-Box, the `fends` reads
of `Vfuel` and `Fobl`, `term_wf` and three `cfacts` premises. A spawn needs
some such fact, because without it the split of O-Spawn is a choice per
index and ownership is not index-free. Options. (a) Transfer sets in the
labels of send and spawn. (b) Send only. A spawned thunk holds no end, and a
parent hands ends to a child by a message on a fresh channel, at the cost of
a channel, a synchronization and readiness facts per spawn (unchecked
against GrowRing and every example that spawns a closure over ends). (c)
The relation reads `fends w` at the same clauses, which is (a) without the
label. Recommended (a), with the spawn half subject to the author's
agreement, (b) as the fallback that reads no syntax at a spawn.
**Checked.** The argument that a spawn needs an index-free split, and the list
of conditions the transfer sets replace (§2.7). **Not checked.** Option (b)
against GrowRing and every example that spawns a closure over ends, and the
claim that a closure owning an end it does not mention is rejected by the
relation alone.

**Q4. Budgets.** (a) One refill N per judgment, maximum at composition.
(b) A refill per thread, fixed in the soup. (c) Budgets per point in the
world (today). Recommended (a). **Checked.** Every derivation of CostEx.v uses
one budget per program, and adequacy reads counters and tickets only (§4.1,
§4.4). **Not checked.** FuelE monotone in the counters and in N, which the
maximum at composition needs.

**Q5. Ends nobody waits on** (review point 4). What (a) loses is the class
of plan §7. A thread holds an end forever while it loops, and nobody ever
waits on its partner, as in the controller, where server and client each
hold one end of ctl and never use it. Under (a) the holder's counter of ctl
reaches 0 and F-Tick stops it. No current example or test has this shape.
`ctl` and "controller" occur in no file of theories/ (checked by grep), and
CostEx.v, ChoiceEnc.v and Ordered.v contain no end held forever. The
controller was never proved (quirk A12). Options. (a) Drop. (b) Idle cost
protocols. If idleness changed how a counter evolves, the counters would
depend on the index, because protocols are chosen per index (§4.4), and (b)
would be unsound. (b) is sound only in this form. Every counter evolves
the same way at every index (refill N at an action, minus one at every
other action of its holder, minus one at a hand-over, truncated at 0), and
idleness only removes checks at that index. F-Tick's "≥ 1" and the
hand-over's "≥ 1" are not asked of an idle end, and no thread may act on an
idle end (F-Wait). Adequacy reads the checks only for the partner ō of an
end o that a pending thread waits on. That thread acts on o at every index
the proof reads, so F-Wait makes o non-idle there, and pairing makes ō
non-idle at the same index. φ stays index-free. Recommended (a) now, (b) as
an extension. **Checked.** No example or test needs (b) (grep), and the
adequacy argument for the corrected (b) on paper (B.1, #44). **Not checked.**
A Rocq proof, and a typing of the controller.

**Q6. One relation.** (a) R^κ with a cost table for DF and Live.
(b) Two copies as today (decision 2026-11-16 for the current development).
Recommended (a) for the rewrite, because the copies are an artefact of
Rocq (quirk A4) and the paper already presents liveness as the DF relation
with the τ clause made inductive. **Checked.** The two cost tables reproduce
today's costs, and the arrow and the bind lemma read the same for both
(§2.8). **Not checked.** Internalize over κ and `live ⊆ DF`.

**Q7. Constants.** (a) Saturated operators, constants as derived λ-values.
(b) Constants as values with a β-like step `App k v → op v`. (c) Today's
η-restriction. Recommended (a). (b) is the same up to one definition.
**Checked.** The counterexample of plan §19.14.4 has no form under (a)
(§3.2). **Not checked.** Nothing beyond the port.

**Q8. Spawn in the cost judgment.** (a) C-SpawnLam and C-Spawn both.
(b) Per-end floors on arrows, so C-Spawn alone types GrowRing. (c) Only
C-SpawnLam, with `spawn v` sugar for `spawn (λ_. v ∗)`. Recommended (a).
**Checked.** GrowRing types by C-SpawnLam (`rg_ctyped`, Rocq). **Not
checked.** Per-end floors.

**Q9. Kripke quantifier in E.** (a) In every unfolding, as the live relation
does. (b) Only at receive, with monotonicity as a lemma, as the base
relation does. Recommended (a), because it costs nothing in a least fixpoint
and gives monotonicity by definition. **Checked.** The live relation uses (a)
today. **Not checked.** The base proofs under (a).

**Q10. One clock.** (a) FuelE reads β at the same level, cost table κ_L.
(b) Every step costs one in FuelE. Recommended (a) if the bind lemma F1
survives it, otherwise (b). **Checked.** Nothing. **Not checked.** F1 with β
at the same level.

**Q11. One static judgment for types and costs** (§2.16). (a) Types carry
cost annotations, DF typing is the instance N = ∞, FuelE reads protocols
from the session types of the soup. (b) A separate cost judgment, as plan
§19.2. Recommended (a), with offset ∞ in transformers. **Checked.** On paper,
the rules (§2.17), the five counterexamples it touches, and conservativity
at N = ∞ with Cycle.v and GrowRing. **Not checked.** A Rocq conservativity
lemma, and FuelE reading session types from the soup's environments.

**Q12. The process conjunct of LF.** Not a choice now. LF keeps
the live process conjunct until `soup_no_tau_divergence` is proved (§2.12).
**Checked.** The infinite spawn chain is rejected per thread (§2.12). **Not
checked.** `soup_no_tau_divergence`.

**Simplifications with unchecked entries in Appendix B.** Each needs its
check before it is adopted.

| Simplification | Unchecked entry |
|---|---|
| anchors and families instead of point values (Q1, Q2) | FreshMany, GuardCex, SegmentInterleave (FactoryEx, ChoiceNegative, Cycle, GrowRing, C2 now checked on paper) |
| one refill N (Q4) | monotonicity of FuelE in counters and N (G3) |
| idle protocols (Q5 b) | the controller (#20). Index-free counters checked on paper |
| send-only transfers (Q3 b) | GrowRing and every spawn of a closure over ends |
| dropping the process conjunct of LF | `soup_no_tau_divergence` |
| one judgment (Q11 a) | Rocq conservativity lemma. Checked on paper |
| one relation R^κ (Q6) | `live ⊆ DF`, Internalize over κ |
| derived constants (Q7) | none, §3.2 |

## 6  Rewrite plan

Each stage ends with a full build, no `Admitted`, no axiom and a regenerated
CheckAll. At most two stages run at once. Each stage delivers the notations
and names of Appendix A for what it defines, in its own `Notations` module,
and states every theorem in them from the first commit. No notation is added
afterwards.

| Stage | Content | Proves | Reuse |
|---|---|---|---|
| S1 language | a lexer test of every token of Appendix A first, then ends c⁺ c⁻, saturated operators, derived constants, `new_ℓ`, `new_κ`, events with transfer sets and thread ids as one semantics with erasure, one `emap` and `csub`, constructors named after the T-Act and P-Act rules | safety, harmony, thread simulation, `act_offer` once | lang/ (Syntax, Semantics, Safety, Harmony, ThreadSim, ChannelSwap), lockfree/Instr.v, Fair.v, Reach.v, TauThread.v |
| S2 points, worlds, types | point algebra with generated roots of families, worlds with family laws, join with renaming apart, restriction, amalgamation, interface strictness (R7), `ty` without `TPt`, typing `Θ ; Γ ; Δ ⊢^F_W t : T` with E-New, E-NewAt, E-Op, two-world `Σ ⊢_W p : T`. Check FactoryEx, FreshBetween, FreshMany, GuardCex, SegmentInterleave, ChoiceNegative and the client and server cycle of §2.5 | world lemmas, `PointSubst` without `TPt`, renaming of generated roots and of families | relation/Worlds.v without budgets, Creation.v reduced to the laws, types/, static/Typing.v, PointSubst.v, FactTheory.v |
| S3 generic relation | `sfix`, cost tables, `V[κ]^W_n⟦Θ ⊢ T⟧`, `E[κ]^W_n⟦Θ ⊢ T⟧^F`, `P[κ]^W_n⟦Σ ⊢ T⟧`, readiness `ready_W` | `adequacy` (DF), `live_adequacy`, downward closure, monotonicity | LogicalRelation.v and LiveRelation.v as templates, Readiness.v unchanged |
| S4 generic compatibility | bind, operator redexes, Internalize, P-Connect, P-Term, P-Join, renaming, all over κ, named `sem_<rule>` and `live_<rule>` | the composition lemmas for both instances, `live ⊆ DF` | liveness/Live*.v (the newer proofs) as the template, composition/ for the base specifics |
| S5 static fundamental theorems | E-rules into R^{κ_DF}, guarded rules into R^{κ_L} | `fundamental`, `live_fundamental_guarded`, `soundness`, `live_soundness`, source soundness with creation | static/Fundamental.v, liveness/GuardRules.v, LiveGuardFund.v |
| S6 fuel | FuelE^N, Vfuel by cost types, F1 to F6, monotonicity in counters and N, renaming | `FuelE_bind`, `Vfuel_recount`, `FuelE_mono` | lockfree/LFFuel.v and LFFuelBind.v minus points, caps and `wbext` |
| S7 cost judgment | rules of §2.11, compatibility per rule | `ctyped_fsem` | static/CostTyping.v, lockfree/CostFund.v minus C-Pt, C-Pay, C-Succ, C-Konst, `pfits` |
| S8 soup and adequacy | `Soup^N`, the deterministic update, `lfsoup_step`, `soup_no_tau_divergence` | `lf_adequacy`, `lf_thread_progress` | Criterion.v unchanged, LFSoup.v and LFAdequacy.v without π, `pupd`, `pev`, `fsolo` |
| S9 lock-free composition and soundness | `lf_p_term`, `lf_p_connect`, `lf_p_join`, the judgment `Σ ⊩^N_W p : T` | `lf_fundamental`, `lf_soundness`, examples | LFCompose.v, LFTyped.v, examples/CostEx.v and CostFsem.v, Rank.v |
| S10 paper | one relation, two cost tables, a fuel layer and a soup, every statement in the strings of Appendix A, checked by paper/rocqrefs.py against `Check` output | | paper/ |

Ordering. S1 and S2 first, alone. S3 and S6 can run in parallel, because
fuel reads no relation. S4 and S7 in parallel. S5 after S4. S8 after S5 and
S6. S9 last. Translations (PGV, PN, MP) stay out until S5 and need only the
removal of point values from their targets.

Statements that change form, for the author's approval. `LFP` keeps its
first conjunct and gains N. `LFP_connect` and `LFP_join` lose `wbud_agree`
and gain renaming apart of families. `LFP_term` loses the known-points
premise. `lf_criterion` goes, and `lf_run_criterion` keeps its text. Every
typing lemma of an example loses `created` and point literals. Every
statement takes the notation and name of Appendix A.

## Appendix A  Notation and statements

The Rocq statements read as the paper's statements. Both use the strings of
this appendix.

### A.1  Spelling rule

A Rocq notation is the paper's LaTeX with `^` for a superscript, `_` for a
subscript and no braces. The paper typesets that same string. A
multi-character index sits in brackets in both (`V[live]`). Every token is
checked by a lexer test at the start of stage S1. A token that Rocq cannot
lex is replaced in both places at once, never in one.

### A.2  Judgments

| Judgment | Paper and Rocq notation | Rocq definition |
|---|---|---|
| order fact | `W ⊢ x ≺ y` | `w_lt W x y` |
| world extension, join | `W ⊑ W'`, `W1 ⊔ W2` | `wext`, `wjoin` |
| lock-free world | `lfworld W` (strict and well founded) | `lfworld` |
| readiness | `ready_W(Θ ∣ F, t)`, `ready_W(Σ, p)` | `ready_t`, `ready_p` |
| static term typing | `Θ ; Γ ; Δ ⊢^F_W t : T` | `typed` (Γ the facts and future hypotheses) |
| static process typing | `Σ ⊢_W p : T` | `ptyped` |
| guard | `guarded t` | `guarded` (rules `glive`) |
| cost typing | `Θ ; Γ ⊩^N e : σ ▷ c ; t` | `ctyped` |
| lock-free process typing | `Σ ⊩^N_W p : T` | `lfptyped` |
| value relation | `v ∈ V[κ]^W_n⟦Θ ⊢ T⟧`, `[κ]` omitted for κ_DF | `Vrel κ n W Θ T v` |
| term relation | `e ∈ E[κ]^W_n⟦Θ ⊢ T⟧^F` | `Erel` |
| process relation | `p ∈ P[κ]^W_n⟦Σ ⊢ T⟧` | `Prel` |
| semantic term typing | `Θ ; Δ ⊨^F_W t : T` (DF), `Θ ; Δ ⊫^F_W t : T` (live) | `sem_typed κ` |
| semantic process typing | `Σ ⊨_W p : T` (DF), `Σ ⊫_W p : T` (live), `Σ ⊪_W p : T` (lock-free) | `sem_ptyped κ`, `lf_sem` |
| fuel | `e ∈ F^N_n⟦σ ▷ c ; r⟧(Π, φ, tk)`, `v ∈ FV^N_n⟦σ⟧(Π, φ)` | `FuelE`, `Vfuel` |
| semantic cost typing | `Θ ; Γ ⊨^N e : σ ▷ c ; t` | `csem` |
| soup | `a ∈ S^{N,W}_n⟦Σ ⊢ T⟧` | `Soup` |

### A.3  Theorems

| Paper statement | Rocq name |
|---|---|
| `∅ ⊨_W p : T  ⟹  deadlock_free p` | `adequacy` |
| `∅ ⊫_W p : T  ⟹  deadlock_free p ∧ no_tau_divergence p` | `live_adequacy` |
| `strict W ∧ Θ ; ∅ ; Δ ⊢^F_W t : T  ⟹  Θ ; Δ ⊨^F_W t : T` | `fundamental` |
| `strict W ∧ Σ ⊢_W p : T  ⟹  Σ ⊨_W p : T` | `fundamental_proc` |
| `… ∧ guarded t  ⟹  Θ ; Δ ⊫^F_W t : T`, and for processes | `live_fundamental`, `live_fundamental_proc` |
| `strict W ∧ ∅ ⊢_W p : T  ⟹  deadlock_free p` | `soundness` |
| `strict W ∧ ∅ ⊢_W p : T ∧ guarded p  ⟹  deadlock_free p ∧ no_tau_divergence p` | `live_soundness` |
| `prim T ∧ ∅ ; ∅ ; ∅ ⊢^∅_W t : T  ⟹  (∅, {t}) deadlock free`, no creation constraint | `soundness_source` |
| `Θ ; Γ ⊩^N e : σ ▷ c ; t  ⟹  Θ ; Γ ⊨^N e : σ ▷ c ; t` | `cost_fundamental` |
| `lfworld W ∧ ∅ ⊪_W p : T  ⟹  lock_free p` | `lf_adequacy` |
| `lfworld W ∧ ∅ ⊪_W p : T  ⟹  every weakly fair maximal run makes every thread progress` | `lf_thread_progress` |
| `strict W ∧ Σ ⊩^N_W p : T  ⟹  Σ ⊪_W p : T` | `lf_fundamental` |
| `lfworld W ∧ ∅ ⊩^N_W p : T  ⟹  lock_free p` | `lf_soundness` |

The composition rules are rules of `⊢_W` and `⊩^N_W`, and each is valid for
the three semantic process judgments.

```
P-Term     Θ_B, Σ ; ∅ ; ∅ ⊢^∅_W t : T    dom Θ_B = C0, the ends of Θ_B paired and dual
           ──────────────────────────────────────────────
           Σ ⊢_W (C0, {t}) : T

P-Connect  Σ1, Σ_C ⊢_{W1} p1 : T    Σ2, Σ̄_C ⊢_{W2} p2 : 1    strict (W1 ⊔ W2)
           ──────────────────────────────────────────────
           Σ1, Σ2 ⊢_{W1 ⊔ W2} (C1 ∪ C2 ∪ dom Σ_C, p1 ∥ p2) : T

P-Join     as P-Connect, with strict (W1 ⊔ W2) replaced by the strictness of the
           join of the two worlds restricted to their shared names
```

The lock-free rules `⊩^N_W` add `fsem^N` to P-Term and nothing to P-Connect
and P-Join beyond renaming families apart.

### A.4  Naming rules

- A paper rule R-Name is the Rocq constructor `r_name`, lower case with
  hyphens as underscores. E-Abs is `e_abs`, P-Connect `p_connect`, C-Send
  `c_send`, T-Act-New `t_act_new`, P-Act-Msg `p_act_msg`, O-Po `o_po`.
- The lemma that validates rule R for the semantic judgment J is `J_r_name`,
  with J one of `sem`, `live`, `lf`, `cost`. Examples are `sem_e_abs`,
  `live_p_connect`, `lf_p_term`, `cost_c_send`.
- Clauses of a relation carry the paper's labels in comments, (stop),
  (ready), (step), O-Send, Q-Recv.
- A definition carries the paper's word. `ready`, `future`, `world`,
  `strict`, `lfworld`, `fuel`, `soup`, `lock_free`, `deadlock_free`.
  Readiness keeps its name everywhere, and fields are never called slots.

### A.5  Statements that read differently today

| Today | Difference | The rewrite |
|---|---|---|
| `typed W Φ Ψ Θ Δ F e T` | two hypothesis contexts Φ, Ψ, where the paper writes one Γ, and the world in a different position | one Γ, notation `Θ ; Γ ; Δ ⊢^F_W t : T` |
| `sem_typed W Θ Δ F e T` with `term_wf` at E-Abs, E-Box | the paper states the side predicate wf(Θ ; Δ, t) | no `term_wf` (§2.7), the paper drops wf |
| `Prel_connect`, `conn_all` | lands in `wjoin W1 W2`, the paper rule P-Connect is one-world and its proof returns by monotonicity | P-Connect is two-world in both |
| `pt_term`, `pt_connect`, `lf_term`, `lf_connect` (the latter in P-Join form, LFTyped.v) | names and forms differ from P-Term, P-Connect | `p_term`, `p_connect`, `p_join` in `⊢_W` and `⊩^N_W` |
| `Prel_term`, `LPrel_term`, `LFP_term`, `LFP_connect`, `LFP_join` | names | `sem_p_term`, `live_p_term`, `lf_p_term`, `lf_p_connect`, `lf_p_join` |
| `LFP_term` premises `lsem_typed`, `tenv_dual (w_eq W) ΘB`, known points | not the premises of P-Term | the premises of P-Term plus `fsem^N` |
| `soundness_created`, `soundness_source` with a creation constraint | two theorems, a constraint the paper explains at length | one `soundness_source` without a constraint |
| `live_fundamental_guarded` over `gtyped` | name and an extra judgment | `live_fundamental` over `⊢_W` and `guarded` |
| `lf_adequacy` premises `world_wf W`, `well_founded (w_lt W)` | two premises | `lfworld W` |
| `ctyped_csem`, `ctyped_fsem` | names | `cost_fundamental`, `fsem_of_cost` |
| `w_eq` and `tenv_comp (w_eq W)` in statements | no-eq leftovers | `=` and `Θ = Θ1 · Θ2` |
| liveness and lock freedom | no paper statement yet | the forms of A.2 and A.3 enter the paper in S10 |

## Appendix B  Counterexamples and rejections

Status. **R** handled, with a Rocq lemma today that the rewrite ports.
**D** handled by the design, argued. **M** moot, the mechanism it attacked is
gone. **U** unchecked.

| # | Counterexample or rejection | Source | Handled by | Status |
|---|---|---|---|---|
| 1 | C1 with a ceiling | plan §14.1 | rank on index-free placement, `c1_rank_fails` for the world facts | R |
| 2 | C1 without a ceiling | plan §17.2, scratch C1World.v | rank on index-free placement (§4.2) | D |
| 3 | C1′, points shifted upward | plan §10.1 | rank | D |
| 4 | C2 pipeline, lock free, rejected by the old R3 | plan §10.1 | types under the design (B.1) | D |
| 5 | C3 link refresh with a chatter step | plan §10.1 | tickets, `c3_link_loop_not_tix` | R |
| 6 | C4, R4 rejected the Forwarder | plan §10.1 | the Forwarder types, `fw_ctyped` | R |
| 7 | postponement, a holder loops and never serves | plan §8, liveness.md §9 | F-Tick, aging in the cost judgment | D |
| 8 | endless delegation, Padovani's Example (2), the starving server | plan §1, §8 | send asks φ|M ≥ 1 (F-Tick), floors, `starve_not_spare` | R |
| 9 | hop at counter 0 under truncation | review point 1 | φ|M ≥ 1 at send and spawn (§2.10) | D |
| 10 | growing chain with a chatterbox | plan §8 | rank | D |
| 11 | link loop `rec f. new; link; f ()` | plan §8 | link costs 0, τ-divergence in κ_L | D |
| 12 | KobForwarder | LiveKob.v, GuardEx.v, Rank.v | `kob_tau_diverges`, `kob_not_live`, `kob_not_guarded`, `kob_cworld_not_wf`, `kob_rank_fails` | R |
| 13 | PN's `⟨fix λx.x⟩` | GuardEx.v | `pn_div_not_guarded`, DF keeps its typing | R |
| 14 | the unguarded system types a τ-divergent program | LiveKob.v | `live_fundamental_false`, guard | R |
| 15 | the unrepaired guard | GuardCex.v | `cx_tau_diverges`, `cx_not_guarded`, `live_guarded_unrepaired_false`, guard rule L7 | R |
| 16 | index halving at a synchronization | sharp edge 44 | κ_L charges 2 | D |
| 17 | an end held across an infinite call | plan §8, R1 | aging by ∞ at C-App, `cb_inf_not_aged` | R |
| 18 | a server that serves b only on a's request | plan §8, R2 | credits fall below the argument floor | D |
| 19 | main returns an end | plan §8 | `prim T` | D |
| 20 | the controller | plan §7 | lost under Q5 (a), typed under Q5 (b) | U |
| 21 | C1 against the oracle on closed runs | plan §15.6 | no oracle | M |
| 22 | replacement against the send floor, Forwarder | quirk A13b, `fw_not_fsem` (deleted) | link tickets, no replacement | D |
| 23 | the Scheduler fails option 2 in every world | plan §18.1, `sched_not_fsem_all` (scratch) | link tickets, `sched_ctyped` | R |
| 24 | receive at unknown points | quirk A13c, `fuel_recv_unknown`, `sync_not_fsem` (deleted) | no budgets at points | M |
| 25 | merge of renamings | plan §19.8.1, Merge.v | `kinj` in FuelE | D |
| 26 | `new` reusing a held name | plan §19.8.2, Collide.v | new fresh against the thread's own ends | D |
| 27 | off by one at the value and the call | plan §19.8.3 | value clause at its level, body after β | D |
| 28 | context ticks without a frame | Frame.v, `bind_needs_bound` | the frame d | D |
| 29 | a received closure acts m + 1 times | plan §19.1 | arrow cost c, `cb_ctyped` | R |
| 30 | GrowRing with one floor per closure | plan §19.12 | C-SpawnLam, `rg_ctyped` (Q8) | R |
| 31 | a constant at arrow type | plan §19.14.4 | constants are λ-values (§3.2) | M |
| 32 | a box hides channel constants under an empty map | plan §19.14.3 | no V clause reads a term, a send of the box needs M ⊆ held | D |
| 33 | closure arguments without `fin_ok`, `fkont` without the cap | plan §19.14.1, 19.14.5 | no caps | M |
| 34 | a hole sends an end its context holds, or its own subject | plan §19.13.1 | M ⊆ dom φ ∖ {o} | D |
| 35 | select renames onto the partner's entry | plan §19.13.3 | end names | M |
| 36 | a renaming pushes a held end into a box inside a pair | plan §19.13.4 | disjoint split | D |
| 37 | `CAny` lets a context hold ends across an action | plan §19.12.4 | no `CAny` | M |
| 38 | link loop and spawn loop transformers | scratch Tix.v | transformers 2^s·r + b | D |
| 39 | two threads take turns linking the waiter's end | plan §18.4 | tickets are conserved and spent | D |
| 40 | infinite spawn chain | review point 5 | live relation per thread (§2.12), `kob_not_live` | R |
| 41 | a generated root reused after a link renamed its channel | this document, §2.5 | roots from a supply separate from channel names | D |
| 42 | two components with contradicting laws | review point 3 | families renamed apart (§2.4) | D |
| 43 | a created end and a carried end at one point | review point 2 | harmless under readiness and strictness (§2.3) | D |
| 44 | idleness changes counters per index | review point 4 | idleness removes checks only, adequacy proof on paper (B.1) | D |
| 45 | dropping a fresh conservative extension fails at V-Const | counterexamples/DropCounter.v, `force_notin_Wb` | no V-Const, no extension with chosen facts | M |
| 46 | one round is not enough, relay with one round | Rejected.v, `rr_call_underivable` | readiness unchanged | R |
| 47 | a box needs its constraint | Rejected.v, `ord_no_constraint` | readiness unchanged | R |
| 48 | reversed agents, a cyclic forwarding | Rejected.v, `sched_rev_underivable`, `ms_rev_underivable`, `badlink_underivable` | readiness unchanged | R |
| 49 | the negative control of the choice encoding | ChoiceNegative.v, `t2_underivable` and others | independent of placement, open since end points. The encoding itself types with anchors (B.1) | M |
| 50 | one payload point needs two contradicting facts | ChoiceEnc.v, `same_payload_not_acyclic` | restated over W it is `same_payload_cycle`, void since end points (B.1) | M |
| 51 | a box with a point of the first call | FactoryEx.v, `fx_no_first_call` | the first call needs no point. FactoryEx types with an anchorless and an anchored variant of mk (B.1) | D |
| 52 | no point between two box points | FreshBetween.v, `fb_between_underivable` | the box anchors at the end at ι | D |
| 53 | data branch without a derivation | DataBranch.v, `db_typed_false` | readiness unchanged | R |
| 54 | SemFlag underivable | SemFlag.v, `sf_underivable` | open since end points, outside this proposal | U |
| 55 | semantic deadlocks | GrowDeadlock.v `grow_not_df`, cfst/CfstDeadlock.v `dl_not_deadlock_free`, cfst/SkipDrop.v `sd_not_deadlock_free`, lit/LitRejected.v `pcx1`, `pcx2`, `msr`, `mcx2`, `mcx3` | facts of the untyped semantics, unchanged | R |
| 56 | rounds not eventually periodic | SemRounds.v, `rdfirst_not_periodic` | a fact of the program, unchanged | R |
| 57 | translations | mp/MPRounds.v `p8_not_mtyped`, pgv/PGVExamples.v `cx1_rejected`, `cx2_rejected` | out of the build | U |
| 58 | a chain descending in W | Rank.v, `chain_not_wf` | rank | R |

Totals. 58 entries. 20 R, 26 D, 9 M, 3 U, 0 fails. The unchecked ones are
20 (the controller, which depends on Q5), 54 (SemFlag) and 57 (the
translations), and 54 and 57 lie outside this proposal.

### B.1  The closed checks

**#4, the C2 pipeline.** Each stage receives on its input, creates a channel,
spawns the next stage on one end and sends on the other (plan §10.1).

```
stage = !(f = λin. let ⟨v, in⟩ = recv in in let () = close in in
                  let (a, b) = new in
                  let () = spawn (λ_. (force f) b) in
                  close (send ⟨v, a⟩))
in : ?∗.Close@ι      a : !∗.Close@ρ,  b : ?∗.Close@ρ̄,  ρ a fresh root
```

Readiness. A stage blocks on `in` while it holds nothing and on a while it
holds nothing, because b left with the child, so it needs no fact, and the
fresh root needs no law. Rank. The stage blocked on a waits on its child,
which is enabled at its receive, so no chain of waits grows. Fuel. b is
handed to the child at N − 1 ≥ 1 (N ≥ 2), a is acted on next, no other end is
held. Guard. The receive precedes the force of the self. Costs. The box has
cost 4 per force, the self is forced only inside the spawned thunk, typed by
C-SpawnLam with b at credit N − 1, and the transformer of a recursion that
spawns is (∞, 0) with no link. Types (argued). A streaming stage that keeps
`in` while it sends needs a below the partner of `in`, so it creates
a by `new_κ in` and states {x.κ+i ≺ x̄+i+1 | i} in its box constraint, the
pattern of the client and server cycle.

**#44, idle counters in the corrected form.** Counters evolve by the
index-free update, idleness removes F-Tick's "≥ 1" and the hand-over's "≥ 1"
for an idle end at that index, and F-Wait forbids acting on an idle end.
Adequacy instantiates `Hfuel` at a position k for a thread t pending on o,
whose partner ō the thread s holds, and reads the soup at index 3
(LFAdequacy.v, `fuel_step` from `Hrun k 3`). At index 3 the FuelE of t sees
its next step, the action on o, so F-Wait makes Π_3(o) non-idle, and the
soup's pairing at index 3 makes Π_3(ō) non-idle. So at index 3 s's F-Tick
asks φ(ō) ≥ 1 whenever s acts on another end, and a hand-over of ō asks
φ(ō) ≥ 1, and the index-free counter drops by one in both cases. That is the
first disjunct of `Hfuel`. Links lower the tickets as before. The proof
never compares idleness across indices, because it reads every position at
one fixed index. Handled (argued). The controller (#20) types under Q5 (b)
with both ends of ctl idle, and stays outside Q5 (a).

**#49, the negative control of the choice encoding.** The encoding first.
sel₁ creates (k, k′) at the carrier's payload field x[0], today by
`new` at a point value (ChoiceEnc.v:721), under the design by `new_0 c` on
the carrier c, which places the channel at x.0 = x[0] (fields ignore
polarity, so the dual carrier point gives the same field). sel₂ uses
`new_1 c`. The sent end k′ arrives at x[i], where V at the payload type
expects it. So `sel1_typed`, `sel2_typed` and `branch_typed` carry over with
the anchor in place of the point value. The negative control asks whether
T2 types when both arms share x[0]. With end points the two arms ask
δ ≺ x[0]‾ and x[0] ≺ δ̄, four distinct points and no cycle, which is why the
theorems are commented out (ChoiceNegative.v:404-577, "END POINTS: open").
Placement changes neither the points nor the facts of this question. Moot
for the proposal. It remains the open question of the end-points port.

**#50, `same_payload_not_acyclic`.** The lemma says that no top-level
creation constraint accepted by `soundness_source` contains δ ≺ a[0] and
a[0] ≺ δ (ChoiceEnc.v:479). Creation constraints go. Restated over the new
placement it reads "no strict world contains both facts", which is
`same_payload_cycle` (ChoiceEnc.v:472) at W, true by strictness. Its use, to
reject the shared-point program, is void since end points for the reason of
#49. Moot.

**#51, `fx_no_first_call`.** The lemma says that in the empty world no
instance exists for the first force of a box whose result names the box
variable (FactoryEx.v:258). Under the design the first call needs no point,
because mk creates at a fresh root. The second call must place q relative to
p, because main closes p while it holds q, and two generated roots are never
ordered (§2.4). Today the program already passes that information as a
point value derived from p (FactoryEx.v:59-60). Under the design it passes p
itself as the anchor.

```
mk₀ = !(f = λu. let () = u in let (c, c′) = new_ℓ in
              let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)
mk₁ = !(f = λp. let (p, ⟨c, c′⟩) = new_κ p in
              let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in ⟨p, c′⟩)
main = let p = (force mk₀) ∗ in let ⟨p, q⟩ = (force mk₁) p in
       let () = recvclose p in recvclose q
Λ_ℓ(r) = { r̄ ≺ r.κ, r̄⁺ ≺ r.κ }     mk₁ : □∀ζ. {ζ ≺ ζ.κ, ζ⁺ ≺ ζ.κ}. (?∗.Close)@ζ ⊸ …
```

Main receives and closes on p at ῑ_p and ῑ_p⁺ while it holds q at
(ῑ_p.κ)‾, and the facts come from the constraint of mk₁ at ζ = ῑ_p, the facts
Tmk1 states today. Handled (argued), at the price of two variants of mk
where today one term carries two types. Under Q2 (c) the factory fails,
because it creates related channels at run time with no law and no anchor
for the first call.

**GrowRing, found while checking Q11.** The ring creates b at X[1] after it
has closed x, so no end at X is held at that moment, and `new_κ` has no
anchor (GrowRing.v, `ring`). Moving `let (b, b′) = new_1 x` before
`recv x` anchors b at X[1] while x is held at X. The ring then holds b across
the receive and the close of x, which asks X ≺ X[1], X[1]‾ and
X+1 ≺ X[1], X[1]‾, and the constraint Cr already gives both (the last row of
Cr and X ≺ X+1). The credit of b falls by two before the hand-over, so the
budget may rise above `rg_ctyped`'s B = 4. Handled after the reordering
(argued). The design point involved is that anchored creation needs the
anchor held at the moment of creation.
