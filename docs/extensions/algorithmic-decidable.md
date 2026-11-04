# Decidable fragments of the fact theory

State of 2026-11-04. Companion to algorithmic-bidir.md, which generates the
constraints this file decides. Notation follows ORDERS-SPEC.md. p[j] is the
payload point, written `pt_slot x j` in Rocq. A point is (p, b), a name p at
offset b. Names are constants a, point variables ι and payload names (p, b)[j].
The fact theory of a hypothesis context Ψ is `heqs Ψ` and `hlt Ψ` of
static/Source.v, the least congruence for successor and payload points that
contains the ≡ facts, and the least relation that contains the ≺ facts and
program order x ≺ x+1 and is closed under ≡ and transitivity.

The questions. A constraint 𝒞 of algorithmic-bidir.md asks, in a context Ψ
given by the creation constraints in scope, for facts x ≺ y and x ≡ y
(entailment), for cc(C) (a creation constraint is acyclic and conservative),
and the whole program asks that its C₀ be acyclic (strictness). Three
fragments of constraints are decidable for all three questions. The fourth
section says what lies outside and why.

Tags. [known] is standard material, [derived] is proved here, [guess] is a
conjecture with what would refute it. Nothing in this file is mechanized.

## 1  Fragment 𝔇₁, finite ground constraints

A constraint is in 𝔇₁ when it is a finite set of facts x ≺ y and x ≡ y between
points over finitely many names. A whole program without boxes generates such
constraints, one per new plus C₀ (algorithmic-bidir.md, Section 7). Points
mentioned by the facts are the mentioned points M, names occurring in them and
their parent names are the mentioned names N, both finite.

### 1.1  The alias structure

An alias (p, a) ≡ (q, b) generates (p, a+k) ≡ (q, b+k) for every k ≥ 0 and
nothing at offsets below a and b. The ≡ classes of points are therefore
described by a weighted graph on N with a threshold per edge.

Alias graph. For each ≡ fact (p, a) ≡ (q, b) an edge p → q with potential
d = b − a and threshold a, and the reverse edge q → p with potential −d and
threshold b. A chain p = p₀ → p₁ → … → pₘ = q has potential Σdᵢ and threshold
max over i of (tᵢ − Σ_{j<i} dⱼ), the least offset of p from which every alias
of the chain applies. Let D(p, q) be the potential of a chain and T(p, q) the
least threshold over chains with that potential. Both are computed by a
Floyd–Warshall pass over N once the potentials are consistent.

Consistency. Two chains from p to q with different potentials d ≠ d′ give
(p, o) ≡ (q, o+d) ≡ (p, o + d − d′) for every large o, hence x ≡ x+k for some
k > 0, and with program order x ≺ x+k ≡ x the order is not strict. The
procedure reports this at once. Under consistency D is a function.

Payload congruence. (p, a) ≡ (q, b) gives (p, a)[j] ≡ (q, b)[j] at threshold 0
and potential 0 for the two payload names. The closure adds this edge for
every pair of mentioned payload names with equal index whose parent points are
≡ by the structure so far, and repeats until no edge is added. N is finite, so
this stops.

**Lemma 1 (aliases).** [derived] In the generated theory, (p, o) ≡ (q, o′)
holds iff p and q lie in one class, o′ = o + D(p, q) and o ≥ T(p, q).

Proof. The right side is closed under the generators. Every alias fact is an
edge. Reflexivity, symmetry and transitivity hold by chains and by the
composition rule for thresholds. Successor congruence raises o, which keeps
o ≥ T. Payload congruence is the added edges. Conversely every instance of the
right side is derivable along its chain by successor congruence and
transitivity. ∎

One point is a successor of another in the generated ≡ ∪ program order
exactly when one weak segment connects them.

**Lemma 2 (one segment).** [derived] For points x, y the relation
"x (≡ ∪ ≤_po)* y" holds iff there is a name p and offsets a ≤ a′ with
x ≡ (p, a) and y ≡ (p, a′). The segment is strict, that is some step is a
program-order step, iff a < a′.

Proof. Two consecutive segments x ≡ (p, a) ≤ (p, a′) ≡ (q, b) ≤ (q, b′) ≡ y
fuse, because (p, a′) ≡ (q, b) gives (p, a′ + k) ≡ (q, b + k) for k = b′ − b by
successor congruence, so x ≡ (p, a) ≤ (p, a′ + k) ≡ y. Induction on the
number of segments. ∎

With Lemma 1 the test is finite. x = (n, o) reaches y = (n′, o′) weakly iff some
name p of the common class has o ≥ T(n, p), o′ ≥ T(n′, p) and
o + D(n, p) ≤ o′ + D(n′, p). The inequality is independent of p by
consistency.

### 1.2  Strictness and entailment

Fact graph. Vertices are the mentioned points M. A strict edge x → y for each
≺ fact. A segment edge x ⇝ y when x reaches y weakly by Lemma 2, strict when
the segment is strict.

**Theorem 1 (𝔇₁ strictness).** [derived] The generated order is strict iff the
fact graph has no closed walk through a strict edge.

Proof. The generated order is (≡ ∪ ≤_po ∪ facts)⁺ with at least one strict
step, read on classes. A derivation of x ≺ x is a closed walk in that relation.
Cut it at the endpoints of its fact edges, which lie in M. Between two cuts the
walk uses ≡ and program order only, which is one segment by Lemma 2, hence a
segment edge of the fact graph. A closed walk with no fact edge is one segment
from x to x, strict only if a < a′ for one name, which contradicts x ≡ x and
Lemma 1 under consistency. Conversely every closed walk of the fact graph is a
derivation. ∎

Entailment. For Γ ⊢ x ≺ y with x, y over mentioned names, add x and y to M
and search for a walk from x to y through a strict edge. Γ ⊢ x ≡ y is Lemma 1.

Cost. The alias structure costs O(|N|³) for the Floyd–Warshall pass and one
congruence round per added edge, at most |N|² rounds. The fact graph has |M|
vertices and O(|M|²) segment edges, each decided in O(|N|). Cycle detection is
linear in the graph. The whole procedure is polynomial in the size of the
constraint.

### 1.3  Creation constraints

cc(C) for the new of a point ι asks that Γ + C be acyclic and conservative
over Γ (types/Types.v, `cc_ok`). In 𝔇₁ both Γ and C are finite. Two shapes
of C are decided here, and they are the two shapes the development proves
sound.

Shape A, order facts. Every fact of C is x ≺ y with at least one of x, y
rooted at ι. Write Lo for the facts u ≺ p with u outer and p rooted at ι, Hi
for the facts q ≺ v with q rooted at ι and v outer, and In for the facts
between two points rooted at ι. Let R be the closure of In and program order on
the points rooted at ι, decided by Theorem 1 on the names rooted at ι.

**Theorem 2 (shape A).** [derived] cc(C) holds iff R is irreflexive and for
every Lo fact u ≺ p and Hi fact q ≺ v with p ≼_R q, Γ ⊢ u ≺ v.

Proof. Sufficiency is `cc_model` of relation/Creation.v with φ the identity
and the two conditions as HRi and HB (`cc_ok_fresh` and `cc_ok_inner` are
its instances). Necessity. If R has a cycle, Γ + C has one through points of
ι, and Γ has none through them, so acyclicity fails. If u ≺ p, p ≼_R q, q ≺ v
and Γ ⊬ u ≺ v, then Γ + C derives u ≺ v between two outer points that Γ does
not derive, so conservativity fails. ∎

The second condition is finite. Lo and Hi are finite, p ≼_R q is Theorem 1 on
the ι names, and Γ ⊢ u ≺ v is entailment in 𝔇₁.

Shape B, one alias. C is the single fact ι ≡ w with w an outer point. Then
cc(C) holds whenever w is known, by `cc_ok_alias` of static/Fundamental.v. No
check is needed beyond knownness.

Other shapes, aliases between ι and several outer points or between payload
points of ι and outer points, are decidable in principle by the same method as
Theorem 1 on Γ + C, with conservativity checked on the mentioned outer points
and their shifts by the potentials of the new aliases. This file does not work
that case out. [guess] The check on mentioned outer points plus one shift per
alias potential suffices. A refutation would be a C with two aliases whose
composition relates two outer points mentioned nowhere.

### 1.4  Where 𝔇₁ falls short

C₀ of soundness_source is checked by Theorem 1 against the empty context,
which is the content of `c0_creation_ok` and `c0_acyclic`. A program whose
creation constraints are all finite is decided in full. The limit is
recursion. A box constraint is an invariant over all rounds and is infinite
as soon as a round moves a point.

## 2  Fragment 𝔇₂, one counter in the offsets

A schema is a fact with one counter k ∈ ℕ. 𝔇₂ allows, over finitely many names
N, finitely many facts of the following forms, with a, b, c constants and
δ = b − a.

```
shift      ∀k. (p, k+a) ≺ (q, k+b)                 edge p → q, effect δ, guard k+a ≥ a
alias      ∀k. (p, k+a) ≡ (q, k+b)
fan-down   ∀k. (p, k+a) ≺ (q, c)                  a fixed target
fan-up     ∀k. (q, c) ≺ (p, k+a)                  a fixed source
ground     (p, a) ≺ (q, b),  (p, a) ≡ (q, b)
```

The counter sits in the offset of each side and nowhere else. A payload name
(p, b)[j] with constant b is an ordinary name here. A counter inside the index
of a payload name is outside 𝔇₂ (Section 4).

Alias schemas add nothing. ∀k. (p, k+a) ≡ (q, k+b) and the ground alias
(p, a) ≡ (q, b) generate the same theory, by successor congruence. So the
alias structure of 𝔇₂ is that of 𝔇₁, Lemma 1 applies, and the rest of this
section assumes the ≡ facts have been resolved. Every name is its class
representative, a point below its threshold to the representative is kept as a
separate vertex (finitely many per name), and potentials have been added to
the offsets. [derived] This leaves a graph of the same shape with the same
cycles, because Lemma 2 fuses every ≡ step with its neighbouring program-order
steps into one offset comparison.

After resolution the generated order is the reachability relation of the
infinite graph 𝔊 with vertices (p, o), p ∈ N, o ∈ ℕ, and the following edges. Program order
(p, o) → (p, o+1), shift edges (p, o) → (q, o+δ) for o ≥ a, fan-down edges
(p, o) → (q, c) for o ≥ a, fan-up edges (q, c) → (p, o) for o ≥ a, and ground
edges. Every edge is strict. Strictness of the order is acyclicity of 𝔊.

### 2.1  Uniform schemas

𝔇₂ᵘ is the subfragment with shift schemas only, besides program order. The guards are the only
constants. Let 𝔊ᵘ be the finite weighted graph on N with an edge p → q of
weight δ per shift schema and a loop of weight 1 per name.

**Theorem 3 (uniform).** [derived] 𝔊 has a cycle iff some strongly connected
component of 𝔊ᵘ contains a closed walk of total weight 0. This holds iff some
component contains a simple cycle of weight ≤ 0 and a simple cycle of weight
≥ 0. It is decided in polynomial time.

Proof. A cycle of 𝔊 projects to a closed walk of 𝔊ᵘ whose weights sum to 0,
because the offset returns to its start, and all its vertices lie in one
component. Conversely let W be a closed walk of weight 0 in a component. Lift
it from an offset o₀ larger than every guard plus the length of W times the
largest |δ|. Every intermediate offset stays above every guard, so every edge
applies, and the lift closes. For the second statement, a closed walk of weight
0 contains a simple cycle, and removing it leaves a shorter closed walk, so the
walk is a sum of simple cycles with weights of both signs or a zero one.
Conversely take simple cycles A and B in one component with weights α ≥ 0 and
β ≤ 0, and a closed walk P that visits a vertex of A and a vertex of B, of
weight π. If α = 0 or β = 0 the cycle itself has weight 0. Otherwise let
g = gcd(α, |β|). Choose t ≥ 1 with g | tπ, for instance t = g, and integers m,
n with mα + nβ = −tπ. The solutions form the line (m₀ + j|β|/g, n₀ + jα/g), so
some solution has m, n ≥ 1. Traverse P t times, A m times and B n times along
P, which is a closed walk of weight 0. The decision computes the components, and in
each decide whether all simple cycles have positive weight and whether all have
negative weight. All simple cycles of a component have weight ≥ 1 iff the
weights w′ = |N|·w − 1 admit no negative cycle, decided by Bellman–Ford, because
a simple cycle has at most |N| edges. Likewise for ≤ −1. ∎

Request and reply {ι+k ≺ ι′+k, ι′+k ≺ ι+k+1} is uniform with weights 0 and 1
and the program-order loops of weight 1. The component {ι, ι′} has only
positive cycles. The constraint of the box is strict, and so is the creation
constraint of b in rr_main, which has the same shape.

### 2.2  Monotone schemas with constants

𝔇₂ᵐ is the subfragment with shifts of δ ≥ 0, fan-downs, fan-ups and ground facts. Let B be the
largest constant that occurs. The abstraction 𝔊^B has vertices (p, v) with
v ∈ {0, …, B} ∪ {⊤}, where ⊤ stands for any offset above B, and an edge for
every edge of 𝔊 whose source value matches, with the target abstracted. A
target above B becomes ⊤, a shift or program order from ⊤ stays at ⊤, a
fan-down from ⊤ goes to its constant, a fan-up into offsets above B goes to ⊤
and into offsets ≤ B goes to every such exact value.

**Theorem 4 (monotone).** [derived] 𝔊 has a cycle iff 𝔊^B has one. Decided in
time polynomial in |N| · (B + 2).

Proof. Abstraction maps cycles to cycles. For the converse take a cycle of
𝔊^B. If it visits an exact vertex, read it from there. Concrete offsets are
exact until the first step into ⊤, then increase weakly, and every guard is at
most B, so every edge applies, until a fan-down or a fan-up into an exact value
resets the offset to a constant. The concrete walk therefore follows the
abstract one and closes at the exact vertex. If the cycle stays in ⊤ vertices,
its edges are shifts and program order among names, and the concrete offset
after one round has grown by the total weight σ ≥ 0. If σ = 0 it closes at any
offset above B. If σ > 0 it does not close, but then the cycle in 𝔊^B is not
realizable, so this case must be excluded. For the ⊤ part the procedure
applies Theorem 3 to the subgraph of shift edges and program order, asking for
a zero-weight closed walk, which under δ ≥ 0 means a cycle of shift edges of
weight 0 that uses no program-order edge. ∎

The two procedures combine. 𝔊 has a cycle iff 𝔊^B restricted to walks that
touch an exact vertex has one, or the zero-weight condition of Theorem 3 holds
on the shift edges.

The tail call {ι+k ≺ ζ} is a fan-down. The box constraint of FreshMany
{ι ≺ δ} ∪ {δ+k ≺ κ} is a ground fact and a fan-down. The constraints of the
two streams of examples/cfst/Stream.v and of the lockstep channels `lsa_C`,
`lsb_C` are shifts of weight 0 and 1 and fan-downs to the ceiling. All are in
𝔇₂ᵐ.

### 2.3  General one-counter schemas

With negative shifts and constants together, 𝔊 is the configuration graph of
a one-counter automaton whose states are N, whose counter is the offset,
whose transitions are the shift edges with lower-bound guards, and whose
fan edges test or set the counter to a constant. A cycle of 𝔊 is a
configuration reachable from itself in one or more steps. [known, uncited,
verify] Reachability in one-counter automata with zero tests and unary
updates is decidable, so acyclicity of 𝔊 is decidable. The guards o ≥ a and
the constant tests are encoded by keeping min(o, B) in the finite control.
This file gives no self-contained proof for this case and no complexity bound
beyond decidability. [guess] The bound is polynomial, by the same bounded
abstraction as Theorem 4 together with a reachability procedure for the ⊤
region, which is reachability in a one-counter net.

Entailment of a ground fact x ≺ y in 𝔇₂ reduces to strictness. With Γ strict,
x ≼ y iff Γ ∪ {y ≺ x} is not strict (algorithmic.md, Lemma 6), and 𝔇₂ is
closed under adding a ground fact. Entailment of a whole schema
∀k. (p, k+a) ≺ (q, k+b), which a force of a box asks, is the question whether
the set of k with a path from (p, k+a) to (q, k+b) is all of ℕ. In 𝔇₂ᵘ and
𝔇₂ᵐ a path for one k above B is a path for every larger k, by the same lifting
as in Theorem 3, so finitely many k decide it. [guess] In general the set of
such k is semilinear and computable, which again rests on one-counter
reachability.

## 3  Fragment 𝔇₃, regular walks

The constraints of recursion through payload points move a counter into the
index of a payload name, which is outside 𝔇₂. The chain
{ι[0]ⁿ+1 ≺ ι[0]ⁿ⁺¹} of the received chain, the relay
{ι+k+1 ≺ (ι+k)[0]+1}, and the ceilings over walks of the segment functions
{κ·w ≺ ζ, κ·w ≺ (κ·w)[i]} are of this kind. 𝔇₃ reads points as words.

Words. Fix a bound on payload indices, say j < m. A walk is a word over the
alphabet Σ = {s, c₀, …, c_{m−1}}, where s is the successor and c_j the payload
point [j]. Every point rooted at r is (r, w) for one walk w, where (r, ε) is (r, 0),
(r, w s) is (r, w)+1 and (r, w c_j) is (r, w)[j]. The encoding is a bijection
between points with roots in a finite set of roots and words r·w.

Schemas of 𝔇₃. Finitely many facts of the following forms, with L a regular
language over Σ, u, u′ fixed walks, r, r′ roots and z a fixed point.

```
suffix     ∀w ∈ L. (r, w u) ≺ (r′, w u′)       prefix shared, suffixes rewritten
ceiling    ∀w ∈ L. (r, w u) ≺ z
floor      ∀w ∈ L. z ≺ (r, w u)
ground     x ≺ y
root alias ∀w ∈ L. (r, w u) ≡ (r′, w u)        the same walk on both sides
```

A shift schema ∀k. (p, k+a) ≺ (q, k+b) is the suffix schema with L = s*,
u = sᵃ, u′ = sᵇ. So 𝔇₂ ⊆ 𝔇₃ as sets of generated theories, except for ground
aliases with potential, which 𝔇₃ handles only through the root aliases below.

Root aliases. ∀w ∈ L. (r, w u) ≡ (r′, w u) with the same walk on both sides
identifies two name patterns and nothing else. Its closure under the
congruences identifies (r, w u v) with (r′, w u v) for every v. The procedure
replaces r′·w u by r·w u everywhere, a prefix rewriting of the encoded words by
a regular pattern, after which no ≡ fact remains. The forwarder's
(ι+k)[1] ≡ (ι′+k)[1] is of this form with L = s*, u = c₁. This is stage 1 of
egg-smt-demo.md, where the e-graph over name patterns performs the same
replacement.

Encoding of the edge relation. Write a point (r, w) as the word r·wᴿ, the root
first and the walk reversed. Program order (r, w) ≺ (r, w sⁿ), n ≥ 1, becomes
r·x → r·sⁿ·x for every x, a prefix rewriting r → r·s⁺ with arbitrary
suffix. A suffix schema becomes r·uᴿ·x → r′·u′ᴿ·x for x ∈ Lᴿ, a prefix
rewriting of r·uᴿ into r′·u′ᴿ with the suffix in a regular language. A
ceiling becomes r·uᴿ·x → z for x ∈ Lᴿ, a floor the reverse. Each of these
edge sets has the form U × V · W with U, V, W regular. Graphs whose edge
relation is a finite union of such sets are the prefix-recognizable graphs of
Caucal [known, uncited, verify].

**Theorem 5 (𝔇₃).** [derived from a known result, uncited] After the root
aliases are resolved, the generated order of a 𝔇₃ constraint is the
reachability relation of a prefix-recognizable graph. Strictness, entailment
of a ground fact and entailment of a schema whose instances form a regular
set are decidable.

Proof. The generated order is reachability in the graph above, read on words,
because no ≡ fact remains. [known, uncited] Prefix-recognizable graphs have a
decidable monadic second-order theory. "Some vertex reaches itself by a
nonempty path" is a monadic second-order sentence, and so is "every pair
(x, y) in a regular set has a path from x to y" when the set is given by an
automaton on the convolution of the two words, which the suffix schemas are. ∎

The cost of the monadic second-order route is nonelementary in general.
[guess] Acyclicity alone is polynomial, by reduction to emptiness of a
pushdown system over the reversed words, where a path is a run of a pushdown
automaton whose stack is the word. A refutation would be a hardness result for
cycle detection in prefix-recognizable graphs.

Theorem 2 carries over. For a creation constraint in 𝔇₃ of shape A, the
relation ≼_R inside the fresh root and the entailments Γ ⊢ u ≺ v are the two
decidable questions of Theorem 5, and Lo and Hi are now regular sets of facts
whose pairs are compared as a regular relation.

What 𝔇₃ cannot say. The ranks of examples/cfst/CfstScheduler.v define the
constraint of each scheduler channel by an arithmetic comparison
rk b k < rk a j of two independent offsets, with rk affine in ⌊k/2⌋. The
generated order coincides with that of a finite set of shift schemas over the
two residues of k, so the scheduler lies in 𝔇₂ after residue splitting
(algorithmic.md, Lemma 4), but the constraint as written is not a 𝔇₃
schema. [guess, not checked in detail] The replacement by shift schemas
generates the same theory for every a. A refutation would be one pair (k, j)
related by rk and not by the shift schemas with the program order.

## 4  Example coverage

Every constraint of theories/examples and theories/examples/cfst, by the
innermost fragment that contains it as written. "Γ finite" means the context
it is checked against is in 𝔇₁.

| file | constraint | fragment |
|---|---|---|
| Sync, Cycle, Scheduler, MilnerSched, FactoryEx, FreshBetween, SyncFresh and the other `*Fresh` files | `fresh_bcs L H`, `alias_bcs x` | 𝔇₁, shape A or B |
| Delegation, OptionPayload | `dl_C`, `op_C` | 𝔇₁, shape A |
| Congruence | `cg_C` (box, one alias), `cgc_C` | 𝔇₁ |
| Ordered, Rejected | `ord_C`, `ord0_C` | 𝔇₁ |
| Factory | `Cfa` | 𝔇₁ |
| cfst/BranchOrder | `boc_C`, `bod_C` | 𝔇₁ |
| cfst/SegmentInterleave, SegmentDeleg | `sid_C`, the alias at κ′[0] | 𝔇₁ |
| cfst/CfstScheduler | `lead_facts` | 𝔇₁ |
| RequestReply | `rq_C`, `rrf_C` | 𝔇₂ᵘ |
| TailCall | `tc_C`, `tcc_C` | 𝔇₂ᵐ, fan-down |
| FreshMany | `fm_C` | 𝔇₂ᵐ |
| cfst/Stream, cfst/CfstTools | `st_C`, `lsa_C`, `lsb_C` | 𝔇₂ᵐ |
| cfst/CfstScheduler | `fl_C`, `wk_C` | 𝔇₂ᵐ after splitting k into its two residues |
| cfst/CfstScheduler | `sch_C a` | 𝔇₂ᵐ after splitting, [guess] of Section 3 |
| ReceivedChain, Stream (core) | `ch_C`, `st_C` | 𝔇₃, L = c₀*, u = s, u′ = c₀ |
| FactServer, KobForwarder | `fc_C`, `fw_C` | 𝔇₃, L = c₀*, u = c₀, u′ = ε and u = c₀ s, u′ = ε |
| Relay | `rel_C`, `relc_C`, `reld_C` | 𝔇₃ (relay schemas), 𝔇₁ (`reld_C`) |
| Forwarder | `fp_C` | 𝔇₃, L = s*, u = ε, u′ = c₀ |
| Forwarder | `fw_C`, `fwb_C` | 𝔇₃ with one root alias |
| ChoiceEnc | `lp_C` | 𝔇₃, L a chain of payload points, u = s |
| SendTreeType, cfst/TreeCopy, TreeSum, ArithServer | `send_C`, `after_C`, `copy_C`, `cafter_C`, `tca_C`, `tcb_C` | 𝔇₃, L = Σ*, ceilings and u = ε, u′ = c_i |

The translations. theories/pgv, theories/pn and theories/mp type at worlds
`Wpgv`, `Crel` and `Wmp` whose facts come from ranks of priorities, levels or
denotations. Each is given with its own strictness proof, a rank into ℕ or ℤ,
which is the certificate route of Section 5 and not a fragment of this file. A
closed PGV program has finitely many priorities, so its world restricted to
the points the program mentions is in 𝔇₁. [guess] The same holds for a closed
Padovani and Novara program with its levels. Not checked.

The rejections of Rejected.v are entailment failures or strictness failures in
𝔇₁ and 𝔇₂ᵘ, and egg-smt-demo.md reproduces each.

## 5  Outside the fragments

### 5.1  Two counters in one word

The undecidability of algorithmic.md, Theorem 5, reads as follows in the
words of Section 3. Its schemas relate ⟨q; t, x, y⟩ = a sᵗ c_q sˣ c₁ sʸ c₁ to
⟨q′; t+1, x+1, y⟩. The two sides share the suffix sʸ c₁ and the prefix a, and
differ in the middle, where two counters move independently. A schema whose
two sides share a prefix and rewrite the suffix is in 𝔇₃. A schema whose two
sides share a suffix and rewrite a middle block with a counter is not, and
with three counters in one word strictness is undecidable, by the reduction
from two-counter machines there. [known, from algorithmic.md] The natural
extension of 𝔇₃ to schemas that rewrite in the middle of a word, that is
∀w ∈ L, v ∈ L′. (r, w u v) ≺ (r′, w u′ v), is therefore undecidable. Two
counters per word, the relay's shape with one more level, is open
(algorithmic.md, §10.1).

### 5.2  Two independent counters

A fact with two counters that are not tied, such as ∀k, j. (p, k) ≺ (q, j)
whenever an arithmetic relation of k and j holds, is a Presburger-definable
set of ground facts. When the relation is a difference bound j ≥ k + d the
set generates the same theory as a shift schema. For general Presburger
relations the generated order is reachability in a graph on ℕ² with
semilinear edge sets, and [guess] strictness is undecidable there as well, by
the same two-counter encoding with the clock in one coordinate. Not shown.

### 5.3  Where a certificate takes over

Outside 𝔇₁ to 𝔇₃, and inside them when the decision procedure is too slow,
the development's own route is a ranking certificate, a map from points into
ℕ, ℤ or a lexicographic product that every fact and every program-order step
raises. `cc_ok_inner`, `wgen_strict`, `wgen_strict_lex` and `wgen_strict_z` of
examples/ExampleTools.v are the checkers, and algorithmic-smt.md and
egg-smt-demo.md show that z3 and cvc5 find such ranks for every constraint of
the development, with a lexicographic level for the ceilings and a piecewise
rank for the ground delegation round trip. A certificate is checked in Rocq by
`lia`. The certificate route is sound and incomplete, the fragments are
complete for their questions. The boundary between the two is the decision
procedure's domain. A constraint in 𝔇₁ needs no certificate, a constraint in
𝔇₃ needs one only when the prefix-recognizable check is not implemented, and a
constraint with two independent counters needs one always.
