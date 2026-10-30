# Deciding strictness of W_G

State of 2026-10-30, revised the same day after DECIDABILITY-REVIEW.md and sharp
edges 58. Paper-level. Nothing here is mechanized. Notation follows ORDERS-SPEC.md
§4, §5 and §9.

## 0  Results

Static.v types a box body once, with its point variables and its constraint C as
hypotheses, at one world W that knows constants only (sharp edges 57 and 58). The
type checker then decides strictness of W_G for a finite set G of ground facts and
ground aliases. It also decides entailments W_G ∪ Ψ ⊢ x ≺ y at the side conditions
that mention point variables, among them the body atoms of a box under its C and
C[xs] at force sites inside box bodies (§9). Lemma 5 reduces an entailment to at
most (2|Ψ| + 2)² ground queries and a search in a graph on 2|Ψ| + 2 vertices.
Lemma 6 reduces a ground query to strictness of G plus one fact. Lemma 7 bounds the
choice of G to relations on the finitely many ground points the open conditions
mention. Everything therefore rests on strictness for ground G. Ground G lies in L
without counter variables. It satisfies (D), (C) and (A) outright, and (R) and (S)
when its aliases relate shapes of equal depth. Theorem 4 decides it under (M).
Delegation emits aliases of unequal depth, and a delegation round trip violates (M)
(§9.3). Strictness for those ground G is open.

Theorems 1 to 4 are results about the schema class L of §1, which models the orbit
reading of §1.3. Static.v no longer uses that reading. Strictness of W_G is
decidable for every finite G in L that satisfies five syntactic side conditions
(diagonal freedom, role consistency, offset alignment, equal coefficients,
monotone boundary roles) and a sixth, finite shape closure, that holds for every
example but is not shown decidable here. When no role carries a constant the
procedure is polynomial in the size of the static graph 𝒢 of §2. Otherwise it is
polynomial in the size of an abstract graph that grows exponentially in the number
of constant-carrying roles per shape (Theorems 2 to 4). Theorem 3 needs
constant-free G. Every slot point carries the constant offset 0, so the sender gate
(c, κ) ≺ (c[κ][1], 0) of the free-coordinate extension of ORDERS-SPEC §16 needs
Theorem 4 and (M). Theorem 3 alone covers only the receiver schema
(c[κ][1], b) ≺ (c, κ+1).

Offset alignment (A) answers gap G2 of the review. It rejects an alias that carries
a counter at the offset on one side and at an index coordinate on the other, such
as the delegation alias (e, κ) ≡ (c[κ][1], 0) under recursion. Under the reading of
Static.v there are no counters, and (A) rejects nothing.

Two claims of ORDERS-SPEC do not hold as stated.

- "Boundary facts reduce by unrolling" is false once a family has three counting
  coordinates. Strictness for unit schemas with constants is undecidable, already
  without aliases and with nesting depth 3 (Theorem 5, a reduction from
  two-counter machines).
- Slot names do not nest boundedly in programs. A recursion on a received channel
  needs the points c, c[0][1], c[0][1][0][1], … (§1.4). Any finite G has bounded
  depth, so the static system under the orbit reading rejects such a program.
  Static.v rejects it as well (§9.4). This is a completeness gap, not a
  decidability gap.

Stepped boxes of sharp edges 61 (§10) add one obligation per outside force, C at
every word of the steps. Lemma 8 turns it into strictness of G plus one ≺ schema
family per fact of C. These families contain no alias schemas (Lemma 9), so (A)
holds and G2 cannot arise. Pure shifts with diagonal or axis generators reduce to
Theorems 2 to 4. Mixed generators need Lemma 2 for interval shifts, planned and not
proved. One step that moves into slots with slot-free dependency cycles reduces to L
with one counter per side. The relay lands there and violates (M), so it is the open
case of §7.1. Several non-commuting steps have a decidable depth test. Unbounded
depth, sum coordinates and scalings are open.

Proved here are Theorems 1 to 5 and Lemmas 1 to 9. Cited are the linear-programming
characterization of zero multicycles and the recursive SCC scheme of Kosaraju and
Sullivan (STOC 1988, pp. 399–401), polynomial-time linear programming, and the
undecidability of halting for two-counter machines (Minsky 1961). We re-prove the
parts of Kosaraju–Sullivan we change.

## 1  The schema class

ORDERS-SPEC defines G only as "a finite set of fact schemas and alias schemas over
points", closed under the substitutions at recursive calls. This section fixes a
reading of that sentence. Every result below is relative to it.

### 1.1  Families

A shape is a point constant together with a finite sequence of slot indices,
f = a.i₁…iₙ. The depth of f is n. A ground point of shape f is

```
(a[b₁][i₁]…[bₙ][iₙ], b_{n+1})        with coordinates  (b₁, …, b_{n+1}) ∈ ℕ^{n+1}
```

so the vertices of shape f form a copy of ℕ^{d_f} with d_f = n+1. The last
coordinate is the offset. Program order moves only the offset. A slot moves the
offset into a new index coordinate and starts a new offset at 0.

```
(p, b) + 1  = (p, b+1)
(p, b)[i]   = (p[b][i], 0)
```

A fresh point that `new` creates inside the body of a recursive box is not one
constant. Each unfolding creates a different channel. We read it as a family ν
whose index coordinates are the unfolding counters of the enclosing boxes, so it is
again a shape with d_ν ≥ 1. The fresh points μ and ℓ of E-Abs and E-Exp are
treated the same way.

### 1.2  Unit schemas

A point term over counter variables κ₁, …, κ_m is a shape f together with one
coordinate expression per coordinate, each either a constant c ∈ ℕ or κ_j + c.
A schema is an atom between two point terms, together with the domain κ̄ ∈ ℕ^m.

```
σ  ::=  s ≺ s′  |  s ≡ s′            s, s′ point terms over κ̄,  κ̄ ∈ ℕ^m
```

A variable is shared when it occurs on both sides and free when it occurs on one
side only. The class L consists of finite sets of such schemas. Its instances are
the ground atoms obtained by κ̄ ∈ ℕ^m.

Diagonal freedom (D). No variable occurs twice on the same side.

(D) holds for every G the static system emits under the reading of §1.3. A
point term arises from one bound point variable by slots and an offset, and the
substitution at a recursive call adds the box's counter to the offset of that
variable only. Distinct boxes contribute distinct counters. So a counter lands in
exactly one coordinate of a point term.

Shifts. If κ is shared and stands at coordinate position j on the source as
κ + c and at position j′ on the target as κ + c′, the schema carries the value at
j to the value at j′ shifted by δ = c′ − c, and it exists only where the source
value is at least c.

### 1.3  Where the schemas come from

The static rules of ORDERS-SPEC §9 emit the following atoms over point terms.

```
send     ι ≺ ι[i]                 for each payload point                     {ι} ≺ heads(P[ι])
E-App    u ≺ x                    x ∈ F                                      {u} ≺ F
E-Abs    u ≺ μ,   ℓ ≼ x           x ∈ heads(Θ, Δ)
link     ι ≡ ι′
E-Ch     ι′ ≡ ι
payload  x ≡ ι[i]                 the sender's channel aliased to the slot (delegation)
```

At top level all coordinates are constants. Inside the body of a recursive box
□(∀ιs. T) the atoms mention the bound point variables ιs. The orbit reading takes
"G closed under the substitutions at recursive calls" to mean that G contains the facts of every instance
in the orbit of the first instance under the recursive substitutions. We call a
box shift-only when its recursive calls instantiate each bound point variable ι_j
by ι_j + s_j. With a single recursive call site and all s_j ∈ {0, s}, the orbit is
ι_j + s·κ for one counter κ ∈ ℕ, and each body atom becomes one unit schema after
residue splitting (Lemma 4 in §5.3). The request/reply example is of this form.

```
(a, κ) ≺ (b, κ)        (b, κ) ≺ (a, κ+1)                       one box, s = 1
```

A body of an inner box that the outer body calls at a point of the outer orbit
adds its own counter. This gives the free-coordinate schemas.

```
(c, κ) ≺ (c[κ][1], 0)          sender gate, delegation under recursion
(c[κ][1], b) ≺ (c, κ+1)        receiver loops on the received channel, b free
```

Orbits that do not fit L are listed in §7.

Static.v does not use the orbit reading. It reads the atoms of a box body as
entailment obligations under the hypotheses C of the box and emits only ground atoms
into G (§9). The orbit reading and the class L remain the setting of Theorems 1 to 5.

### 1.4  Nesting

Programs nest slots without bound. Let S = μX.?(∃ι. X@ι).Close and take the
recursive receiver below.

```
f : □(∀ι. S@ι ⊸^ι ∗)
f = !(f = λc. let (d, c′) = recv c in close c′; f d)
```

At the instance ι the body holds d at ι[1] while it closes c′ at ι+1, so it emits
ι+1 ≺ ι[1]. The recursive call instantiates ι by ι[1]. The orbit of (c, 0) is
(c, 0), (c[0][1], 0), (c[0][1][0][1], 0), …, and the closure contains
(π, 1) ≺ (π[0][1], 0) for every π on that chain. No finite set of unit schemas
over finitely many shapes contains these facts, so with "G finite" the static
system cannot type f. Its partner can be well typed and the composite is deadlock
free, so this is a loss of completeness.

Within a finite G in L the shapes are finitely many by definition. The slot
congruence can still generate deeper derived aliases (§2). We close the shapes as
follows.

Sh(G) is the least set of shapes that contains every shape of G, is closed under
prefixes, and is closed under alias transfer. If some alias schema relates a point
term of shape g to one of shape h, then g.w ∈ Sh(G) iff h.w ∈ Sh(G), for every
sequence of slot indices w.

Finite shapes (S). Sh(G) is finite.

(S) fails for self-delegation, where the alias (d, κ) ≡ (d[κ][1], 0) puts d, d.1,
d.1.1, … into one transfer class. Section 7 lists (S) as unproved to be decidable
in general. For every example in ORDERS-SPEC §13, Sh(G) is the set of prefixes of
the shapes of G.

## 2  Strictness as a cycle problem

Γ_G is the following infinite graph. Its vertices are the ground points of shapes
in Sh(G). It has a strict edge x → y for each instance x ≺ y of a ≺ schema and for
program order x → x+1. It has weak edges x → y and y → x for each instance
x ≡ y of an alias schema in the alias closure A(G) below.

A(G) contains, for every alias schema s ≡ s′ of G and every slot sequence
w = i₁…i_k with shape(s).w ∈ Sh(G), the schema

```
(s + ν₀)[i₁] + ν₁ … [i_k] + ν_k   ≡   (s′ + ν₀)[i₁] + ν₁ … [i_k] + ν_k
```

with fresh shared variables ν₀, …, ν_k. The case k = 0 is the successor closure
s + ν₀ ≡ s′ + ν₀.

Let E be the equivalence generated by the instances of A(G). It relates points of
shapes in Sh(G). Write u[w] + n for (u[i₁] + n₁ … [i_k]) + n with w = n₁ i₁ … i_k
nonempty. The outside equivalence O is the equivalence on points of shapes outside
Sh(G) generated by the pairs u[w] + n ≡ v[w] + n with u E v and u[w] outside Sh(G).
Then v[w] lies outside Sh(G) as well, by alias transfer along the chain from u to v.
O relates points with equal offsets.

**Lemma 1 (alias closure).** ≡_{W_G} is E ∪ O. In particular ≡_{W_G} restricted to
points of shapes in Sh(G) is E.

*Proof.* The instances of A(G) and the generators of O are aliases of W_G by
successor and slot congruence. This gives E ∪ O ⊆ ≡_{W_G}. For the other inclusion
it suffices that E ∪ O is a congruence that contains the base aliases, because
≡_{W_G} is the least such relation on all points. E and O live on disjoint sets of
points, so E ∪ O is an equivalence. E contains the base aliases (k = 0, ν₀ = 0).

Successor. E is closed under +1, because the set of instances of A(G) is (shift
ν_k). The generators of O are closed under +1 (raise n), so O is.

Slots on E. Let x E y by a chain x = z₀, …, z_m = y. Each z_j is related to x by a
chain of alias schemas. If x[i] has a shape in Sh(G), then each z_j[i] has a shape
in Sh(G) by alias transfer, and the instance of A(G) with word w.i and ν_{k+1} = 0
relates z_j[i] to z_{j+1}[i]. So x[i] E y[i]. If x[i] lies outside Sh(G), then
x[i] O y[i] by the generator with u = x, v = y, w = 0 i and n = 0.

Slots on O. Sh(G) is prefix closed, so every slot of an outside point lies outside.
The image of a generator u[w] + n ≡ v[w] + n under [i] is the generator for the word
w n i with offset 0. So [i] maps chains of generators to chains of generators, and
O is closed under slots. ∎

**Theorem 1 (reduction).** W_G is strict iff Γ_G has no closed walk that contains a
strict edge.

*Proof.* The order of W_G is the transitive closure of the strict edges composed
with ≡ on both sides, read on ≡-classes. It is irreflexive iff no point x has
x ≺⁺ x modulo ≡, that is, iff there is no closed walk of strict edges and
≡-steps with at least one strict edge. By Lemma 1 a ≡-step between points of
Sh(G) is an E-step, that is, a path of weak edges, and a ≡-step at a point outside
Sh(G) is an O-step and stays outside. It remains to show that points outside Sh(G)
lie on no such walk. No ≡-step relates a point of Sh(G) to an outside point. No
strict edge leaves or enters the outside part except program order, which keeps the
shape, because every ≺ schema mentions shapes of G only. Inside the outside part, O
preserves the offset and program order raises it, so it carries no closed walk with
a strict edge. ∎

Theorem 1 does not use (S). (S) makes the static graph below finite.

The static graph 𝒢 is the finite multigraph whose vertices are the shapes of
Sh(G). Each ≺ schema and the program-order schema of each shape give a strict
edge, and each schema of A(G) gives two weak edges, one per direction. Every
closed walk of Γ_G projects to a closed walk of 𝒢.

## 3  Roles

Roles need every edge of 𝒢 to be a unit schema. A schema of A(G) adds ν₀ to the
offsets of s and s′. If a shared variable κ sits at the offset of s and at an index
coordinate of s′, the offset of s + ν₀ is κ + c + ν₀, a sum of two variables. The
alias (e, κ) ≡ (c[κ][1], 0) gives (e, κ + ν₀) ≡ (c[κ][1], ν₀), whose instances
relate (e, m) to (c[k][1], m − k) for all k ≤ m. No finite set of unit schemas has
these instances (DECIDABILITY-REVIEW.md, G2). We exclude this case.

Offset alignment (A). In every alias schema of G, the two offsets hold either
constants or one shared variable κ, as κ + c on one side and κ + c′ on the other.

(A) costs one scan over the alias schemas. It fails in two ways. A shared variable
sits at the offset on one side and at an index coordinate on the other, the case
above. Or an offset holds a free variable κ. Then the instances with κ = 0 and κ = 1
are aliased to the same point, so (f, …, c) ≡ (f, …, c+1), and program order makes
W_G non-strict. The second failure therefore decides the instance at once, and only
the first one rejects G. Under the orbit reading the first failure is delegation
under recursion with a payload alias that carries the counter. Under the reading of
Static.v there are no counters (§9), and (A) rejects nothing.

Under (D) and (A) every schema of A(G) is a unit schema. ν₀ lands in the
coordinates that were the offsets of s and s′, and ν_k for k ≥ 1 in fresh offsets.
If those coordinates hold κ + c and κ + c′, κ occurs nowhere else by (D), and κ + ν₀
renames to one variable κ′ ∈ ℕ with the same instances. Otherwise they hold
constants, and c + ν₀, c′ + ν₀ are unit expressions with ν₀ shared. (D) carries over
to A(G).

Union the coordinate positions (f, j) over all edges of 𝒢 whenever one shared
variable sits at (f, j) on one side and at (g, j′) on the other. The classes are
roles.

Role consistency (R). No role contains two positions of the same shape.

Under (R) every vertex (f, x) has at most one r-coordinate x_r for each role r,
and R(f) denotes the roles present at f. For an edge e and a role r, e shares r
when a shared variable carries r from source to target, with shift δ_e[r] ∈ ℤ, and
when r is absent at both ends, with shift 0. Otherwise e cuts r. An edge cuts r when
r is present on one side only, when it holds a free variable on one side, or when it
holds a constant on one side.

(R) and (D) are checked by one union-find pass over G. Program order shares every
role of its shape, with shift 1 on the offset role and 0 elsewhere. Under (A) the
schemas of A(G) share the roles of s and s′ and the fresh roles ν_k.

**Lemma 2 (threads).** Assume (D), (R) and (A) and that no schema of G contains a
constant. Then Γ_G has a closed walk with a strict edge iff 𝒢 has a closed walk
e₁ … e_n with a strict edge such that every role r is cut by some e_k or satisfies
Σ_k δ_{e_k}[r] = 0.

*Proof.* (⇒) Project the concrete walk to 𝒢. If no edge cuts r, every edge
carries the r-coordinate and adds its shift, and the walk returns to its start, so
the shifts sum to 0.

(⇐) Let C bound every constant of G and Δ bound every |δ|, and put
N = C + nΔ + 1. Assign concrete r-coordinates along the walk role by role. If no
edge cuts r, start at N and add the shifts. The values stay in [N − nΔ, N + nΔ],
above every guard, and return to N. If some edge cuts r, give r the value N at
the target of every cutting edge that has r there, and carry it forward by the
shifts until the next cutting edge, cyclically. Values again stay above every
guard. Every edge instance is now determined. A shared variable takes the source
value minus its constant, which is ≥ 0. A free variable takes whatever its side
needs. (D) makes these choices independent and (R) makes "the r-coordinate" of
each vertex well defined. The walk closes because each role returns to its
starting value. ∎

Lemma 2 is where coordinates become independent threads. Its proof uses the
absence of constants twice, once for "start anywhere" and once for "shift up".
Section 5 removes constants on monotone roles. Section 6 shows that general
constants make the problem undecidable.

## 4  Uniform and free-coordinate edges

A walk of 𝒢 is valid when it satisfies the condition of Lemma 2. For a subgraph
H of 𝒢, cut(H) is the set of roles cut by some edge of H. For a role set S, LP_S(H, e)
is the linear program over x ∈ ℚ^{E(H)}

```
Σ_{e′ ∈ in(v)} x_{e′} = Σ_{e′ ∈ out(v)} x_{e′}     for each vertex v of H
x ≥ 0
Σ_{e′} x_{e′} δ_{e′}[r] = 0                          for each role r ∉ S
x_e ≥ 1
```

This is Kosaraju and Sullivan's multicycle LP (their Thm 2.4, p. 399, in the
per-edge form x_e ≥ 1 of their §3, p. 400) with the labels restricted to the roles outside S. A feasible x scales to an integral
circulation whose support contains e.

**Algorithm SFZ(H)** (strict zero cycles with free coordinates).

```
1  S := cut(H)
2  loop
3     H := H without the edges that cut a role outside S
4     E′ := { e ∈ H | LP_S(H, e) feasible }
5     if E′ has no strict edge: return No
6     if S ⊄ cut(E′): S := S ∩ cut(E′); continue
7     let Q₁, …, Q_k be the strongly connected components of (V(H), E′)
8     if k = 1: return Yes
9     return SFZ(H|Q₁) ∨ … ∨ SFZ(H|Q_k)
```

Singleton vertices without E′ edges count as components. H|Q keeps the edges of
H with both ends in Q.

**Theorem 3 (free coordinates).** Under (D), (R), (A) and (S), for constant-free
G, SFZ(𝒢) returns Yes iff Γ_G has a closed walk with a strict edge, and it runs in
polynomial time.

*Proof.* By Lemma 2 it suffices to show that SFZ(H) returns Yes iff H contains a
valid closed walk.

Invariant. Every valid walk W contained in the input H stays inside H at line 3
and inside E′ at line 4. Let S(W) be the roles W cuts. Initially S(W) ⊆ cut(H) = S.
If S(W) ⊆ S, line 3 removes no edge of W. W is a circulation with zero sum on each
role outside S(W), hence on each role outside S, so its edge counts are feasible
for LP_S(H, e) for each e on W, and W ⊆ E′. Then S(W) ⊆ cut(E′), and line 6
keeps S(W) ⊆ S.

No at line 5. A valid W has a strict edge and lies in E′.

Recursion at line 9. A valid W is a closed walk inside E′, so its vertices lie in
one component Q, and W ⊆ H|Q.

Yes at line 8. Every vertex of H lies in the one component, so E′ spans V(H) and
is strongly connected. For each e ∈ E′ take an integral solution x^e of
LP_S(H, e). Its support lies in E′, because x^e also witnesses feasibility for
every edge of its support. The sum x = Σ_e x^e is a circulation with support
exactly E′ and zero sum on every role outside S. Its multigraph is balanced and
connected, so it has an Euler circuit W (Kosaraju–Sullivan, proof of Thm 2.2,
p. 399). W uses every edge of E′. So W contains a strict edge (line 5 passed) and
cuts every role in S (line 6 passed). Every role outside S is shared by all edges
of H (line 3) and has zero sum on W. So W is valid.

Termination and cost. Line 6 shrinks S, so the loop runs at most |roles| + 1
times per call. Line 9 recurses only when k ≥ 2, on smaller vertex sets. As in
Kosaraju–Sullivan (Thm 3.3 and its proof, p. 401), the calls at one recursion depth work on
disjoint subgraphs, and the depth is at most |V(𝒢)|. The total is
O(|V| · (|roles| + 1) · |E|) feasibility tests of linear programs with |E|
variables and |V| + |E| + |roles| constraints, each polynomial. ∎

**Theorem 2 (uniform schemas).** Assume (D), (R), (A) and (S). If every edge
shares every role of both its ends (no free variables, no constants, equal role
sets), then S = ∅ throughout,
SFZ is Kosaraju and Sullivan's ZCYCLE with the extra requirement of a strict edge,
and strictness of W_G is decided in O(|V| · |E|) LP tests.

The strict-edge requirement is the only change to ZCYCLE. ZCYCLE asks for a zero
cycle, and strictness asks for a zero cycle through a strict edge. Weak edges
alone form zero cycles (an alias and its reverse), and those cycles are harmless.
The domain ℕ instead of ℤ costs nothing (the shift-up step in Lemma 2). S = ∅
relies on the convention of §3 that an edge shares, with shift 0, every role absent
at both its ends. Without it, weak components of 𝒢 with different role sets put
those roles into cut(𝒢). The answer is the same, because those roles have no shift
on those edges and their LP constraint is trivial (DECIDABILITY-REVIEW.md, G3).

## 5  Constants

### 5.1  Monotone roles

A role carries a constant when some schema of A(G) holds a constant at a position
of that role. Slot points always carry one (the offset 0 of ι[i]), and top-level
facts carry only constants.

The shift graph of a role r has the shapes in which r is present as vertices and
an edge f → g of weight δ_e[r] for every edge e of 𝒢 that shares r. Program order
contributes a self-loop of weight 1 on the offset role. An alias contributes
weights δ and −δ.

Monotone boundaries (M). The shift graph of every role that carries a constant
has no negative cycle.

(M) is checked by Bellman–Ford. If it holds, take shortest-path potentials π_r
with δ_e[r] + π_r(src e) − π_r(tgt e) ≥ 0 and replace each r-coordinate x_r at
shape f by x_r − π_r(f). Shifts become nonnegative, and constants and guards move
by bounded amounts. Below, assume every shift on a constant-carrying role is ≥ 0.
Let L and B be the least and greatest constant or guard on such roles after the
change.

### 5.2  Folding monotone roles into the control

Let R_c be the roles that carry a constant and A = {L, …, B, ∞}. The abstract graph
𝒢^# has vertices (f, a) with a assigning a value of A to each role of R_c present
at f. It has an edge (f, a) → (g, a′) for an edge e of 𝒢 when for each r ∈ R_c

```
e shares r              a′_r = a_r ⊕ δ_e[r]   and a_r ≥ the guard     (⊕ saturates above B to ∞)
constant c at source    a_r = c
constant c at target    a′_r = c
free at source          a_r ≥ the guard
free at target          a′_r ≥ the guard, any value of A
```

The edge keeps e's strictness and e's shifts on roles outside R_c. For r ∈ R_c it
shares r with shift δ_e[r] when e shares r and a_r = a′_r = ∞. In every other case
it cuts r. 𝒢^# is constant-free.

**Lemma 3 (abstraction).** Under (D), (R), (A) and (M), Γ_G has a closed walk with a
strict edge iff 𝒢^# has a valid closed walk.

*Proof.* (⇒) Map each concrete vertex (f, x) to (f, a) with a_r = x_r when
x_r ≤ B and ∞ otherwise. Saturating addition abstracts a nonnegative shift
exactly, so each concrete edge maps to an edge of 𝒢^#. For a role outside R_c the
condition of Lemma 2 holds as before. A role r ∈ R_c not cut in 𝒢^# is shared at ∞
by every edge, so the concrete values exceed B everywhere and the shifts sum to 0.

(⇐) Roles outside R_c are assigned as in Lemma 2. Take r ∈ R_c. If 𝒢^# does not
cut r on the walk, every edge shares r at ∞ and the shifts sum to 0, so start at
max(N, B+1) and carry. Otherwise split the walk cyclically at the edges of 𝒢 that
cut r. A segment starts at a constant (exact value) or a free variable (choose the
abstract value, or a large value for ∞). Inside a segment the finite abstract
values are exact, and once the abstract value reaches ∞ the concrete value is above
B and stays consistent with all later guards and tests, which all lie at or below
B. If no edge of 𝒢 cuts r but 𝒢^# does, then some abstract value on the walk is
finite. Values are nondecreasing around the walk and return to their start, so
they are all equal and all shifts on r are 0. The concrete value is that constant.
In each case the concrete walk closes. ∎

**Theorem 4 (boundaries on monotone roles).** Under (D), (R), (A), (S) and (M),
strictness of W_G is decidable. Run SFZ on 𝒢^#. The size of 𝒢^# is at most
|Sh(G)| · (B − L + 2)^ρ, with ρ the largest number of constant-carrying roles at
one shape.

*Proof.* Theorem 1, Lemma 3 and Theorem 3. ∎

All examples of ORDERS-SPEC §13 satisfy (M). In request/reply the shifts are 0
and 1. In delegation the slot-offset role of c.1 carries the constants 0 and j,
and its shifts are program order (+1) and the payload alias (0). In the scheduler
and bad link every constant sits on a cut, and the shared shifts come from program
order and aliases with equal offsets.

### 5.3  Coefficients other than 1

Orbits with step s > 1 give coordinate expressions s·κ + c. Extend point terms
by such coefficients.

Equal coefficients (C). In every schema, a shared variable has the same
coefficient at its two occurrences.

**Lemma 4 (residue splitting).** Assume (C). For each role r let m_r be the least
common multiple of the coefficients at positions of r. Write each r-coordinate as
x = m_r·q + ρ with 0 ≤ ρ < m_r and move ρ into the shape. Then G becomes an
equivalent set of unit schemas over the split shapes, and (D), (R) and (M) carry
over.

*Proof.* A variable κ with coefficient s occurs at positions of one role r, and
s | m_r. Substitute κ = (m_r/s)·κ′ + t for each t with 0 ≤ t < m_r/s. An
occurrence s·κ + c becomes m_r·κ′ + (s·t + c), with quotient κ′ + ⌊(s·t + c)/m_r⌋
and remainder (s·t + c) mod m_r. Each t gives one unit schema in κ′ ∈ ℕ, and the
union over t has the same instances as the original. A constant c becomes the
quotient ⌊c/m_r⌋ with remainder c mod m_r. Program order κ + 1 is the case s = 1.
The substitution keeps every variable at its positions, so (D) and (R) hold. A
closed walk of the split shift graph returns to its residues and projects to a
closed walk of the original whose total shift is m_r times the split total, so
negative cycles correspond and (M) holds. ∎

The split multiplies the number of shapes by at most Π_r m_r. Schemas that violate
(C), such as (a, 2κ) ≺ (b, κ), are scalings and not shifts (§7).

## 6  Undecidability with general boundaries

**Theorem 5.** Strictness of W_G is undecidable for finite sets of unit schemas
that satisfy (D), (R), (A) and (S), use no alias schemas, and use shapes of depth
at most 3. The roles that carry constants then violate (M).

*Proof.* Reduce halting of a deterministic two-counter machine M from (q₀, 0, 0)
(Minsky 1961). Encode a configuration (q, x, y) at clock t as the point

```
⟨q; t, x, y⟩  ≔  (a[t][q][x][1][y][1], 0)
```

with states as slot indices. The machine edges advance the clock.

```
inc x, q → q′          ⟨q; κt, κx, κy⟩      ≺  ⟨q′; κt+1, κx+1, κy⟩
x = 0, q → q′          ⟨q; κt, 0, κy⟩       ≺  ⟨q′; κt+1, 0, κy⟩
x > 0, dec x, q → q″   ⟨q; κt, κx+1, κy⟩    ≺  ⟨q″; κt+1, κx, κy⟩
```

and likewise for y. At the halting state h a cleanup phase empties x, then y,
then t, without advancing the clock, and closes the loop at the start.

```
⟨h; κt, κx, κy⟩       ≺  ⟨h_x; κt, κx, κy⟩
⟨h_x; κt, κx+1, κy⟩   ≺  ⟨h_x; κt, κx, κy⟩       ⟨h_x; κt, 0, κy⟩  ≺  ⟨h_y; κt, 0, κy⟩
⟨h_y; κt, 0, κy+1⟩    ≺  ⟨h_y; κt, 0, κy⟩        ⟨h_y; κt, 0, 0⟩   ≺  ⟨h_t; κt, 0, 0⟩
⟨h_t; κt+1, 0, 0⟩     ≺  ⟨h_t; κt, 0, 0⟩
⟨h_t; 0, 0, 0⟩        ≺  ⟨q₀; 0, 0, 0⟩
```

Every schema has offset 0 on both sides. Program order leaves offset 0 for vertices
that no schema touches, and from there only program order continues, so program
order lies on no cycle. Prefix shapes carry only program order. There are no
aliases.

A cycle avoiding the last edge stays in the machine phase, where t strictly
increases, or in the cleanup phase, where x + y + t strictly decreases or the
phase index increases. So every cycle passes ⟨q₀; 0, 0, 0⟩. From there the machine
edges follow the run of M deterministically, because the zero branch requires
x = 0 and the decrement branch x ≥ 1. The cleanup succeeds from every halting
configuration. Hence W_G is non-strict iff M halts. ∎

The static system emits each ingredient of the construction on its own. These
are shared counters with shifts ±1 between slot families (lockstep loops over two
received channels), constants at slot offsets and at top level, and slot indices
as distinct families. Whether one well-typed program emits the whole
gadget is open (§7).

## 7  What does not go through

1. ORDERS-SPEC §16, "boundary facts reduce by unrolling". False in general
   (Theorem 5). True for monotone roles in any dimension (Theorem 4). The case of
   non-monotone boundary roles with fewer than three counting coordinates per
   family is open. The criterion (M) is syntactic and cheap. The static system
   violates it under reading A (§8.2) and under reading C (§9.3). Under reading C
   the violating G is ground, and Theorem 5 says nothing about ground G.
2. Slot nesting is unbounded in programs (§1.4). The static system types only
   programs whose orbit closure fits a finite G. Static.v rejects the recursive
   receiver as well (§9.4). A schema language with variables
   ranging over names would cover the recursive receiver. Its graphs are
   prefix-rewriting graphs with counters, and nothing here decides them.
3. (S), finiteness of the shape closure, is defined but its decidability in
   general is not proved here. It holds when every alias schema relates two shapes
   of equal depth, because transfer then preserves depth and the slot indices come
   from G. Delegation emits aliases of unequal depth, also in ground G (§9.3).
4. Orbits outside L. A box whose bound points move at different rates (a sent
   twice per unfolding, b once) gives schemas such as (a, 2κ) ≺ (b, κ), a scaling
   and not a shift. Lemma 4 does not apply. A consistent choice of rates per
   position would rescale them, but we have not written that case out. A cycle with
   rate product ≠ 1 gives affine maps with nontrivial multipliers, and their fixed points can close cycles. Several
   recursive call sites with different shift vectors give coordinates that are sums
   of counters. Both cases are open.
5. Violations of (R). A schema such as (a[κ₁][1], κ₂) ≺ (a[κ₂][1], κ₁) permutes
   coordinates. Without free variables and constants, lifting shapes to (shape,
   permutation) pairs reduces it to Theorem 2, at a factor d!. With free variables
   the lifting interacts with cuts, and that case is open.
6. The reading of §1. ORDERS-SPEC does not define schemas, orbits or fresh points
   inside boxes. Sections 1.1 to 1.3 fix one reading. A different reading of
   "closed under the substitutions at recursive calls" changes the class. Static.v
   follows reading C of §9, and the orbit reading is no longer the target.
7. Offset alignment (A). We did not extend Lemma 2 to edges that relate an offset
   on one side to the sum of an index and an offset on the other. Such an edge
   relates (e, m) to (c[k][1], m − k) for all k ≤ m, a two-variable constraint
   that roles cannot express. (A) rejects these G under the orbit reading. Under
   reading C it rejects nothing.
8. Reading C (§9). Open are strictness for ground G with aliases of unequal depth
   or with roles that violate (M), a polynomial bound for the choice of G in
   Lemma 7, and whether ground G can encode a two-counter machine.

## References

- S. Rao Kosaraju, Gregory F. Sullivan. Detecting cycles in dynamic graphs in
  polynomial time. STOC 1988, pp. 398–406. Store key `kosaraju1988detecting`.
  Used: Thm 2.2 and 2.4 (p. 399), VPARTITION and ZCYCLE (pp. 400–401), Thm 3.3 and its proof (p. 401).
- Marvin L. Minsky. Recursive unsolvability of Post's problem of "Tag" and other
  topics in theory of Turing machines. Annals of Mathematics 74(3), 1961. Store key
  `minsky1961recursive`. Cited for undecidable halting of two-counter machines,
  not re-read here.

## 8  Can the static system violate (M)?

This section predates sharp edges 57 and 58. Neither of its readings is what
Static.v does now. Static.v follows reading C of §9, under which G is ground and the
question of this section becomes the question of §9.3. The relay discussion stays
because it shows what reading A would cost and why relay does not type.

The answer depends on how a recursive box contributes facts. Under the orbit
reading of §1.3 the static system emits a G that satisfies (D), (R), (C) and (S),
generates a strict world, and violates (M). Under reading B, which Static.v used
before sharp edges 57 and which types a box body at every instance in one world, the
same program is rejected, and
the emitted set is not a finite set of unit schemas. Neither reading is shown here
to yield the gadget of Theorem 5.

### 8.1  Two readings of "emits"

A derivation emits the atoms its side conditions ask for (ORDERS-SPEC §16, "rules
emit facts instead of checking them"). The finitary system of Static.v adds one row
to the table of §1.3. Inside the body of a λ or a box the frame holds the frame
variable φ with the hypothesis u ≺ φ, and E-App checks x ≺ φ as x ≼_W u (sharp
edges 56). So every blocking point x in the body of a function with upper point u
emits one more atom.

```
E-App/φ  x ≼ u            x blocking in the body of λ or box with upper point u
```

The readings differ at E-Exp.

- Reading A (orbit, §1.3). G contains the body atoms at the instances in the orbit
  of the first instance under the substitutions at recursive calls. This is how we
  read "G closed under the substitutions at recursive calls" in ORDERS-SPEC §9.
- Reading B (every instance, Static.v before sharp edges 57). Rule t_box types the body for every
  instance xs of the box's ιs at the one world W. G must then contain the body
  atoms at every instance.

The soundness theorem of Static.v at that time covered reading B only, because
V-Box asked for every instance (sharp edges 52). After sharp edges 58 V-Box asks for
every instance xs with C[xs/ιs], and the theorem covers reading C. Reading A is therefore an interpretation of the
spec that the mechanized proof does not cover. A sound version of A needs V-Box
restricted to the instances of an orbit.

### 8.2  A program that violates (M) under reading A

The receiver relay holds the channel it received in the previous round while it
receives the next one, and it acts on the new channel first.

```
D  = ?∗.Close
S  = μX. ?(∃ι. D@ι). X

r  : □(∀ι ι′ ζ.^⊥  S@ι ⊗ Close@ι′ ⊸^ζ_⊤ ∗)
r  = !(f = λp. let (c, d) = p in
              let (e, c) = recv c in
              let (v, e) = recv e in let () = v in
              let () = close d in
              (force f) ⟨c, e⟩)

t₀ = let (d, c) = recv c in let (v, d) = recv d in let () = v in (force r) ⟨c, d⟩
```

P-Term types t₀ as an open process with Σ = c : S@(c, 0), where the point constant
is written c as in ORDERS-SPEC §13. We have not written out the partner. The
recursive call instantiates (ι, ι′, ζ) by (ι+1, ι[1]+1, ζ), and t₀ forces r at
((c, 1), (c[0][1], 1), (z, 0)) for a point constant z that no channel uses.

ζ is a ceiling. A loop that blocks at unboundedly many points needs an upper point
u with u[xs′] ≼ u[xs] at the recursive call (row E-App/φ) that lies above every
blocking point of the body. Under shift-only instantiation only a bound variable
with shift 0 or a constant does this.

Write c_k = (c, k) and d_k^j = (c[k][1], j). Round k ≥ 1 runs at the instance
(c_k, d_{k−1}^1, (z, 0)), and these instances form the orbit. We emit each ≼ of
row E-App/φ as ≺. Round k emits the following atoms.

```
recv c     c_k ≺ d_{k−1}^1                              c_k ≺ (z, 0)
recv e     d_k^0 ≺ d_{k−1}^1,    d_k^0 ≺ c_{k+1}         d_k^0 ≺ (z, 0)
close d    d_{k−1}^1 ≺ c_{k+1},  d_{k−1}^1 ≺ d_k^1        d_{k−1}^1 ≺ (z, 0)
call       (z, 0) ≼ (z, 0)
```

t₀ emits d_0^0 ≺ c_1. With k = κ+1 the round atoms are unit schemas over one
counter κ ∈ ℕ.

```
(c, κ+1) ≺ (c[κ][1], 1)
(c[κ+1][1], 0) ≺ (c[κ][1], 1)          (c[κ+1][1], 0) ≺ (c, κ+2)
(c[κ][1], 1) ≺ (c, κ+2)                (c[κ][1], 1) ≺ (c[κ+1][1], 1)
(c, κ+1) ≺ (z, 0)     (c[κ+1][1], 0) ≺ (z, 0)     (c[κ][1], 1) ≺ (z, 0)
(c[0][1], 0) ≺ (c, 1)                                                  ground, from t₀
```

**Claim.** W_G is strict, G satisfies (D), (R), (C) and (S), and G violates (M).

*Proof.* Rank c_k by 3k, d_k^0 by 3k+1, d_k^j for j ≥ 1 by 3k+6−1/j, and (z, j) by
ω+j. Every atom and every program-order step on these points raises the rank. Every
other point carries program order only. G has no alias schema, so W_G is strict.

Each schema has κ at most once per side, with coefficient 1, so (D) and (C) hold.
Without alias schemas Sh(G) is the set of prefixes {c, c.1, z}, so (S) holds. The
first schema puts κ at the offset of c and at the index coordinate of c.1, and every
other shared κ sits at one of these two positions. So the role r consists of these
two positions, one per shape, and (R) holds. The offsets of c.1 and of z hold only
constants and form roles of their own.

The ground fact (c[0][1], 0) ≺ (c, 1) puts constants at both positions of r, so r
carries a constant. The schema (c[κ+1][1], 0) ≺ (c[κ][1], 1) shares r with shift −1
and gives the shift graph of r a self-loop of weight −1 at c.1. ∎

Theorem 4 therefore does not cover the static system under reading A. relay is not
shift-only, because it instantiates ι′ by ι[1]+1. Its orbit lies in L anyway. A
reading of §1.3 that admits only shift-only boxes rejects relay, but that reading is
a syntactic restriction on recursion. The family c.1 has one counting coordinate,
so relay falls in the open case of §7.1.

### 8.3  Reading B rejects relay

At the instance ι′ = ι the first recv blocks at ι while it holds d at ι, and asks
ι ≺ ι. The ceiling fails as well, because x ≼ ζ would have to hold for every
point ζ. More generally a body atom s ≺ s′ that some instance makes reflexive is
never emitted into a strict world, and the instances x and x+1 of a one-variable
body hold together.

Under reading B the emitted set consists of ground atoms and atoms quantified over
all points. A send at the bound point ι in a box body emits ι ≺ ι[i] for every
point ι, which mentions the shapes f, f.i, f.i.i, … for every f. So G is not a
finite set of unit schemas over finitely many shapes, (M) is not defined for it,
and Theorems 1 to 5 do not apply. Its strictness problem is of the kind §7.2
describes.

Which recursive loops reading B types is not settled here. A loop that blocks at
ι, ι+1, … needs a point term u over the box's variables with ι+n ≼ u for all n at
every instance, and a bound ceiling variable does not qualify under B.

Under reading C (§9) relay still does not type (sharp edges 58). Its recursive call
at (ι+1, ι[1]+1, ζ) needs ι+1 ≺ ι[1]+1, and neither W nor C relates a slot of ι to
ι. A larger C does not help. Call a family a variable root with a slot path. W
relates two points of a family with a variable root by program order only, and
never two different such families. The call shifts ι by 1, so the instance of the
C fact from family ι with the largest offset starts above every hypothesis in that
family. From there only program order continues, and it stays in family ι. A target
in family ι.1 or at ζ is out of reach. The ceiling fails for the same reason,
because ι ≺ ζ in C does not give ι+1 ≺ ζ.

### 8.4  The gadget

relay realizes one ingredient of Theorem 5 that §6 does not list, a role that
carries a constant and has a negative shift. It is the cleanup edge
⟨h_t; κt+1, 0, 0⟩ ≺ ⟨h_t; κt, 0, 0⟩ in one coordinate. It does not realize the
gadget. Four pieces are missing.

1. Three counting coordinates in one family. The gadget uses points
   a[t][q][x][1][y][1] whose index coordinates t, x and y move independently. Under
   reading A each counter comes from a box. This needs three nested recursive boxes
   whose bodies act on channels received at depth 3 and hold the channel of the
   previous round at each level, as relay does at depth 1. §1.3 does not define the
   orbit of nested boxes with slot substitutions such as ι′ ↦ ι[1]+1.
2. Zero test and decrement at one coordinate. The zero branch needs a schema with
   the constant 0 at x while t and y are shared. The first action on a freshly
   received channel produces such constants. The decrement needs x shared between
   the channels of rounds t and t+1 with shift −1, from a lockstep inner loop over
   two received channels. Under reading A both code paths emit their atoms at every
   orbit instance. This matches the gadget only if the atoms of each path realize
   exactly its edge.
3. No extra cycles. Each blocking action emits an atom towards every held head and
   towards the ceiling, and each send emits ι ≺ ι[i]. A gadget edge may become a
   chain of such atoms. A reduction must show that no combination of these atoms
   closes a cycle that the run of M does not close.
4. A computable map M ↦ P_M with P_M well typed iff M does not halt. With pieces 1
   to 3 this makes type checking under reading A undecidable, beyond the
   undecidability of strictness for arbitrary schema sets.

Under reading A, typability does not imply (M). Decidable type checking then needs
one of three things. (M) becomes a premise of the static system, or a procedure
decides the emitted sets beyond Theorem 4, or a proof shows that programs never emit
the gadget. Under reading B the question is not posed in L, and §7.2 applies.

## 9  The checker under sharp edges 58

### 9.1  Reading C

Static.v types a program at one well-formed world W = W_G, and W knows constants
only (ORDERS-SPEC §12, sharp edges 57). E-Exp types a box body □(∀ιs. C.^u T) once,
with ιs as point variables and the hypotheses Ψ of the enclosing boxes followed by
C. Every side condition x ≺ y is read in slt W Ψ, the closure of ≺_W and Ψ under ≡_W
and transitivity, and x ≼ y as x ≡_W y or slt W Ψ x y. A force at xs asks C[xs/ιs]
in the same relation, which is ≺_W at top level (sharp edges 58). We call this
reading C. The soundness theorem of Static.v covers it.

A side condition is ground when all its points have constant roots and open
otherwise. A ground condition can enter W as a fact or an alias. An open condition
cannot, because W relates a point with a variable root only by reflexivity and
program order (sharp edges 57). C has ≺ facts only, so an open ≡ condition is
syntactic equality. G is therefore a finite set of ground atoms and ground aliases.
It has no counter variables, and the schemas of §1.3 do not arise.

The checker decides three things. W_G is strict. Every open condition is entailed by
W_G and the hypotheses in scope. And G is chosen so that both hold (Lemma 7).

### 9.2  Entailment and ground queries

**Lemma 5 (entailment).** Let G be ground, W = W_G, Ψ a finite set of ≺ facts over
point terms, and x, y point terms. Let N consist of x, y and the endpoints of Ψ, so
|N| ≤ 2|Ψ| + 2. The graph H on N has a strict edge u → v when u ≺ v ∈ Ψ, when u and v
have constant roots and u ≺_W v, or when u and v lie in one family with a variable
root and u has the smaller offset. It has a weak edge u → v when u ≡_W v. Then x ≺ y
holds in slt W Ψ iff H has a path from x to y with a strict edge.

*Proof.* A derivation of x ≺ y in slt W Ψ is a chain x = z₀, …, z_n = y whose steps
are ≺_W steps or Ψ facts, each up to ≡_W. Cut the chain at the endpoints of its Ψ
steps. Between two cuts every step is a ≺_W step, and these compose into one ≺_W
step by transitivity. ≺_W relates points with constant roots by the order W_G
generates, points of one family with a variable root by program order, and nothing
else. So every segment is an edge of H. Conversely every edge of H is a step of
slt W Ψ. ∎

Lemma 5 costs at most |N|² ground queries u ≺_W v and u ≡_W v and one search in H.
Lemma 6 reduces both queries to strictness.

**Lemma 6 (ground queries).** Let W_G be strict and x, y ground. Then x ≼_{W_G} y iff
W_{G ∪ {y ≺ x}} is not strict. Further x ≡_{W_G} y iff x ≼ y and y ≼ x, and
x ≺_{W_G} y iff x ≼ y and not y ≼ x.

*Proof.* ORDERS-SPEC §5 has successor and slot congruence for ≡ only, so the new fact
leaves ≡ unchanged and adds the single edge y → x to Γ_G. A closed walk with a strict
edge must use it, because W_G is strict. Between two uses it runs from x to y in Γ_G,
which gives x ≼_{W_G} y. Conversely x ≼ y closes such a walk. The other two claims
hold because a strict W_G never has x ≺ y and y ≼ x together. ∎

G ∪ {y ≺ x} is ground. It can add shapes to Sh(G) and make a role carry a constant,
so the hypotheses of Theorem 4 must be checked again for it.

**Lemma 7 (choosing G).** Let G₀ hold the ground conditions, and let P be the finite
set of ground points that occur in the open conditions and in the hypotheses in
scope. Some G ⊇ G₀ with W_G strict entails every open condition iff some
G₀ ∪ R does, where R is a set of facts and aliases between points of P.

*Proof.* Take a strict W′ ⊇ W_{G₀} that entails every open condition. Let R be the
facts a ≺ b and aliases a ≡ b with a, b ∈ P that hold in W′. W_{G₀ ∪ R} ⊑ W′, so it
is strict. By Lemma 5 each open condition needs only ≺_W and ≡_W between points of
P, and R supplies those. ∎

The search ranges over relations on P, finitely many, and each candidate costs one
strictness test and the entailments of Lemma 5. This bound is exponential in |P|. A
better one is open.

### 9.3  Strictness for ground G

Ground G lies in L with m = 0. The schemas of A(G) contain only the fresh variables
ν_k, each once per side, at the offsets or at the index coordinates the offsets
become. So (D), (C) and (A) hold, and Lemma 4 is not needed. Lemma 1 and Theorem 1
apply. (R) and (S) hold when every alias relates shapes of equal depth (§7.3).
Theorem 4 then decides strictness under (M).

Delegation breaks both premises. The payload alias x ≡ ι[i] relates the shape of x
to a shape one slot deeper than that of ι, so aliases of unequal depth are the rule.
(M) also fails for a plain program. A process receives d on c at instant 2, acts
twice on d, and sends d on c at instant 7. The payload alias is
(c[2][1], 2) ≡ (c[7][1], 0), and A(G) holds (c[2][1], 2 + ν₀) ≡ (c[7][1], ν₀). Its
shift on the offset role of c.1 is −2 in one direction. Any ground fact at an offset
of c.1 makes that role carry a constant, so the shift graph has a negative cycle.
The cycle is not a closed walk of Γ_G, because the index coordinates 2 and 7 are
distinct constants. So (M) rejects this G although no closed walk realizes the
negative cycle. A criterion that looks only at the walks Lemma 3 must realize is
open.

### 9.4  Status of the earlier results

| Result | Under reading C |
|---|---|
| Lemma 1, Theorem 1 | apply to ground G |
| Lemmas 2, 3, Theorems 2 to 4 | apply to ground G under (R), (S) and (M). (D), (C) and (A) hold outright |
| Lemma 4 | not needed, ground G has no coefficients |
| Theorem 5 | does not apply, it needs counter variables. Whether ground G can encode a two-counter machine through A(G) is open |
| §1.4, unbounded nesting | Static.v rejects the recursive receiver f. With C = {ι+1 ≺ ι[1]} the call at ι[1] asks ι[1]+1 ≺ ι[1][1], and no chain from family ι.1 at offset 1 reaches family ι.1.1 |
| §8, relay | does not type (§8.3) |

The argument of §8.3 applies to any recursive call that shifts a variable ι by
s ≥ 1 and needs a C fact from family ι to another family. A loop that alternates
between two channels at ι and ι′ and keeps ι ≺ ι′ in C is of this kind, because its
call at (ι+1, ι′+1) asks ι+1 ≺ ι′+1. Whether the examples of ORDERS-SPEC §13 type
under reading C is being tested separately.

## 10  Stepped boxes (sharp edges 61)

Plan only. Lemma 8 and Lemma 9 below are proved. The rest names the lemma each class
needs and says whether we have it.

### 10.1  What the checker decides

A box □(∀ιs. C.^u_Σ T) carries a finite set Σ of steps, substitutions on its ιs. C
holds at τ(ιs) for every word τ ∈ Σ*. The body is typed once under C, and a recursive
call at σ(ιs) with σ ∈ Σ asks nothing new, because the words of σ(ιs) are words of ιs.
Body conditions therefore stay finite and Lemma 5 decides them. A force at ground
points xs outside every box asks C^Σ(xs) ⊆ ≺_{W_G} with

```
C^Σ(xs)  =  { x[τ(xs)/ιs] ≺ y[τ(xs)/ιs]  |  x ≺ y ∈ C,  τ ∈ Σ* }
```

A force of another stepped box inside a body at open points asks an infinite family
of open entailments. This section does not decide it.

**Lemma 8 (force obligation).** Let G₀ hold the ground conditions and let F be the
union of C^Σ(xs) over all outside force sites. Some strict W ⊇ W_{G₀} entails F and
every open condition iff W_{G₀ ∪ R ∪ F} is strict for some R as in Lemma 7.

*Proof.* Every world that entails F contains W_{G₀ ∪ R ∪ F}, with R read off it as in
Lemma 7. Conversely W_{G₀ ∪ R ∪ F} has F as facts. ∎

So the ∀τ obligation becomes strictness of one schema set. Lemma 6 is still the tool
for the finitely many ground queries of Lemma 5. The world generated by F depends on
the set F only, so each fact of C contributes its own family f^Σ(xs) with its own
counters.

**Lemma 9 (no alias schemas).** F has ≺ schemas only, because C has ≺ facts only (58).
The aliases of G₀ ∪ R are ground. So every alias schema of the final G is ground,
and (D), (C) and (A) hold for the alias part as in §9.3.

Consequently G2 cannot arise under reading C with steps. (A) restricts alias schemas
only, and a ≺ schema may carry a counter at an offset on one side and at an index
coordinate on the other. The relay schemas below are of that kind and lie in L.

### 10.2  The three classes

**(a) Pure shifts.** σ_i(ι_j) = ι_j + s_ij. Steps commute, a word reduces to its count
vector n ∈ ℕ^m, and the root ι_j moves by s_j · n. A fact rooted at ι_j and ι_j′ has
one counter coordinate per side, at the offset or at the first index coordinate. Its
coordinate pairs form the monoid generated by g_i = (s_ij, s_ij′) ⊆ ℕ².

- Every g_i diagonal (s_ij = s_ij′). Unit schemas with equal coefficients after
  Lemma 4 and finitely many ground exceptions. Theorems 2 to 4 apply under (R), (S)
  and (M). Request/reply is here. σ = (ι+1, ι′+1) gives (a, κ) ≺ (b, κ) and
  (b, κ) ≺ (a, κ+1), shifts 0 and 1, so (M) holds and Theorem 4 decides it.
- Every g_i on an axis. Free coordinates. Theorems 3 and 4 apply.
- Diagonal and axis generators mixed. One side holds κ + κ′ with κ′ free, so the edge
  shares a role with shift set c + ℕ, c − ℕ or ℤ. Needed: Lemma 2⁺, Lemma 2 for
  interval shifts. SFZ extends by one LP variable y_{e,r} per interval edge and role
  with y ≥ c·x_e or y ≤ c·x_e, which keeps the LP homogeneous. In (M) an edge c − ℕ
  or ℤ counts as an unbounded negative weight. We expect the proofs of Lemma 2,
  Theorem 3 and Lemma 3 to go through with these changes. Not written out.
- A generator off the diagonal and off the axes. A scaling, open as §7.4.

**(b) One step that moves into slots.** Let j → j′ when σ(ι_j) is rooted at ι_j′. The
depth of σ^k(xs) is bounded iff no cycle of this functional graph contains a slot
entry. With slot-free cycles, after a finite tail and residue splitting by the cycle
lengths, each root carries one counter at one coordinate. Each fact then gives unit
schemas with one counter per side and finitely many ground instances. Equal cycle
shifts give (C), and Lemma 4 puts the family into L. No new lemma is needed, and the
class reduces to Theorems 2 to 4 under (R), (S) and (M).

The relay, σ = (ι+1, ι[1]+1) forced at ((c, 1), (c[0][1], 1)), has instances
ι = (c, κ+1) and ι′ = (c[κ][1], 1) for all κ ∈ ℕ. Its C, the side conditions of its
body, then yields exactly the round schemas of §8.2, for example
(c, κ+1) ≺ (c[κ][1], 1) and (c[κ+1][1], 0) ≺ (c[κ][1], 1). By the Claim of §8.2 this G
satisfies (D), (R), (C) and (S) and violates (M). So the relay is decidable iff the
open case §7.1 is, non-monotone boundary roles with one counting coordinate. G2 plays
no part.

**(c) Several steps that do not commute.** Words form a tree. Let U be the union of
the dependency graphs of the steps. A root's chain under a word is a path of U, so
depth is unbounded iff U has a reachable cycle through a slot entry. This test is
decidable.

- Unbounded depth. The instances are points with ever longer slot paths, as in §1.4.
  The graph is a prefix-rewriting graph whose letters carry counters (§7.2). Open.
- Bounded depth. The pair of chains of a fact is a path of the product of U with
  itself. Its coordinate vectors form a finite union of linear sets, from the
  decomposition of a path into a simple path and simple cycles. Each generator adds a
  cycle's shift to one coordinate per side. A component whose generators each hit
  distinct coordinates reduces as in (a). A coordinate hit by two diagonal generators
  that lead to two different coordinates of the other side holds a sum r = r₁ + r₂ of
  two roles. This is the ≺ form of G2. Lemma 2 fails exactly in its (⇐) step, where
  (D) and (R) let each role be assigned on its own. A sum edge ties two threads at one
  position of the walk, so validity depends on prefix sums and not on edge counts
  alone. Open.

### 10.3  What a decision procedure needs

1. Lemma 8 and Lemma 9, proved here.
2. (a) Lemma 2⁺ with SFZ and Lemma 3 extended to interval shifts. Planned, not proved.
   Scalings stay open.
3. (b) Nothing new beyond the open case §7.1, which the relay hits.
4. (c) The depth test, decidable. With bounded depth and no sum coordinates, as (a).
   Sum coordinates and unbounded depth are open.
5. Forces of stepped boxes at open points inside box bodies. Open.
