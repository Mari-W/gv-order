# Deciding strictness of W_G

State of 2026-10-30. Paper-level. Nothing here is mechanized. Notation follows
ORDERS-SPEC.md §4, §5 and §9.

## 0  Results

Strictness of W_G is decidable for every finite G in the schema class L of §1 that
satisfies four syntactic side conditions (diagonal freedom, role consistency,
equal coefficients, monotone boundary roles) and a fifth, finite shape closure,
that holds for every example but is not shown decidable here. When no role
carries a constant the procedure is polynomial in the size of the static graph 𝒢
of §2. Otherwise it is polynomial in the size of an abstract graph that grows
exponentially in the number of constant-carrying roles per shape (Theorems 2 to 4). The free-coordinate extension that ORDERS-SPEC §16 calls open
is Theorem 3.

Two claims of ORDERS-SPEC do not hold as stated.

- "Boundary facts reduce by unrolling" is false once a family has three counting
  coordinates. Strictness for unit schemas with constants is undecidable, already
  without aliases and with nesting depth 3 (Theorem 5, a reduction from
  two-counter machines).
- Slot names do not nest boundedly in programs. A recursion on a received channel
  needs the points c, c[0][1], c[0][1][0][1], … (§1.4). Any finite G has bounded
  depth, so the static system rejects such a program. This is a completeness gap,
  not a decidability gap.

Proved here are Theorems 1 to 5 and Lemmas 1 to 4. Cited are the linear-programming
characterization of zero multicycles and the recursive SCC scheme of Kosaraju and
Sullivan (STOC 1988, pp. 399–400), polynomial-time linear programming, and the
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
□(∀ιs. T) the atoms mention the bound point variables ιs. "G closed under the
substitutions at recursive calls" means that G contains the facts of every instance
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

**Lemma 1 (alias closure).** On points of shapes in Sh(G), ≡_{W_G} is the
equivalence generated by the instances of A(G).

*Proof.* The instances of A(G) are aliases of W_G by successor and slot congruence,
which gives one inclusion. For the other, let R be the set of instances of A(G)
and E its equivalence closure. E is closed under +1, because R is (shift ν_k). If
x E y by a chain x = z₀, …, z_m = y and x[i] has a shape in Sh(G), then each z_j
is related to x by a chain of alias schemas, so each z_j[i] has a shape in Sh(G)
by alias transfer, and z_j[i] R z_{j+1}[i] by the instance of A(G) with w extended
by i. So E is closed under slots on Sh(G). E contains the base aliases, so E
contains ≡_{W_G} restricted to Sh(G). ∎

**Theorem 1 (reduction).** Under (S), W_G is strict iff Γ_G has no closed walk
that contains a strict edge.

*Proof.* The order of W_G is the transitive closure of the strict edges composed
with ≡ on both sides, read on ≡-classes. It is irreflexive iff no point x has
x ≺⁺ x modulo ≡, that is, iff there is no closed walk of strict edges and
≡-steps with at least one strict edge. By Lemma 1 a ≡-step between points of
Sh(G) is a path of weak edges. It remains to show that points outside Sh(G) lie on
no such walk. By alias transfer, a derived alias relates a point of shape g.w to
one of shape h.w with g, h related by an alias schema, and g.w ∈ Sh(G) iff
h.w ∈ Sh(G). So no ≡-step and no edge leaves or enters the outside part except
program order, which keeps the shape. Every ≺ schema mentions shapes of G only.
Inside the outside part, aliases preserve the offset and program order raises it,
so it carries no closed walk with a strict edge. ∎

The static graph 𝒢 is the finite multigraph whose vertices are the shapes of
Sh(G). Each ≺ schema and the program-order schema of each shape give a strict
edge, and each schema of A(G) gives two weak edges, one per direction. Every
closed walk of Γ_G projects to a closed walk of 𝒢.

## 3  Roles

Union the coordinate positions (f, j) over all edges of 𝒢 whenever one shared
variable sits at (f, j) on one side and at (g, j′) on the other. The classes are
roles.

Role consistency (R). No role contains two positions of the same shape.

Under (R) every vertex (f, x) has at most one r-coordinate x_r for each role r,
and R(f) denotes the roles present at f. For an edge e and a role r, e shares r
when a shared variable carries r from source to target, with shift δ_e[r] ∈ ℤ.
Otherwise e cuts r. An edge cuts r when r is absent on one side, when it holds a
free variable on one side, or when it holds a constant on one side.

(R) and (D) are checked by one union-find pass over G. Program order shares every
role of its shape, with shift 1 on the offset role and 0 elsewhere. The schemas of
A(G) share the roles of s and s′ and the fresh roles ν_k.

**Lemma 2 (threads).** Assume (D) and (R) and that no schema of G contains a
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

This is Kosaraju and Sullivan's multicycle LP (their Thm 2.4, p. 399) with the
labels restricted to the roles outside S. A feasible x scales to an integral
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

**Theorem 3 (free coordinates).** Under (D) and (R), for constant-free G, SFZ(𝒢)
returns Yes iff Γ_G has a closed walk with a strict edge, and it runs in
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
Kosaraju–Sullivan (Thm 3.3, p. 400), the calls at one recursion depth work on
disjoint subgraphs, and the depth is at most |V(𝒢)|. The total is
O(|V| · (|roles| + 1) · |E|) feasibility tests of linear programs with |E|
variables and |V| + |E| + |roles| constraints, each polynomial. ∎

**Theorem 2 (uniform schemas).** If every edge shares every role of both its
ends (no free variables, no constants, equal role sets), then S = ∅ throughout,
SFZ is Kosaraju and Sullivan's ZCYCLE with the extra requirement of a strict edge,
and strictness of W_G is decided in O(|V| · |E|) LP tests.

The strict-edge requirement is the only change to ZCYCLE. ZCYCLE asks for a zero
cycle, and strictness asks for a zero cycle through a strict edge. Weak edges
alone form zero cycles (an alias and its reverse), and those cycles are harmless.
The domain ℕ instead of ℤ costs nothing (the shift-up step in Lemma 2).

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

**Lemma 3 (abstraction).** Under (D), (R) and (M), Γ_G has a closed walk with a
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

**Theorem 4 (boundaries on monotone roles).** Under (D), (R), (S) and (M),
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
that satisfy (D), (R) and (S), use no alias schemas, and use shapes of depth at
most 3. The roles that carry constants then violate (M).

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
   family is open. The criterion (M) is
   syntactic and cheap. Whether the static system can violate it is open. If it
   can, either the static system must enforce (M) or the type checker cannot be
   complete for strictness.
2. Slot nesting is unbounded in programs (§1.4). The static system types only
   programs whose orbit closure fits a finite G. A schema language with variables
   ranging over names would cover the recursive receiver. Its graphs are
   prefix-rewriting graphs with counters, and nothing here decides them.
3. (S), finiteness of the shape closure, is defined but its decidability in
   general is not proved here. It holds when every alias schema relates two shapes
   of equal depth, because transfer then preserves depth and the slot indices come
   from G.
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
   "closed under the substitutions at recursive calls" changes the class.

## References

- S. Rao Kosaraju, Gregory F. Sullivan. Detecting cycles in dynamic graphs in
  polynomial time. STOC 1988, pp. 398–406. Store key `kosaraju1988detecting`.
  Used: Thm 2.2 and 2.4 (p. 399), VPARTITION, ZCYCLE and Thm 3.3 (p. 400).
- Marvin L. Minsky. Recursive unsolvability of Post's problem of "Tag" and other
  topics in theory of Turing machines. Annals of Mathematics 74(3), 1961. Store key
  `minsky1961recursive`. Cited for undecidable halting of two-counter machines,
  not re-read here.
