# B. Context-free session types

Notation: this file predates 2026-11-04 and writes p.j for the point now written p[j]; 'slot' and 'carried root' mean that point.

Goal. Deadlock freedom for context-free session types by orders, with the
compositional logical relation unchanged in shape.

## Background

Thiemann and Vasconcelos (ICFP 2016) add Skip and sequential composition S;S.
Equivalence holds up to the monoid laws and the distribution of choice over ;
(Lemma 3.4). Tree serialization needs polymorphism over the continuation,
sendTree : ∀α. Tree → TreeC;α → α, and polymorphic recursion, which the paper
calls essential (pp. 2–3).

Mordido and Pérez (2026) make context-free session types deadlock free with
priorities. Each channel carries a priority sequence, which new fixes as
n₁ + k·n₂. Priority polymorphism ranges over intervals, and fix is a constant.
Our counterpart replaces the fixed sequences by a world. It admits cycles and
partial orders.

## Outline

1. Session syntax. S ::= Skip | S;S | !T | ?T | ⊕{…} | &{…} | μX.S | X, with
   duality pointwise. The relation needs only the head normal form of a
   contractive type (unr, Lemma 3.8 of Thiemann and Vasconcelos). A
   synchronization obligation reads the first action, so E and P keep their
   clauses.
2. Points after a segment. An instant still counts actions, so points stay
   (c, k). After sendTree the continuation sits at ι + n, and n depends on the
   tree. The type quantifies over the offset.

   ```
   sendTree : □(∀ι ζ α. C. Tree → (TreeC;α)@ι ⊸^ζ ∃n. α@(ι+n))
   C = {ι+k ≺ ζ ∣ k ∈ ℕ}
   ```

   The ceiling ζ is the one of the tail-call example. The recursive calls stay
   inside C for every offset, because C[ι+1+n/ι] ⊆ C. This coarse version needs
   offset variables in points (ι+n with n bound by ∃) and nothing new in the
   constraint language.

   The coarse ceiling also bounds the continuation, and that fails as soon as
   another channel acts between the segment and the continuation.

   ```
   sendTree t c ; close d ; send v c
   ```

   The world needs (c,k) ≺ (d,0) for k < n and (d,0) ≺ (c,n), with n the size of
   t. Two additions can express it.
   - Facts that depend on data. C = {ι+k ≺ ζ ∣ k < n} ∪ {ζ ≺ ι+n} with n a term
     over the tree (direction C, offsets as terms). The world of a closed program
     then contains facts at the concrete n.
   - Segment ends as names. A new root names "the instant where the segment that
     starts at x ends", like a carried root names a message position. ζ below
     the end is then a plain fact. Every point of the segment below ζ becomes
     the conditional fact x+k ≺ end ⇒ x+k ≺ ζ, which is not positive.
     The run fixes the alias between the end and a concrete instant, so the world
     must learn an alias between existing points while the program runs
     (direction C, worlds that grow).
3. Polymorphism over session types. ∀α under □, next to ∀ιs. α occurs only in
   session positions S@x, and V reads those only through V-Chan. If V recurses on
   the value structure of a type and treats session subterms as opaque, T[S/α]
   has the structure of T and V stays well founded without an index cost.
4. Static rules. Skip, sequencing, conversion up to the CFST equivalence and
   Γ ⊢ ≡, and instantiation of α at force. Recursion stays an ordinary force.
5. Composition. P-Connect, P-Term and the bind lemma read labels only. They carry
   over without change.

## Target examples

- sendTree and recvTree (Thiemann and Vasconcelos 2016).
- Stream, the binary tree with polymorphism per node, and the asynchronous
  scheduler A.5 (Mordido and Pérez 2026). Every example of Mordido and Pérez
  should type here, which feeds direction D.

## Decisions for the mechanization (2026-10-30, overnight, to be confirmed)

The author asked for full context-free session types on the logical relation.
The decisions below follow the philosophy of the core. They keep the relation
and the composition lemmas free of syntactic premises, stay close to Thiemann
and Vasconcelos, and leave PGV and Padovani–Novara alone. Each is provisional
and logged in SHARP-EDGES.

- K1. Session syntax. S ::= Skip | S;S | !P | ?P | ⊕(S, S) | &(S, S) | Close |
  μX.S | X | X̄. Send and receive lose their continuation, as in Thiemann and
  Vasconcelos. Choice is binary, and n-ary choice nests. The existing session
  type variables X and their duals X̄ serve as continuation variables.
- K2. Close needs no position rule. After a close the entry leaves the
  environment, so the rest of Close;S is never read. No well-formedness
  condition forbids it.
- K3. Equivalence is bisimilarity on the LTS of Thiemann and Vasconcelos over
  contractive types, with the monoid laws of Skip and ;, the distribution of
  choice over ;, and equirecursive μ. The relation reads only the head normal
  form unr(S), whose cases are Skip, !P;S′, ?P;S′, ⊕(S₁,S₂), &(S₁,S₂), Close and
  a variable. Duality is pointwise and maps X to X̄.
- K4. Choice in the calculus. Two new constants select₁, select₂ and one new
  constant branch with labels c◁i and c▷i. Selecting gives a step like send and
  costs 0. Branching waits like receive and costs 1. branch returns a sum, so
  case does the dispatch. Readiness treats a selection like a send and a branch
  like a receive.
- K5. Points. Every action, choices included, moves the instant by one. Skip
  and ; move nothing.
- K6. Polymorphism over the continuation. A box binds session type variables
  next to its point variables, □(∀ιs αs. C. ∗ ⊸^u_⊤ T). V-Box quantifies over
  all closed session types for αs. V reads a session type only through V-Chan,
  so instantiating α keeps the recursion of V well founded.
- K7. Existential points. A new type former ∃ι. C. T with a positive
  constraint C, the dual of the box binder. V⟦∃ι. C. T⟧ holds when some point x
  satisfies C[x/ι] and the value lies in V⟦T[x/ι]⟧. sendTree returns
  ∃ι′. C. α@ι′ for the instant after its segment.
- K8. Facts about segments use the coarse ceiling, a point ζ with ι+k ≺ ζ for
  every k. Facts that depend on the length of the segment wait for direction C.
  The example sendTree t c ; close d ; send v c stays outside.
- K9. Branch layout. The work happens on a branch cfst from orders-lr. PGV and
  Padovani–Novara (theories/pgv, theories/pn) leave that branch's build and are
  not ported.

## Order of work

1. Stage A. Session syntax K1, head normal form, contractiveness, bisimilarity
   and duality K3, choice constants and labels K4 in the LTS.
2. Stage B. The relation for the new labels and the head normal form, readiness,
   costs, and the composition lemmas P-Connect, P-Term, internalizing a link and
   the bind lemma.
3. Stage C. Boxes over session variables K6 and existential points K7 in the
   relation and in the static system, then the fundamental theorem.
4. Stage D. Examples from the literature, each with a closed deadlock_free
   proof, or a precise reason why it falls outside.
   - sendTree and recvTree (Thiemann and Vasconcelos 2016, pp. 2–3).
   - The binary tree channel with polymorphism per node, the stream of
     Listing 1.1, the classic deadlock scenario (rejected), and Milner's
     scheduler A.5 (Mordido and Pérez 2026, pp. 3–5, 37–38).
   - Further CFST examples from the papers store ([EXAMPLE] facts) and from
     FreeST, for instance an arithmetic expression server.
   - A tree server that recurses on both subtrees.

Stages A and B cost the most. Each stage ends with a full build, closed Print
Assumptions and a report.
