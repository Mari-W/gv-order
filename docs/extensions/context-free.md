# B. Context-free session types

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

   The ceiling ζ is the one of the tail-call example. It also bounds the
   continuation. A finer version asks ι+k ≺ ζ for k < n only, and then the facts
   depend on the existential n. Direction C decides this.
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

## Order of work

1. Design note on point 2, together with direction C.
2. Types, duality and head normal form in Rocq.
3. The relation and the composition lemmas.
4. The static system.
5. The examples.

Steps 2 and 3 cost the most.
