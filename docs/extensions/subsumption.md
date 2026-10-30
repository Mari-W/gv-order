# D. Subsumption of related systems

Goal. Every program that a related deadlock-free system types also types here,
through a translation of its derivations. The paper can then say that orders
generalize priorities, trees and acyclic worlds.

## Targets

| System | Calculus | Translation idea | Needs |
|---|---|---|---|
| GV♯ (the paper) | GV, tree topology | trees give a world without cross facts | core |
| PGV (Kokke and Dardha 2021) | GV with priorities | priority of an action becomes the rank of its instant | core |
| Padovani (CSL-LICS 2014) | linear π | priorities as ranks, shifting z ↦ z+n as box instances | encoding of π into GV |
| Mordido and Pérez (2026) | GV with context-free sessions | priority sequences n₁ + k·n₂ as infinite constraints | B |
| Balzer, Toninho and Pfenning (ESOP 2019) | shared sessions | their acyclic order on worlds as facts | shared channels |
| Dardha and Gay, Kobayashi | π with usages and levels | levels as ranks | encoding of π into GV |

## Outline for PGV

1. Points from priorities. A PGV session type writes a priority o on every action,
   !^o T.S. The instant of that action gets rank o, and the world orders instants
   by rank. Every PGV side condition has to become a strict fact. Where PGV
   compares with ≤, the translation needs a tie-breaking rule.
2. Arrows. PGV writes T ⊸^{p,q} U with a lower bound p and an upper bound q on
   the effect. They map to the lower point ℓ and the upper point u of T ⊸^u_ℓ U.
3. Derivations. Translate each PGV rule into a derivation of spec §9 at the
   world of step 1. Fork in PGV is derived from new and spawn, as here.
4. Statement. If ⊢_PGV p, then ⊢_W p for the world W of its priorities, and W is
   strict.

## Outline for GV♯

The tree topology of the paper induces an order in which no two components share
a cross fact. Each GV♯ derivation translates to one here, and the extrusion split
becomes an instance of P-Connect. This makes the order system a conservative
extension of the paper's.

## Open questions

- Padovani and Kobayashi type π-calculi. Subsumption there needs an encoding of
  processes into GV, and the result is weaker than a direct translation.
- PGV and Mordido and Pérez use numeric priorities with arithmetic on them. Our
  worlds are partial orders. Every assignment into ℕ gives a world. The converse
  fails for worlds. The tail-call world puts infinitely many instants below
  (z,0) and has no rank into ℕ (tc_deadlock_free uses a pair rank). Whether some
  program types here and not in PGV is a separate question.
- Whether the translations go in Rocq. PGV and GV♯ are small enough. The others
  stay on paper.
