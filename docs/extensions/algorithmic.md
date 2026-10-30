# A. Algorithmic typing

Goal. Type the examples without hand-written derivations, worlds and rank
proofs. Completeness is not the goal. The declarative system of spec §9 stays the
reference, and the algorithm is sound for it.

## Outline

1. Linear structure. Session types, environment splitting with input and output
   contexts, and conversion on regular session types. Standard GV techniques make
   this decidable. Points play no role here.
2. Fact generation. A judgment Θ; Δ ⊢ t : T ⇝ 𝒞 generates fresh point variables
   at new, at λ (μ, ℓ) and at force. It solves ≡ by union-find with congruence
   closure for successor and carried roots, which also fixes the payload points
   of send and recv. It collects the ≺ atoms in 𝒞.
   Rocq: every strict world that satisfies 𝒞 under an assignment yields a typed
   derivation at that world.
3. Non-recursive fragment. Without boxes 𝒞 is finite. The world is its closure
   and strictness is a cycle check modulo ≡, in polynomial time. This types sync,
   cycle, scheduler and delegation, and rejects blocked and bad link.
4. Boxes with annotations. The programmer writes ∀ιs and C. Two fragments are
   compared by which examples they type.
   - Decidable. Finite C plus counter facts with constant offsets, each counter
     once per side. A recursive call is matching under a counter shift.
     docs/DECIDABILITY.md analyses strictness for this fragment.
   - SMT. Linear arithmetic over offsets. Strictness by a ranking certificate
     (linear or lexicographic) that the solver finds and Rocq checks.
5. Parser and checker. A small front end for writing example programs and running
   them through the algorithm.
6. Recursion and inference of C. To be discussed. One heuristic closes the facts
   of one round under the call substitution, C = ⋃ₖ C₀[σᵏ(ιs)].

## Open questions

- Which fragment types the four recursive examples (request and reply, relay,
  tail call, received chain) and the forwarder.
- Whether certificates for strictness should be checked in Rocq or trusted.
