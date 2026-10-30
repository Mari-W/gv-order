# D.2 Adequacy for Padovani and Novara (FORTE 2015)

Status. Planned. Same procedure as for PGV (pgv-adequacy.md). Study first, then
model the system on our terms and translate it into the static system.

Source. L. Padovani and L. Novara, Types for Deadlock-Free Higher-Order Programs,
FORTE 2015, LNCS 9039, pp. 3–18. Indexed as padovani2015types with full text. The
longer technical report hal-00954364 has different rule names ([T-REC POLY], a
displacement constructor). The published chapter is the reference, and the
report is read only where the chapter leaves a gap.

## What the system is

A higher-order functional language with fork, new, send and recv over linear
channels, which are used exactly once. Synchronous communication, send blocks
(p3). Channel types p[t]^n carry a level n. Judgments Γ ⊢ e : t & ρ carry an
effect ρ, and arrows t →^{ρ,σ} s carry the level of the closure and the latent
effect (p8). Level polymorphism is level shifting ⇑ⁿ, applied by [T-APP-POLY] to
functions of level ⊤, and the recursive calls of fibo need it, so it is
polymorphic recursion (p10). Effect masking and polymorphic recursion are the two
key ingredients (p15). Examples are parallel Fibonacci (p5, p11) and a cyclic
signal pipe with a recursive channel type (p5, p13).

## Stage 1, study (stop and report afterwards)

1. How levels, effects and the arrow annotations work, rule by rule.
2. What effect masking is and why it is sound.
3. How [T-APP-POLY] and level shifting type recursion, and what "function of
   level ⊤" buys.
4. How the soundness proof uses levels. Look for gaps of the kind found in PGV
   (pgv-counterexamples.txt). Any program that types and deadlocks goes into a
   file padovani-novara-counterexamples.txt with only the program, why it types
   and why it deadlocks.
5. What one static order means for this system. Linear channels have one action,
   so falling sessions cannot occur. Shifting by n is an infinite family of
   instances, which our infinite constraints state.

## Stage 2, model and translate (after the author has seen stage 1)

- Linear channels as one-shot sessions on our terms. A channel of type p[t]^n
  becomes a session with one message at the point of level n.
- Arrows t →^{ρ,σ} s become T ⊸^u_ℓ U with ℓ from ρ and u from σ.
- Level shifting becomes a box ∀ι with the shift as the instance. [T-APP-POLY]
  applies only to functions of level ⊤, and our boxes hold no channel either.
- Recursion through fix becomes a recursive box whose constraint is the
  invariant over all shifts.
- Effect masking becomes whatever stage 1 shows it to be.
- World. Points by level, as for PGV, with the shifts as successor families.
- Theorem. A closed well-typed program is deadlock free, through soundness.
- Examples. fibo and the signal pipe, each with a closed deadlock_free proof.
