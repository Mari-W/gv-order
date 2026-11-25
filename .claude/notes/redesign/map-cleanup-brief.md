# Final map clean-up, 2026-11-24, brief for three passes

The author asked for a final clean-up of the relation map, in three passes
run one after the other: Opus, then Fable, then Opus. Each pass works on its
own branch from the current tip of `redesign`, commits there, and never
pushes or merges. Each pass appends its report to
docs/redesign/map-cleanup.md under its own heading.

## Scope

- The source is docs/explorer/map.json. Read docs/explorer/BLOCKS.md and
  docs/explorer/MAP-SKILL.md first. Check with `docs/explorer/check.sh`,
  which must end with 0 errors. Try to lower the warnings, and list the
  ones you leave with a reason.
- Content only. No change to tools/proof-map, check.sh, index.html or the
  extension in ext/, and no Rocq change. If a tool bug blocks you, write it
  down in the report.
- The map must match the Rocq in v2/ at the tip of `redesign`. Every cited
  Rocq name exists and says what the map says. Recent merges to reflect:
  examples/BranchExt.v, Descent.v, PointReuse.v, Rejects.v, CopycatTwoN.v,
  static/Skeleton.v, PointSubstTyped.v, ConnectNExact.v, and the liveness
  files (liveness/LivePConnect, LivePTerm, LiveGuardProc). Programs the map
  calls typed, rejected, deadlock free or lock free carry the Rocq result
  that proves it, or the map says "argued" plainly.
- Design decisions are not yours. A quirk, a simplification of a
  definition, an unnecessary assumption or lost generality goes into the
  report as a question for the author, never silently into the map.

## Text rules (the author's standing rules)

- Mathematically rigorous. Math notation wherever possible, explicit
  quantifiers, precise terms, symbols in $…$.
- Self-contained. No citations of decisions, Q or F numbers, counterexample
  names, log entries or file names in prose. Rocq names only in their own
  field.
- Nothing undefined. Every symbol is defined on the page before its use.
- No horizontal scrolling of definitions.
- One toggle, DF or LF. LF is DF plus additions, every addition coloured in
  LF and absent in DF (\annot{…}, \annraw{…}, \annp{…}, LF-only rows and
  blocks). check.sh reports any DF-LEAK as an error.
- No coined or informal vocabulary. Forbidden: soup, bookkeeping, hop,
  tick, refill, spare, holder, waiter, fueled, partner end, slot, gate,
  priority, pruning, frame (for the future F), relay, and any new name an
  agent invents. Use: lock-free process relation (state: annotated
  configuration), counter bound N, transfer, decrement, thread holding o,
  dual end, dual point, positive, F-Count, field σ.κ, future F. Rocq names
  keep their names.
- Notation. Letters Γ facts, Δ variables, Θ term channel environment, Σ
  process interface, W static world, R relation world, i term variables.
  End types $S_x^{a,m}$ (plain $S_x$ in DF), fuel $S^{f,m}$, protocol
  variants with primes, never $S_1$.
- Prose style. No colons, semicolons or em dashes in prose (math and code
  exempt). No "since" for causation. No hedging. Claim first. Active voice,
  present tense. No filler adjectives (novel, significant, comprehensive,
  robust, crucial, …). No summarizing last sentence. Mean sentence length
  about 21 words. Explain what happens in the program, not metaphors.
- Easy for humans. A reader new to the project should follow each section
  from the intro, the captions and one example.

## The three passes

1. Opus, faithfulness. Audit every block, theorem row and example against
   the Rocq. Fix wrong statements, stale names, missing recent results and
   wrong status claims. Fix rule violations you meet. Leave prose polish to
   pass 2.
2. Fable, content and prose. Restructure where it makes the story clearer,
   rewrite captions, intros and example descriptions under the text rules,
   add cross-links (to arguments, rules, examples), check that every
   example works and is described correctly. Look for simplifications,
   standard notation, unnecessary assumptions and lost generality, and
   write each one down as a question. Keep pass 1's faithfulness.
3. Opus, verification. Re-check everything pass 2 touched against the Rocq
   and the rules, revert or fix anything that drifted, run check.sh, and
   write the final report with the open questions for the author.
