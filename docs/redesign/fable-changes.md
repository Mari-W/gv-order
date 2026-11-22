# Content pass over the explorer map, 2026-11-22

Branch redesign-fable, from redesign at 1ed17be. One entry per block or note that
changed, with the reason. Presentation only. System changes are proposals in
fable-findings.md and are not on the map.

Cross-references: every id in a block's `usedIn` list is now an inline `[[link]]`
in the using block, and formulas wrap types, judgments and operators that have a
definition in `\sym`. The "Also in" chips of the page are going away.

## Syntax

- Section intro. Says how to read the map (top to bottom, each section uses only
  earlier ones, hovers on symbols).
- `syn-ends`, `syn-prims`, `syn-terms`, `syn-values`, `syn-fends`, `syn-procs`,
  `syn-labels`, `syn-points`, `syn-moves`, `syn-csub`. Captions gained inline
  links to the blocks that use them (contexts, head steps, constant types, value
  and term relation, process steps, process typing and relation, creation,
  worlds, side conditions, actions, payloads). Each caption now ends with where
  the notion is used.
- `syn-terms` caption says why constants come with their argument ($\lambda x.\,k\,x$
  for a constant as a function). `why` says that terms carry no point and no
  annotation, so one program has many typings.
- `syn-points` gained an example that explains the fact $x \prec \overline{y}$ a
  thread needs when it closes one end while holding another. This is the first
  place a reader meets a fact.
- `syn-let` deviation reason was wrong ("an application of a $\lambda$"). It now
  quotes the actual definition, a pair elimination and a unit elimination.
- Notes `syn.unit`, `syn.lam`, `syn.let`, `syn.new`, `syn.op`, `end.cend`,
  `end.dual`, `syn.fchans`, `pt.const`, `pt.shift`, `pt.laws`, `link.csub`,
  `prim.link`: rhetorical "every" replaced by "each" or dropped. `syn.let.breaks`
  no longer writes $\mathsf{new}_\ell$, a former surface form.
- `prim.send`, `prim.recv`: a duplicate argument row `S` removed. `prim.select`:
  the argument row says which continuation is which.
