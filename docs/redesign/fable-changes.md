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

## Semantics

- Section intro says what the semantics is (a two-layer labelled transition
  system) and that points never appear. The deadlock-free view gets its own
  closing sentence.
- `sem-labels`, `sem-head`, `sem-ctx`, `sem-proc`, `sem-events`, `sem-props`:
  inline links to labels, head steps, frames, process steps, events, terms,
  constants, `csub`, configurations. `sem-proc` caption now walks the eight
  rules in words, and its `why` says why only close and link ask the channel
  to be restricted.
- `sem-props`: the deadlock-freedom sentence is visible in the deadlock-free
  view (it was wrapped in `\inmode{lf}`), the caption defines a terminated
  process and a pending thread, and a `breaks` field gives the two-channel
  cycle as a stuck process and the starving server as deadlock free but not
  lock free.
- **Check fix (ext/gv-check.js, one line).** The DF-LEAK regex `lock[- ]free`
  matched "deadlock free", so 22 deadlock-free sentences across the map had
  been wrapped in `\inmode{lf}` and were invisible in the deadlock-free view
  (among them "If $\varnothing \vDash_R p : T$ then $p$ is deadlock free").
  The regex now reads `(?<!dead)lock[- ]free`, and the 22 sentences are
  unwrapped (section intros of semantic and theorems, `sr-reading`, `sr-ord`,
  `ct-costs`, `rd`, `sj-all`, `th-chain`, `th-sound`, `th-adeq`, notes
  `se.reach`, `w.rord`, `w.strict`, `P-Connect.n`, `rd.p-term`, `sj.proc`,
  `th.adequacy`, `th.soundness`, `th.soundness-source`, `th.adequacy-h`).
- Notes `prop.*`, `ev.*`, `se.*`, `lbl.recv`, `T-Act-Recv`, `T-Act-New`,
  `P-Act-Link`, `P-Act-Msg`: "every" to "each" where it was rhetorical;
  `prop.pend` says what pending means; `P-Act-Msg.why` says why there is no
  $\mathsf{ech}\,o \in C$ premise.
