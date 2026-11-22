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

## Types and worlds

- Section intro says why there are two kinds of world (a derivation sees
  constants, a run sees fresh roots) and that they meet in $R \vDash W$.
- `ty-grammar`: caption explains $u$ and $l$ in words and links session types,
  points, active points, annotations, the judgment and the value relation. New
  example with an end before and after a send and the arrow type of a closure
  that captured it.
- `ty-session`: caption explains `unfold`; `why` explains `Skip`, sequencing and
  why contractivity is asked (links to the contractivity example); new example.
- `ty-dual`: caption explains $\mathsf{flip}_\alpha$; links to creation, link,
  composition.
- `ty-equiv`: caption defines $\simeq$ in words and says who uses $\simeq$ and
  who $\approx$.
- `ty-heads`: caption and example explain $\mathsf{ap}$ as "the points at
  which the partners act next" and why an arrow records one point $l$.
- `ty-payload`: caption says why sender and receiver compute the same fields.
- `ty-ann`: the redundant `\inmode{lf}` inside a lock-free block is gone;
  links to conservativity and the counters block.
- `ty-kinds`: links P-Term, weakening/contraction, aging, value relation.
- `w-world`: caption links order, extension and process typing; `why` says why
  a static world speaks about constants only; new example world with a ranked
  model in the lock-free view.
- `w-order`: caption links the order judgment and readiness; `why` justifies
  $x \prec \overline{x}^{+}$; new example of derived facts.
- `w-wf`: the deadlock-free caption no longer says "$N = \infty$" (a lock-free
  notion). `why` says that acyclic and well-founded differ only on infinite
  worlds and why static worlds are infinite.
- `w-ext`: the formula now defines $W \sqsubseteq W'$, $W_1 \sqcup W_2$ and
  $W|_S$ (they were bare symbols). The sentence on acyclic joins was wrapped in
  `\inmode{lf}` and invisible in the deadlock-free view although the rule is
  shown there; it is now plain. New example of two acyclic worlds with a cyclic
  join. Note `w.restrict` declares $\mathsf{root}$ as `croot_in`.
- Notes `ty.*`, `sty.*`, `ann.*`, `w.*`: "every" to "each" where rhetorical.

## Typing

- Section intro states the one idea of the system (a thread that waits at $x$
  while it holds an end whose partner acts at $y$ needs $x \prec y$).
- `t-judgment`: caption links contexts, types, active points, aging; `why`
  says what the future replaces (a global order on actions).
- `t-contexts`: **the end type in $\Delta$ was shown as $S_x^{a}$ while the
  Rocq `tentry` has a credit and tickets.** It now reads $S_x^{a,m}$, as in
  the counters block, and E-Chan likewise. New example of a derived fact.
- `t-side`: links to the four rule blocks that use the checks.
- `t-lf-counters`: caption links annotations, aging, actions, link, closures,
  spawn, creation, fuel values and the lock-free process relation. `why` now
  says why one number cannot do both jobs.
- `t-lf-wf`, `t-agecap`: links; `t-agecap.why` says why idle ends truncate.
- **The guard appeared twice** (a summary table `t-lf-guard` and the rules
  `g-guard`). The table block is gone. The rules block now sits where the table
  was, after the counters, with the summary folded into its caption and the
  `usedIn` lists merged.
- `r-base`, `r-fun`, `r-data`, `r-boxes`, `r-ex`, `t-consts`, `r-act`,
  `r-threads`, `r-new`, `t-subs`, `p-typing`: inline links to the definitions
  each rule reads (side conditions, active points, session types, payloads,
  moves, duality, kinds, the judgment, the constants, the value relation, the
  obligations, readiness, composition). New examples for E-Abs (a closure type
  and the caller it rejects) and P-Term/P-Connect (the two-thread close).
- `r-act`: **in the deadlock-free view the premise that the sent value is a
  subtype of the payload type was invisible**, because the whole premise
  $T' - 1 \leq T[x\cdot i]$ was lock-free coloured. It now reads
  $T' \leq T[x\cdot i]$ in the deadlock-free view and $T' - 1 \leq T[x\cdot i]$
  in the lock-free view. Note `E-Send.floor` rewritten accordingly.
- `r-new.why` answers three "why not simpler" questions: why not one rule
  with a position, why fields at all, why hide the root. `r-ex.why` says what
  hiding buys. `p-typing.why` says what hiding buys for composition.
- `t-subs.why` says the one reason subtyping exists.
- 21 nested `\inmode{lf}{\inmode{lf}{…}}` collapsed to one level (no change
  in either view).

## Semantic typing

- Section intro says in two sentences what "safe" means.
- `sr-reading.why` explains how the relation proves the rules (one
  compatibility lemma per rule, the fundamental theorem as the induction,
  adequacy off readiness, and when a premise is justified).
- `sr-ord.why` tells a reader used to natural-number indices that nothing is
  lost in the deadlock-free view.
- `ct-costs.why` says why a send is free and a receive costs one.
- `v-rel`, `e-rel`, `e-obl`, `rd`, `p-rel`, `p-obls`, `fu-vs`, `fu`,
  `fu-obls`, `fv`, `soup`, `sj-all`: inline links to the types, values, ends,
  worlds, costs, rules and the blocks that use each relation. `e-obl.why`
  says that O-New chooses position and facts inside the relation. `rd` gained
  an example of two threads that cannot both be ready. `p-rel.why` says what
  fusion saves. `fu.why` says why fuel is separate from the relation.
- `sj-all`: **the semantic term judgment bound $n$ and used $\alpha$**; the
  binder is now $\alpha$ in both views. Caption explains the hidden judgment.
- Cost subscripts $\kappa_{give}$ etc. are set in `\mathrm` (they were read as
  products of variables), and the two `\text` labels of `fu-obls` are `\textsf`.

## Theorems

- Section intro and all captions now show the deadlock-free sentences in the
  deadlock-free view (see the check fix above).
- `th-chain`: lock-free sentences restructured as siblings, "excluded middle"
  in the deadlock-free sentence replaced by "a classical hypothesis".
- `th-sound`, `th-compose`, `th-fund-proc`, `th-adeq`, `th-conserv`,
  `th-terms`: inline links to properties, events, worlds, ranked worlds,
  semantic judgments, the process relation, fuel, values with fuel, E-App,
  frames, annotations. `th-adeq.why` sketches the adequacy argument.
  `th-compose.why` says what fusion buys and points at the flag example.

## Examples

- Each lead now says what the example demonstrates and links the rules and
  theorems it uses (E-Box/E-Force, E-New, E-New-Field, side conditions, the
  guard, aging, E-Send, E-Link, P-Term, P-Connect, composition, adequacy,
  soundness, the join of worlds, `gen_new`, contractivity).
- `xref-missing` of the merged checker: 0.
