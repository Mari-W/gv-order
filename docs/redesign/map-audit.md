# Map audit, 2026-11-22

Branch redesign-map, from redesign at 1401e2d. The audit checks every block,
caption, note and example of docs/explorer against the Rocq of v2/ on this
branch, against the map deltas of the reports in docs/redesign/pending.md,
and against the proof-map checker of branch mapkit. Measured boxes are left
out (branch redesign-mbox).

Each entry gives the block or note id, the old and new text or formula, the
reason, and the Rocq name it was checked against. Sections follow page order.

## Syntax

- Section order (layout.js). Old: terms, let, constants, values, ends, fends,
  processes, points, moves, labels, link substitution. New: ends, constants,
  terms, let, values, fends, processes, labels, points, moves, link
  substitution. Why: checker (var-before-intro of $o$, $k$, $\kappa$), each
  block now uses only what earlier blocks define.
- `syn-terms`. Old: variable $x$ and the former $k$. New: variable $i$ and the
  former $k\,e$. Caption old "Thirteen term formers with de Bruijn variables.
  A box $!e$ binds itself in $e$, and $k$ ranges over the constants." New
  names the binders of λ, case and the pair let, and says that a constant
  always comes with its argument. Why: Rocq change and faithfulness, `Op (k :
  prim) (e : expr)` is a saturated constant, and $x$ clashed with points in
  E-Var next to E-Chan. Checked against `expr`, `Op`, `Var`.
- `syn-values`. Old: $v ::= \ast \mid o \mid k \mid \lambda e \mid \ldots$. New:
  $k$ removed, caption adds "A constant applied to a value is a redex, never
  a value". Why: faithfulness, `is_val` has no case for `Op`. Checked against
  `is_val`.
- `syn-prims`. Caption and title note rewritten: the constants cover channels,
  threads and boxes, one former $k\,e$, one typing rule per constant. Old why
  text claimed "each has an ordinary function type". Checked against `prim`,
  static/Constants.v `k_send`.
- `syn-ends`, `syn-procs`. Captions introduce $c$, $p$ and $q$ before use.
  Why: checker (var-before-intro).
- Notes `syn.var`, `syn.op`, `syn.values` and their signatures follow the
  three changes above. `syn.op` old "A constant $k$ is a value", new "The
  term $k\,e$ applies the constant $k$ to its argument $e$ ... never a value",
  cites `Op` and `k_send` in place of the citation text "(the value $k$ is
  $\lambda x.\,k\,x$)".

## Semantics

- `sem-head`. New rows T-Act-Let (unit and pair elimination) and T-Act-Case,
  with notes `T-Act-Let` and `T-Act-Case`. Old: only application and force
  among the β steps, the caption said β covers the rest. Why: instructiveness
  and checker (uncovered `t_act_case_inl`, `t_act_case_inr`). Checked against
  `head_step` constructors `t_act_let_unit`, `t_act_let_pair`,
  `t_act_case_inl`, `t_act_case_inr`.
- `sem-events`. Caption adds what $\tau$ and administrative events are, so
  $\tau$ is defined before the block uses it. Checked against `ev_tau`,
  `ev_admin`.
- `sem-props`. Lock-free caption names the run $r$, its events $l$ and the
  pending thread $t$. Old "a waiting thread later takes part in a step". Why:
  checker (var-before-intro), and the old text said "waiting" where
  `lock_free` says pending. Checked against `lock_free`, `lf_run`.

## Types and worlds

## Typing

## Semantic typing

## Theorems

## Examples

## Questions for the author

## Things the map still forgets

## Checker counts before and after

Before, at 1401e2d. `node check.js` on the converted map with the overlay and
extension of demo/, `--root v2`.

| Category | Before | After |
|---|---|---|
| errors | 19 | |
| name-missing | 13 | |
| name-elsewhere | 3 | |
| reason-missing | 3 | |
| warnings | 729 | |
| var-before-intro | 106 | |
| prose-in-formula | 66 | |
| rename-undeclared | 45 | |
| bare-word | 10 | |
| prose:every/any/all | 319 | |
| prose:metaphor | 175 | |
| prose:hedge | 6 | |
| prose:colon | 1 | |
| prose:pronoun ending | 1 | |
| info | 11 | |

gen.js before: 0 errors, no DF-LEAK, unused notes `O-Spawn.transfer` and
`fu.oneclock`. lint-map.py before: 163 metaphor, 319 every/any/all, 1 pronoun
ending, 0 elsewhere.
