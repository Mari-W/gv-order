# Map audit, 2026-11-22

Branch redesign-map, from redesign at 1401e2d. The audit checks every block,
caption, note and example of docs/explorer against the Rocq of v2/ on this
branch, against the map deltas of the reports in docs/redesign/pending.md,
and against the proof-map checker of branch mapkit. Measured boxes are left
out (branch redesign-mbox).

Each entry gives the block or note id, the old and new text or formula, the
reason, and the Rocq name it was checked against. Sections follow page order.

## Syntax

## Semantics

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
