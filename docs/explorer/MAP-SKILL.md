# A proof-map skill (planned, not started)

The author wants the explorer to become a skill that other proof developments can use
(2026-11-20). A separate agent builds it later. This file records the requirements.

## Requirements

1. **Data apart from the page.** A map is JSON: sections, blocks, rules, notes, examples, mode
   switches. One fixed page renders any map. No project code in the page.
2. **Generated from, or checked against, the proof code.** Either the JSON is generated from the
   Rocq development (definitions, inductive rules, theorem statements), or a checker compares a
   hand-written JSON with it. Every cited Rocq name must exist, and every block must say which
   definition it shows.
3. **Rigour checks.** Every symbol in a formula has a hover. Every variable is introduced before it
   is used, in the block or in a block the reader has seen before. No prose inside formulas. The
   prose rules of the author (today `.claude/tools/lint-map.py`) run on every build.
4. **Cross-links.** Hovers, "used in" lists and links between blocks resolve, also across sections
   and after blocks are merged.
5. **Modes as data.** The deadlock-free / lock-free switch and the "planned" tag are instances of
   generic mechanisms: a map declares its modes and which parts of a formula belong to which mode,
   and marks parts that are planned but not yet in the proof code.
6. **Design.** No scrollbar anywhere at any zoom level: formulas shrink or wrap, the hover panel
   never scrolls sideways. A better theme than today's.
7. **Maintenance.** The skill keeps a map current: after a merge of the proof code it lists what
   changed, updates the generated parts, and reports what a human must rewrite.

## What exists today

- `gen/*.js` build `data.js` by hand-written generators, `gen/layout.js` merges and orders blocks,
  `gen/prose.js` holds the reader-facing text, `BLOCKS.md` the block rules.
- Checks: `gen/gen.js` (unhovered symbols, notes without signature, unused notes),
  `.claude/tools/mj/check.js` (MathJax renders every block in both modes),
  `.claude/tools/lint-map.py` (prose rules), `.claude/tools/shoot.sh` (screenshots of every
  section in both modes).
- Missing: a check that the formulas match the Rocq, a check for variables used before they are
  introduced, and JSON as the single source.
