# The relation map as a proof map

The author wants the explorer to become a skill that other proof developments can use
(2026-11-20). The base skill lives in `tools/proof-map` (`SKILL.md`, `FORMAT.md`), and since
phase C (2026-11-22) the relation map is one of its maps. This file records the requirements and
how to edit and check the map.

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
5. **Justified deviations.** A map may show a definition differently from the raw code
   (notation, merged clauses, a renamed operator, a planned change). Every such difference carries
   a reason in the JSON, why the display is faithful to the code or why it is planned, and the
   page shows the reason next to the item. The checker accepts a difference only with a reason.
6. **Modes as data.** The deadlock-free / lock-free switch and the "planned" tag are instances of
   generic mechanisms: a map declares its modes and which parts of a formula belong to which mode,
   and marks parts that are planned but not yet in the proof code.
7. **Design.** No scrollbar anywhere at any zoom level: formulas shrink or wrap, the hover panel
   never scrolls sideways. A smoother page, with text and formulas that can be selected and
   copied. A better theme than today's.
8. **Layers.** A shareable base skill describes the baseline: the JSON format, the page, the
   checks against the code, the writing and structure rules. Features for one paper, such as the
   deadlock-free / lock-free toggle, live in a private skill for that paper built on top of the
   base, through extension points of the page and of the JSON.
9. **Maintenance.** The skill keeps a map current: after a merge of the proof code it lists what
   changed, updates the generated parts, and reports what a human must rewrite.

## The map

| File | Role |
|---|---|
| `map.json` | The map, the only source. Sections, blocks, notes, examples in proof-map/1. |
| `ext/gv-check.js` | Private checker module: DF-LEAK, the author's prose rules, verdicts of examples. |
| `ext/gv-page.js` | Private page script: verdict badges on examples, the cursor report to `serve.sh`. |
| `index.html` | A link to `tools/proof-map/page/index.html`, which reads `map.json` next to it. |
| `serve.sh` | Serves this directory on localhost, reloads the page when the map changes. |
| `check.sh` | Every check in one command. |
| `BLOCKS.md` | Which blocks exist and in which order. |
| `attic/` | The retired generators `gen/*.js`, their last `data.js` and old page, and the one-time `migrate.js` and `compare.js` of phase C. Nothing reads them. |

The DF/LF switch is the `modes` mechanism of the base. Lock-free parts of a shared formula sit in
`\inmode{lf}{…}` (coloured), layout that belongs to them in `\inmodeplain{lf}{…}`, and a part only
the deadlock-free view shows in `\inmodeplain{df}{…}`. Prose takes `\inmode{lf}{…}` for lock-free
sentences. A block with `"modes": ["lf"]` is a lock-free block of its own, a row of a table with
`"modes": ["lf"]` a lock-free row. A block whose two views differ too much for markup has
`variants.df`.

## Editing the map

1. Edit `map.json` directly. `tools/proof-map/FORMAT.md` explains each field and the markup
   (`\sym{key}{…}` for a hover, `\inmode`, `\planned`, `[[block-id]]` links, tables).
2. Keep the reader-facing rules of `BLOCKS.md` and of part C of `tools/proof-map/SKILL.md`.
3. Run `docs/explorer/check.sh`. It must end with `total … ok`. Read the warnings of the steps you
   touched.
4. Look at the result with `docs/explorer/serve.sh`. Hover each new symbol once, and switch
   between DF and LF.
5. Screenshots: `THEMES=light tools/proof-map/shoot.sh docs/explorer/map.json OUT 1400 2400 1`
   (and zoom `2` for 200 %). `node tools/proof-map/test/page-test.js docs/explorer/map.json`
   checks for horizontal overflow from 320 to 2560 CSS pixels, hover, pin, links, filter and copy.

## The check

`docs/explorer/check.sh` runs `tools/proof-map/check.js` on `map.json` against `v2/` with the
extension, and prints one table.

| Step | What | Fails on |
|---|---|---|
| 1 schema | `map.json` against `tools/proof-map/schema.json`, the extension loads | any finding |
| 2 proof-map | Rocq names exist where cited, hovers have notes, links resolve, deviations have reasons, variables come before use, renamed symbols are declared | errors |
| 3 DF-LEAK | nothing of the lock-free view in a formula, caption, table or note a deadlock-free reader reaches | any finding |
| 4 writing | the prose rules of the base and of `ext/gv-check.js` (from `.claude/tools/lint-map.py`) | errors |
| 5 MathJax | every formula, table cell, signature, argument and `$…$` of prose renders in both modes | any finding, or mathjax-full missing |

The exit status is 1 when a step fails. Warnings never fail the check. `check.sh --list CATEGORY`
prints every finding of one category, such as `prose:every/any/all`. MathJax needs
`npm install --prefix tools/proof-map --no-save --no-package-lock mathjax-full@3.2.2` once,
into the gitignored `tools/proof-map/node_modules`.

The untracked helpers `.claude/tools/lint-map.py`, `.claude/tools/mj/check.js` and
`.claude/tools/shoot.sh` read the retired `data.js` and are superseded by `check.sh` and
`tools/proof-map/shoot.sh`.
