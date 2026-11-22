---
name: proof-map
description: Build, check and maintain an interactive web map of a Rocq development (definitions, inductive rules, theorems) from one JSON file. Use to create a map from proof code, to check a map against the code after a change, to convert an older map, or to write the captions and notes of a map. A private skill per paper extends it with its own modes, checks and page features.
---

# Proof maps

A proof map is one JSON file and one fixed page. The JSON holds sections, blocks of TeX, notes
behind every symbol, examples and the Rocq names each item shows. The page renders any such file
with MathJax, and `check.js` compares the file with the Rocq sources. Nothing in the page or the
checker knows a particular development.

| File | Role |
|---|---|
| `schema.json`, `FORMAT.md` | The format, normative and explained. |
| `page/index.html` | The page. Static, no build step, MathJax 3.2.2 from cdnjs. |
| `check.js` | The checker. Node, no dependencies, no network. |
| `lib/rocq-index.js` | Reads names and statements out of `.v` files. Also a command line lookup. |
| `serve.py` | Serves page and map on localhost, reloads on change. |
| `shoot.sh`, `test/page-test.js` | Screenshots, and a browser test of hover, pin, copy, filter and overflow. |
| `convert-explorer.js` | Converts the older explorer format. A template for other converters. |
| `demo/` | A converted map with a private extension, the worked example below. |

## A. Create a map from proof code

1. Index the code. `node lib/rocq-index.js <root>` counts what the tree defines, and
   `node lib/rocq-index.js <root> name …` prints the file, line and statement of each name.
2. Fix the story before writing TeX. A section is one stage of the development, such as syntax,
   semantics, typing, the relation and the theorems. Order the sections so that each one uses only
   what earlier sections define.
3. Write one block per definition or rule group, following the structure rules in part C. Give each
   block its `source`, the Rocq names it shows. Write the formula with `\sym{key}{…}` around every
   symbol a reader may not know, and a note per key.
4. Write the captions and notes last, following the writing rules in part C.
5. Run `node check.js map.json` until it reports no errors, and read the warnings.
6. Open the map with `python3 -I serve.py map.json`. Hover every symbol of a new block once.

A generated map follows the same steps with a script in place of the hand. The script emits the
JSON, and the checker treats generated and written maps alike. When an older map exists, write a
converter in the style of `convert-explorer.js`. It translates markup mechanically and writes
`REASON MISSING` wherever a deviation needs a human reason. Human decisions live in an overlay
file that the converter merges on every run (`--overlay demo/overlay.json`), so a reconversion
keeps them.

## B. Check a map against the code

`node check.js map.json [--root DIR] [--list [CATEGORY]] [--mathjax NODE_MODULES]` prints one line
per category with a count and the first findings. Errors make the exit status 1.

| Category | Severity | Fix |
|---|---|---|
| `schema` | error | Make the JSON match `schema.json`. |
| `file-missing`, `name-missing`, `name-elsewhere` | error | Cite the name where the code defines it, or record a `planned` deviation. |
| `unsourced` | error | Cite the definition, or add an `unsourced` deviation with a reason. |
| `note-missing` | error | Write the note for the key. |
| `dead-link`, `mode-unknown`, `dup-id` | error | Correct the id. |
| `reason-missing`, `planned-no-reason` | error | Write the reason the page will show. |
| `mathjax` | error | Fix the TeX. Needs `--mathjax` with a `node_modules` that holds `mathjax-full`. |
| `unhovered` | warning | Wrap the named symbol or relation in `\sym`. |
| `var-before-intro` | warning | Introduce the variable earlier, see part C. |
| `rename-undeclared` | warning | Use the Rocq name, or add a `renamed` deviation that says why the display differs. |
| `prose-in-formula`, `bare-word` | warning | Move the words into the caption, set names in `\mathsf`. |
| `statement-changed` | warning | Reread the Rocq statement, update the block, then stamp it. |
| `prose:*` | warning | Rewrite the sentence, see part C. |
| `note-unused`, `uncovered`, `unreviewed`, `external` | info | Drop the note, map the constructor, or stamp after a review. |

A block introduces the variables in its `introduces` list and the left sides of `::=` in its
formula. Its caption introduces each variable it sets alone in math, as in `$x$`, `$x, y$` or
`$i \in S$`. The checker reads blocks in section order, once per mode, and a binder
such as `\forall x` or `\lambda x.` introduces `x` inside its own formula.

`rocq-index.js` parses the sources and needs no compiled files. It finds inductive types,
constructors, records with their fields, definitions, fixpoints, lemmas, instances, axioms,
section variables and notations. Each name carries a fingerprint of its statement.
`node check.js map.json --stamp` records the current fingerprints as reviewed, and
`--stamp id1,id2` does so for some items only. Stamp only after a human compared the block with
the statement.

### Maintenance after a merge of the proof code

Run the checker on the merged tree. Three categories list what changed.

- `statement-changed` names each block whose Rocq statement differs from the reviewed one. A human
  rewrites the formula and stamps the new fingerprint.
- `name-missing` and `name-elsewhere` name each citation the merge broke, through a rename, a move
  or a deletion.
- `uncovered` names each new constructor of an inductive the map cites, such as a new typing rule.

A generated map regenerates its blocks, and the checker then reports the handwritten parts that
still need a person. Report the three lists to the author, who does the rewriting.

## C. Writing, ordering and structure

### Structure

1. A block holds one definition, one judgment or the rules of one construct, introduction and
   elimination together. Its title names that thing.
2. A helper used by one block lives in that block. A helper gets its own block only when several
   blocks use it and the paper gives it a name.
3. A mode that extends a definition extends it in place. Its premises, annotations and rows go
   into the same block, wrapped in `\inmode`, and the other modes hide these parts.
4. A block of one mode alone exists only for a notion without a counterpart in the other modes.
5. Theorems follow the proof. The theorem section opens with the chain of results, then the
   lemmas in the order of the proof.
6. An overview block may open a section and show how the blocks after it fit together. It cites
   the definitions it summarizes, or carries an `unsourced` deviation.
7. A block shows mathematics. Words go into the caption and the notes, never into `\text`. An
   overview that pairs each formula with a sentence uses a `table` of rows instead of a formula.

### Ordering

1. A section uses only what earlier sections and earlier blocks define. The checker enforces this
   for variables.
2. Inside a section, a definition comes before the rules that use it, and a rule before its
   lemmas.
3. Notes repeat nothing from captions. The caption says what the formula means, the note behind
   the title says why the block exists and what breaks without the block.

### Writing

1. Lead with the claim. A caption opens with what the formula states, never with background.
2. One idea per sentence, at most 35 words.
3. Name the definition and say what it does. A rule restricts, a relation relates, a function
   returns.
4. No colons, semicolons or dashes in running prose. Split the sentence.
5. Write `because`, never `since`, for a cause. State facts without hedges.
6. Use the standard term of the field. A private skill lists the coined words its project forbids.
7. Each field says something new. Drop a `why` that restates the caption.

The checker runs rules 2, 4 and 5 and the lists of the private skill. Stricter house rules, such
as banned metaphors or quantifiers, belong to the private skill as `proseRules`. A base rule that
does not fit a project goes into the `disableProse` list of its extension.

### Deviations

The display may differ from the raw code. Notation, merged clauses, a renamed operator, an
omitted argument and a planned change are all fine, each with a reason the reader sees. A reason
says why the display is faithful to the code, or what the plan is and where it is recorded. The
checker rejects a deviation without a reason and warns about renamed symbols without one.

A reason shared by many items is declared once under `deviationRules`. The rule
`{"kind": "renamed", "reason": "Constructors are shown by their surface keyword.", "appliesTo": "constructors"}`
covers each note that cites a constructor of an inductive type. A list of key patterns, such as
`{"keys": ["prim.*"]}`, covers notes by key. The page lists these rules next to the conventions.

## D. Extending the base in a private skill

A project keeps its own skill, say `.claude/skills/<paper>-map/SKILL.md`, that starts with "Builds
on proof-map" and adds the project's rules. The base never changes for one project. The private
skill extends it at four points.

| Extension point | How |
|---|---|
| Modes | Declare them under `modes` in the map. The page draws the switch, colours `\inmode` parts and tints blocks of one mode. |
| Free fields | Any `x-…` field on the map, a section, a block, a note or an example. The schema accepts it and the base ignores it. |
| Page hooks | A script listed under `extensions.page` calls `ProofMap.register({...})`. |
| Checker module | A module listed under `extensions.check` exports rules and a `check(ctx)` function. |

The page hooks are these. Each one returns HTML and receives the item and a context
`{map, mode, esc, prose, plainTeX, modes}`.

| Hook | Where its HTML goes |
|---|---|
| `css` | A string of CSS added to the page. |
| `blockTags(block, ctx)` | The header of a block, next to the tags. |
| `blockFooter(block, ctx)` | Under the caption and the deviations of a block. |
| `exampleHeader(example, ctx)` | Under the title of an example. |
| `noteRows(note, ctx)` | Extra rows of the note panel, as `[label, html]` pairs. |

The checker module may export these.

| Export | Effect |
|---|---|
| `proseRules` | Extra rules `{name, re, why, severity?}`. |
| `disableProse` | Names of base prose rules to switch off. |
| `proseSkip` | Exact texts the prose rules skip, such as a fixed phrase for definitions. |
| `operators` | More TeX commands that need a hover, such as `\Vdash`. |
| `categories` | Descriptions of the categories the module reports. |
| `check(ctx)` | Runs after the base checks. `ctx` holds the map, the Rocq index `idx`, the items with their `where`, the TeX helpers `tex`, the prose fields and `report(category, severity, where, message)`. |

### Worked example: a deadlock-free and a lock-free view

A session-types development proves deadlock freedom with one relation and lock freedom with a
richer one. The lock-free relation adds credits, costs, ticket needs and a guard to most rules.
Its map shows both views in one set of blocks. `demo/` holds the converted map and its extension.

1. The map declares two modes, `df` and `lf`, with their labels, short tags and colours. The
   default is `df`.
2. The lock-free additions inside shared rules sit in `\inmode{lf}{…}`. The deadlock-free reader
   never sees them, the lock-free reader sees them coloured. Layout that belongs to an addition
   uses `\inmodeplain{lf}{…}`, and a part only the deadlock-free view shows uses
   `\inmodeplain{df}{…}`.
3. A notion without a deadlock-free counterpart, such as fuel, is a block with `"modes": ["lf"]`.
   A rule whose two views differ too much for markup has `variants.df`.
4. The private checker module `demo/ext/gv-check.js` adds three checks the base cannot know. A
   formula or note a deadlock-free reader reaches must not mention credits, ticket needs or the
   guard. The author's strict prose rules (metaphors, quantifiers, `like`, pronoun endings) and the
   project's coined words apply to prose. The Rocq names behind the verdicts of examples must
   exist.
5. The private page script `demo/ext/gv-page.js` reads `x-gv-accepts` on examples and draws one
   badge per judgment, such as "statically typed, lock free at N = 3". The deadlock-free view
   shows only the deadlock-free verdicts.
6. The private skill states the project's structure rules in terms of these modes. Lock freedom
   extends a block in place, and a lock-free block of its own exists only for a notion without a
   deadlock-free counterpart.

Nothing of this lives in the base. A second project with a typed and an untyped view, or a
classical and a constructive one, declares its modes and writes its own module.
