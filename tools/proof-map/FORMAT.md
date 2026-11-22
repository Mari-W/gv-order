# The proof-map/1 format

A map is one JSON file. `schema.json` defines the format, and `check.js` validates each map
against that schema. This page explains the fields and the two small markup languages, one for formulas
and one for prose.

## Top level

| Field | Required | Meaning |
|---|---|---|
| `format` | yes | Always `"proof-map/1"`. |
| `title`, `subtitle` | title | Shown in the header and the browser tab. |
| `source` | no | `root` of the Rocq tree, relative to the map file, and optionally the `revision` last checked. |
| `tex.macros` | no | MathJax macros, `"name": "body"` or `"name": ["body", n]` for `n` arguments. |
| `syntax` | no | `keywords` and `comment` delimiters for example code, such as `["(* *)", "--"]`, the `operators` characters, and `constructors: true` to mark capitalised names. |
| `modes` | no | The views of the map, see below. |
| `conventions` | no | Symbols fixed for the whole map, `{symbol, meaning}`. The symbol may list several letters, such as `i, j`. They count as introduced before the first block. |
| `deviationRules` | no | Deviations declared once, `{kind, reason, appliesTo}`, see Deviations. |
| `sections` | yes | The stages of the story, in reading order. |
| `notes` | yes | One note per hover key. |
| `examples` | no | Programs with what the development proves about them. |
| `extensions` | no | `page` scripts and `check` modules of a private skill, relative to the map file. |
| `x-…` | no | Free fields for extensions, allowed on the map, sections, blocks, notes and examples. |

## Sections, blocks, notes, examples

A section has an `id`, a `title`, an `intro` and its `blocks`.

A block shows one definition or one rule group.

| Field | Meaning |
|---|---|
| `id`, `title` | The id is unique across sections, blocks and examples. |
| `formula` | TeX of the block, with the markup below. A block has a `formula` or a `table`. |
| `table` | An overview that pairs formulas with sentences, see Tables below. |
| `variants` | A whole formula for one mode, used instead of `formula` in that mode. |
| `caption` | What the formula says, in words. The reader sees it under the formula. |
| `why`, `breaks`, `example` | The note behind the title. Why the block exists, what fails without it, an instance. |
| `source` | The Rocq definitions the block shows, as `{file, names, qualifier?, reviewed?}`. Required. An empty list needs an `unsourced` or `planned` deviation. |
| `usedIn` | Ids of the blocks and examples that use this one. The page lists them under Used in, and the checker wants each of them to reference this block inline, see Cross-references. |
| `introduces` | Metavariables the block introduces beyond what the checker infers. |
| `modes` | The modes that show the block. Absent means all. |
| `deviations` | Where the display differs from the code, each with a reason. |

A note explains one hover key. Its fields are `title`, `meaning`, `why`, `breaks`, `example`,
`signature` (TeX), `args` (`{name, meaning, modes?}`), `source`, `usedIn`, `def` and `deviations`.
`def` names the block that defines the symbol, see Cross-references. The page adds the defining
block under Defined in and the other blocks whose formulas use the key under Used in.

An example has `id`, `title`, `lead`, `code`, `meaning`, `modes`, `source` and `deviations`.

## Formula markup

| Markup | Effect |
|---|---|
| `\sym{key}{X}` | X is a hover target with the note `key`. Targets nest, the innermost wins. A click opens the block that defines `key`. |
| `\inmode{m1,m2}{X}` | X shows in the listed modes only, in the colour of the mode. |
| `\inmodeplain{m}{X}` | X shows in the listed modes only, uncoloured. Use it for layout such as `\\` or `\quad` that belongs to a coloured part. |
| `\planned{X}` | X is not yet in the proof code. The page dims it. The item needs a `planned` deviation. |

Everything else is plain MathJax TeX. Copying a formula yields the TeX of the current mode
without this markup.

## Tables

A table keeps the words of an overview out of its formulas. Its columns line up across rows.

| Field | Meaning |
|---|---|
| `rows` | Each row has an optional `label` (prose) with an optional `labelKey` (a note), and its cells. |
| `rows[].cells` | Cells `{formula}` or `{text}`, in column order. The last cell of a row spans the columns left over. `{text: ""}` leaves a cell empty. |
| `rows[].formula`, `rows[].text` | Short form of `cells: [{formula}, {text}]`. |
| `rows[].modes` | The modes that show the row. The row takes the colour of its mode. |
| `header` | Column heads (prose), the label column first when the table has one. |
| `align` | One letter `l`, `c` or `r` per cell column, as in a TeX array. |

A column that holds a sentence takes the room left over, a formula column its natural width. On a
narrow screen the cells stack, each under its column head.

## Prose markup

Prose fields take `$math$`, `` `code` ``, `[[block-id]]` and `[[block-id|label]]` links, and
`\inmode{m}{…}` for words that belong to one mode. A link to a section id works too. Math in prose may hover a note with `\sym{key}{…}`, as in a table cell that reads `$\sym{sj.term}{\vDash}$ and the process relation`.

## Cross-references

Inline references are the primary references of a map. A block refers to what it builds on in its
own text, in two ways.

- A `[[block-id]]` or `[[block-id|label]]` link in the caption, `why`, `breaks`, `example`, a table
  cell or a deviation reason. The page draws it as a link with a thin solid underline.
- A `\sym{key}{…}` target in a formula or in prose math. A click on it opens the block that
  defines `key`. Every symbol in a formula that some block defines carries `\sym`.

The defining block of a note is its `def`. Without `def` it is the first block in reading order
whose formula or table hovers the key in the current mode, and else the first in any mode.
`"def": false` says that no block defines the symbol. Set `def` only where the first use is not
the definition, such as a symbol an overview shows before its block.

The page shows what responds to the pointer. Each glyph of a formula target carries a hairline
under it, drawn once for the innermost target that owns the glyph, so nested targets never stack
lines. The line is dotted when the target only shows a note, and solid when a click also opens a
block elsewhere. Under the cursor the innermost target gets a filled box and the targets around it
a thin outline. A table label with a note has a dotted underline. A click on a symbol pins its
note and opens the defining block, and Back returns. Shift-click or Alt-click pins without
moving, and a click inside the defining block pins only. Escape unpins.

The note panel keeps an index under Used in, with the blocks that list the item in `usedIn` and
the blocks whose formulas hover its key. The index helps a reader find uses. The text itself must
still carry the references. The checker warns with `xref-missing` when block A lists B in `usedIn`
and the text of B neither links `[[A]]` nor hovers a symbol whose defining block is A. The message
names B, the block A, and up to four keys A defines.

## Deviations

A deviation records a place where the display differs from the raw code, or shows something
the code lacks.

```json
{ "kind": "renamed", "reason": "The paper writes heads where the Rocq writes hbot.", "names": ["hbot"] }
```

`kind` is one of `notation`, `merged`, `renamed`, `simplified`, `omitted`, `planned`,
`unsourced` and `other`. `reason` is mandatory. A converter that cannot infer one writes
`REASON MISSING`, which the page shows in red and the checker rejects. `part` names the part of
the formula concerned, `names` the Rocq names, `modes` the modes the deviation applies to.

A reason shared by many items is declared once under `deviationRules`. `appliesTo` is
`"constructors"`, for notes that cite a constructor of an inductive type, or `{"keys": [...]}`
with patterns where `*` matches any text. The checker accepts the items a rule covers.

The page shows every reason under its block and in its note. A tag in the block header names the
kinds.

## Modes

`modes` declares the views. One switch in the header picks a mode, and a block whose formula
differs between modes gets its own small switch.

```json
"modes": { "label": "Instance", "default": "base",
  "options": [ { "id": "base", "label": "Base", "short": "B" },
               { "id": "ext", "label": "Extended", "short": "E", "color": { "light": "#7b4d8f", "dark": "#c6a2dc" } } ] }
```

A part of a formula, a block, a note argument or an example belongs to a mode through
`\inmode`, `modes` or `variants`. A block shown in one mode only gets a tinted background and a
tag.

## Loading

The page reads the map named by `?map=URL`, by default `map.json` in the page directory. Over `file://` Chrome needs
`--allow-file-access-from-files`, otherwise the page tries a sibling `.js` file that sets
`window.PROOF_MAP` and then offers a file picker. `serve.py` serves the page and the map on
localhost and reloads the page when either changes. `?mode=ID` picks a mode, `?note=KEY` pins a
note and `#section/block` opens a block.
