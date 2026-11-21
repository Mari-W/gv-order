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
| `syntax` | no | `keywords` and `comment` delimiters for example code, such as `["(* *)", "--"]`. |
| `modes` | no | The views of the map, see below. |
| `conventions` | no | Symbols fixed for the whole map, `{symbol, meaning}`. They count as introduced before the first block. |
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
| `formula` | TeX of the block, with the markup below. |
| `variants` | A whole formula for one mode, used instead of `formula` in that mode. |
| `caption` | What the formula says, in words. The reader sees it under the formula. |
| `why`, `breaks`, `example` | The note behind the title. Why the block exists, what fails without it, an instance. |
| `source` | The Rocq definitions the block shows, as `{file, names, qualifier?, reviewed?}`. Required. An empty list needs an `unsourced` or `planned` deviation. |
| `usedIn` | Ids of the blocks that use this one. The page lists them as links. |
| `introduces` | Metavariables the block introduces beyond what the checker infers. |
| `modes` | The modes that show the block. Absent means all. |
| `deviations` | Where the display differs from the code, each with a reason. |

A note explains one hover key. Its fields are `title`, `meaning`, `why`, `breaks`, `example`,
`signature` (TeX), `args` (`{name, meaning, modes?}`), `source`, `usedIn` and `deviations`. The
page adds the blocks whose formulas use the key.

An example has `id`, `title`, `lead`, `code`, `meaning`, `modes`, `source` and `deviations`.

## Formula markup

| Markup | Effect |
|---|---|
| `\sym{key}{X}` | X is a hover target with the note `key`. Targets nest, the innermost wins. |
| `\inmode{m1,m2}{X}` | X shows in the listed modes only, in the colour of the mode. |
| `\inmodeplain{m}{X}` | X shows in the listed modes only, uncoloured. Use it for layout such as `\\` or `\quad` that belongs to a coloured part. |
| `\planned{X}` | X is not yet in the proof code. The page dims it. The item needs a `planned` deviation. |

Everything else is plain MathJax TeX. Copying a formula yields the TeX of the current mode
without this markup.

## Prose markup

Prose fields take `$math$`, `` `code` ``, `[[block-id]]` and `[[block-id|label]]` links, and
`\inmode{m}{…}` for words that belong to one mode. A link to a section id works too.

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
