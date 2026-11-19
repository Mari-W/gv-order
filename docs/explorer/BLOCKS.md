# What gets a block

The map tells the story of the paper. Each section is one stage of it, and
each block is one thing the paper defines or states. `gen/layout.js` applies
these rules to the fine-grained blocks the section files define, and
`gen/prose.js` holds the text a reader sees first: section intros, block
captions, block title notes and example descriptions. The prose follows the
pl-paper-writing skill of sill-obs, and `.claude/tools/lint-map.py` checks
the mechanical rules.

1. **One block per definition or rule group.** A block holds one definition
   (one relation, one judgment, one operation) or the rules of one construct,
   introduction and elimination together. Its title names that thing.
2. **Helpers live with their user.** A helper used by one block sits in that
   block. A helper gets a block of its own only when several blocks use it and
   the paper names it, such as heads or readiness.
3. **Lock freedom extends in place.** When lock freedom adds premises,
   annotations, rows or theorems to something deadlock freedom has, they go into
   the same block, coloured, and the deadlock-free view hides them.
4. **Own blocks only for new notions.** A lock-free block of its own (pink
   background, nothing coloured inside) exists only for a notion without a
   deadlock-free counterpart: annotations and ticket needs, aging and capture,
   the guard, fuel and the soup. The typing section opens with one such block
   per device lock freedom adds (credits, tickets, the guard, a well-founded
   world), each listing its operators with a clickable note and their meaning.
5. **Theorems follow the proof.** The theorem section opens with the chain of
   results, then the compatibility lemmas, the fundamental theorems, adequacy and
   soundness. Each lock-free result sits in the block of its deadlock-free
   counterpart. Conservativity has no counterpart and stands alone.
6. **Three overview blocks.** The reading guide opens semantic typing, the
   side-by-side table opens its lock-free part, and the proof chain opens the
   theorems. Each shows how the blocks after it fit together.
7. **Prose goes into captions and notes.** A block shows mathematics. Its
   caption says in words what it means, and its title note says why it is there
   and which blocks use it.

## The blocks

| Section | Blocks |
|---|---|
| Types and worlds | types (credits coloured), session types, duality, equivalence, heads, payloads, *annotations and ticket needs*, kinds, worlds, order, well-formed worlds, extension |
| Typing | *credits*, *tickets*, *the guard*, *a well-founded world*, judgment, contexts, side conditions, *aging and capture*, unit/variables/ends, functions, products/sums/let, boxes, existentials, constants, actions and link, spawn, creation, subtyping and structural rules, process typing, *the guard* |
| Semantic typing | reading guide, step costs, values, terms, obligations of term steps, readiness, processes, obligations of process steps, *relation and fuel side by side*, *fuel*, *fuel obligations*, *fueled values*, *the soup*, semantic judgments |
| Theorems | how the results fit together, bind, composition, fundamental theorems, adequacy, soundness, *conservativity* |

Italic blocks exist only in the lock-free view.
