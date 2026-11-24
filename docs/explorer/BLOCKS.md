# What gets a block

The map tells the story of the paper. Each section is one stage of it, and
each block is one thing the paper defines or states. `map.json` holds the
blocks in this order, and the text a reader sees first: section intros, block
captions, block title notes and example descriptions. The prose follows the
pl-paper-writing skill of sill-obs, and `check.sh` checks the mechanical rules
(see MAP-SKILL.md). Until phase C, `gen/layout.js` and `gen/prose.js` built
this, now in `attic/gen/`.

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
   deadlock-free counterpart: annotations and tickets, aging and capture,
   fuel and the lock-free process relation. After the judgment, its
   contexts and the side conditions, the typing section has one such block per
   device lock freedom adds (counters with credits and tickets, ranked
   worlds), each listing its operators with a clickable note and their
   meaning. They follow the judgment because they use its notation.
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
| Types and worlds | types (credits coloured), session types, duality, equivalence, heads, payloads, *annotations and tickets*, kinds, worlds (kind coloured), order, consistent worlds, extension |
| Typing | judgment, contexts, side conditions, *counters, credits and tickets*, *ranked worlds*, *aging*, unit/variables/ends, functions, products/sums/let, boxes, existentials, constants, actions and link, spawn, creation (E-New, E-New-Field), subtyping and structural rules, process typing |
| Semantic typing | reading guide, step costs, values, terms, obligations of term steps, readiness, processes, obligations of process steps, *relation and fuel side by side*, *fuel*, *fuel obligations*, *values in FV*, *the lock-free process relation*, semantic judgments |
| Theorems | how the results fit together, bind, composition, fundamental theorems, adequacy, soundness, *conservativity* |

Italic blocks exist only in the lock-free view.
