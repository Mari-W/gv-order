# Paper plan, GV≺ skeleton

Branch paper-draft. Every formula, rule and example in the .tex comes from
docs/explorer/map.json through paper/tools/map2tex.py. Rerun `make -C paper gen`
after a map change. Paragraph slots are `% PAR:` comments, gaps are `% GAP:`.

## Build

- `make -C paper` runs map2tex.py, rocqrefs.py and latexmk.
- Skeleton today (figures, listings, theorems, headings, no prose).
  Body pages 1 to 12, about 10.5 pages of figure and listing material.
  References page 12. Appendix pages 13 to 44.
- Appendix parts. Map blocks A to F, pages 13 to 28. All 30 example listings G,
  pages 28 to 33. Index of notation H (note signatures), pages 33 to 44.

## Structure options for lock freedom

| option | layout | page estimate | trade-off |
|---|---|---|---|
| A (built) | §3 typing DF, §4 relation DF, §5 one LF section for the colour of all figures | 22.8 | DF story uninterrupted, LF insights cross typing and relation (adequacy measure = rank plus counter needs both), one forward pointer per figure |
| B | §3 typing DF then LF colour, §4 relation DF then LF colour | 23.3 | colour explained next to its figure, but fuel and the adequacy measure need both halves, so §3 LF part points forward, plus about 0.5 page of repeated LF motivation |

Recommendation A.

## Sections (option A)

| section | concepts | examples (body listing) | figures | map blocks | pages |
|---|---|---|---|---|---|
| 1 Intro | DF compositional, trees, priorities, points and orders, semantic typing, LF second level, contributions | ex-flag (listing, three facts) | – | sem-props, th-compose, th-adeq | 2.0 |
| 2 Language | ends, constants, processes, semantics pointer, DF and LF definitions, points, payload points, worlds, order, consistency, join | ex-close, ex-cycle | fig:syntax, fig:props, fig:worlds, fig:points-example (TikZ) | syn-*, sem-props, w-* | 3.0 |
| 3 Typing | types, context-free session types, arrows u and l, boxes, existentials, judgment with future F, fact theory, side conditions, rules, creation, recursion, process typing | ex-bit, ex-cs, ex-milner, ex-forkjoin (cited: ex-copycat, ex-factory, ex-gennew, ex-between, ex-ring3, ex-shared, ex-point-reuse, ex-sinst) | fig:types, fig:judgment, fig:typing-core, fig:typing-orders, fig:process-typing, lem:two-closes | ty-*, t-*, r-*, p-typing, t-lemmas | 5.5 |
| 4 Relation | ownership, V, E, readiness, costs, obligations, bind, P, semantic judgments, semantic P-Term and P-Connect, fundamental theorems, adequacy, soundness | ex-flag (back reference), cited ex-tree, ex-flagpair, ex-ring | fig:value-rel, fig:term-rel, fig:proc-rel, fig:composition-example (optional), thm:compose, thm:fundamental-terms, thm:fundamental-proc, thm:adequacy, thm:soundness, lem:bind | v-rel, e-rel, rd, ct-costs, e-obl, e-bind, p-rel, sj-all, th-* | 5.0 |
| 5 Lock freedom | orders say on whom, counters how long, annotations N a m c, aging, conservativity, ranked worlds, κ_L, fuel, LF process relation, adequacy measure, EM and FC | rx-postpone, rx-delegate (cited: rx-relink, ex-controller, ex-link, ex-guard-neg, ex-guard-pos, rx-chain, ex-forwarder, ex-cs-split) | fig:lf-counters, fig:aging, fig:ranked, fig:fuel, fig:soup, thm:conserv, plus the colour of every earlier figure | ty-ann, t-lf-counters, t-agecap, t-lf-wf, fu, fu-obls, soup, th-conserv | 3.5 |
| 6 Algorithmic | placeholder | – | – | – | 0.3 |
| 7 Mechanization insights | one world per arm unsound, point reuse, contractivity, two fixed points, one world notion, transfinite indices, assumptions | ex-branch-ext, ex-point-reuse, ex-sinst (cited) | – | fu-vs, w-world, sr-ord | 0.7 |
| 8 Related work | subsumption by example per system | ex-milner (PCP), rest GAP | tab:subsume | – | 2.5 |
| 9 Conclusion | summary, future work | – | – | – | 0.3 |
| total | | | | | 22.8 |

Optional. fig:composition-example (TikZ, two components, joined world, dead-arm
fact as the cycle) costs about 0.35 page. Cut first if the body runs long.
Further cuts in order: ct-costs to the appendix (0.3), fig:aging into a line of
fig:lf-counters (0.25), ex-milner listing to the appendix with a back reference
from §8 (0.3).

## Figures, who explains which part

| figure | map blocks | DF part explained in | LF colour explained in |
|---|---|---|---|
| fig:syntax | syn-ends, syn-prims, syn-terms, syn-values, syn-let, syn-procs | §2.1 | none |
| fig:props | sem-props | §2.1 | §5.1 |
| fig:worlds | syn-labels, syn-points, syn-moves, w-world, w-order, w-wf, w-ext | §2.2, join in §3.5 | §5.3 |
| fig:points-example | ex-cycle, ex-ring (TikZ) | §2.2 | none |
| fig:types | ty-grammar, ty-session, ty-heads | §3.1 | §5.2 |
| fig:judgment | t-judgment, t-contexts, t-side | §3.2 | §5.2 |
| fig:typing-core | E-Abs, E-App, E-Case, E-Send, E-Close, E-Link | §3.3 | §5.2 |
| fig:typing-orders | r-new (E-New, acyc_new, new_ok), E-Box, E-Force, E-Open | §3.4 | §5.2 (tickets, costs), §5.3 (new_ok_N) |
| fig:process-typing | p-typing | §3.5 | §5.2 (N, η), §5.3 (ranked) |
| lem:two-closes | t-lemmas | §3.5 | none |
| fig:value-rel | V-Sess, V-Arrow, V-Box | §4.1 | §5.4 (κ_β) |
| fig:term-rel | e-rel, rd, ct-costs, O-New, O-Send | §4.2, process readiness §4.3 | §5.4 (κ_L) |
| fig:proc-rel | p-rel, sj-all | §4.3 | §5.4 (strict worlds, lock-free judgment) |
| fig:composition-example | ex-flag (TikZ), optional | §4.4 | none |
| theorems of §4.4 and §4.5 | th-compose, th-terms, th-fund-proc, th-adeq, th-sound | §4.4, §4.5 | §5.4 |
| fig:lf-counters, fig:aging, thm:conserv | ty-ann, t-lf-counters, t-agecap, th-conserv | LF only | §5.2 |
| fig:ranked | t-lf-wf | LF only | §5.3 |
| fig:fuel, fig:soup | fu, F-Force, F-Send, soup | LF only | §5.4 |

## Rule selection in the body

| rule | reason |
|---|---|
| E-Abs, E-App | upper point u and lower point l, the future F, u ≺ F |
| E-Case | both arms in one world, the reason ex-flag fails statically and ex-bit types |
| E-Send | point x ≺ F, payload above x, LF payload credit |
| E-Close | smallest action rule, ex-cycle |
| E-Link | dual types at dual points, LF tickets premise |
| E-New with acyc_new | the only source of new facts besides boxes, LF new_ok_N and ticket split |
| E-Box, E-Force | recursion with infinite constraints, ex-cs |
| E-Open | conservativity, needed for the ex-flag rejection |
| P-Term, P-Connect, P-Connect^n | composition, joined world |
| V-Sess, V-Arrow, V-Box | exact ownership, world extension, constraint instances |
| e-rel, rd | readiness, the core of deadlock freedom |
| ct-costs | κ_DF next to κ_L, the LF relation reuses E |
| O-New, O-Send | world growth at creation, ownership split at send |
| p-rel, sj-all | process relation and judgments for thm:compose |
| fu, F-Force, F-Send | fuel, the one new relation for LF |
| soup | LF process relation = E at κ_L plus fuel |

In the appendix only. E-Unit, E-Var, E-Chan, E-Pair, E-LetP, E-LetU, E-Inj,
E-Recv, E-Select, E-Branch, E-Spawn, E-Pack, t-consts, t-subs, V-Unit, V-Prod,
V-Sum, V-Ex, the other O and Q rules, p-obls, e-bind (stated in §4.2), the
other F rules, fv, fu-vs, sr-reading, sr-ord, semantics blocks.

## GAP list

1. Title of the paper.
2. sem-props shows the deadlocking reversed cycle only in its breaks text. No map example with a listing for a deadlocked process.
3. fig:points-example panel (b). The box constraint Cr of ex-ring is not in the map. GrowRing.v rg_F has five facts per pair, so the panel has no fact arrows yet.
4. No deadlock-free map example sends an end and states all its facts, the ideal single example for payload points.
5. No map program uses sequencing S.S of context-free session types (ex-sinst only in types).
6. No map example for "counters alone admit a cyclic wait" (§5.1).
7. Algorithmic typing, undecided, placeholder §6.
8. Size of the development and build numbers are not in the map (§7).
9. Recorded map and Rocq differences (map-faithfulness.md) have no place yet (§7 footnote or appendix table).
10. Related work. Only PCP and ex-milner is confirmed by .claude/notes (Dardha and Gay Example 1). GV, PGV, Padovani 2014, Kobayashi 2006, Padovani and Novara, Thiemann and Vasconcelos, Mordido and Pérez, APCP have no confirmed map example. The old notes cover pre-v2 programs.
11. The authors' previous GV paper (logical relation for deadlock freedom) has no entry in main.bib.
12. Predicates defined only in note prose (conn, sth, pterm_N, sinsts, pfree). The appendix index gives their signatures only.

## Open questions for the author

1. Option A or B for the lock-free split.
2. Points example. ex-cycle (complete facts, no payload) or ex-ring (payload, facts missing from the map) or a new map example for payload points.
3. Keep fig:composition-example (0.35 page).
4. ex-flag in the intro as a full example or only a forward reference to §4.4.
5. Appendix index of notation (11 pages). Keep, shorten to the symbols the body uses, or drop.
6. Combined colour form for replacements. `cons / ranked` via \lfalt, or a different marker.
7. Conclusion after related work, or related work as the very last section.
8. Which related systems get a row in tab:subsume once examples are confirmed.
