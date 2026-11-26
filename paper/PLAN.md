# Paper plan, GV≺ skeleton

Branch paper-draft. The body figures are set by hand in paper/figures/*.tex
from the content of docs/explorer/map.json. The definitions and theorems of
the body are restated in paper form in the section files. The appendix, the
example listings and the rule macros come from the map through
paper/tools/map2tex.py. Rerun `make -C paper gen` after a map change, then
check the body figures against the changed blocks by hand. Paragraph slots are
`% PAR:` comments, gaps are `% GAP:`.

## Build

- `make -C paper` runs map2tex.py, rocqrefs.py and latexmk. No undefined
  references, no overfull boxes.
- Skeleton today (figures, listings, definitions, theorems, headings, no prose).
  32 pages. Body pages 1 to 10, of which about 9 pages are figures, listings,
  definitions and theorems. References pages 10 and 11. Appendix pages 12 to 32.
- Appendix parts. Map blocks A to F, pages 12 to 27, each block a numbered item
  (A.1, A.2, ...) that the body references. All 30 example listings G, pages
  27 to 32. The index of notation is gone, the symbol table below replaces it.
- `\raggedbottom` in main.tex only for the skeleton. Remove it once the
  paragraphs fill the pages.
- Previews of three pages in paper/preview/.

## Look

- One scheme for the lock-free parts. A light shaded background (`\lf`,
  `\lfadd`, colour lfbg) behind each lock-free part of a formula, no change of
  text colour. It stays visible in greyscale. In running text of the appendix,
  where a box cannot break, the lock-free parts keep the accent colour lfcolor.
- Term keywords in sans serif in one quiet blue (kwcolor), in formulas
  (`\kw`) and in listings. Types, points and judgments stay black. Comments of
  listings in grey.
- Listings. map2tex.py highlights the keywords of `syntax.keywords` of the map
  and the comments (`--`, `(* *)`), into a fancyvrb Verbatim with
  commandchars. Each listing is a minipage, so its head never stays behind.
- Rule figures. A header per judgment form (name, rule, boxed form), mathpartir
  rules with names in small caps above, one size (`\small`), a thin rule at the
  bottom.
- Floats. flafter keeps every figure after its place in the text, and a
  `\FloatBarrier` ends every section file. Figures are `[tb]` (rule figures
  `[tbp]`) and come right after the first slot of the subsection that
  introduces them.
- Pictures. Threads as grey boxes, ends as black dots labelled with their
  points, facts as arrows in the keyword colour, channels as dotted lines, the
  fact labels below the picture.

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
| 2 Language | ends, constants, processes, semantics pointer, DF and LF definitions, points, payload points, worlds, order, consistency, join | ex-close, ex-cycle | fig:syntax, def:df, fig:worlds, fig:points-example (TikZ) | syn-*, sem-props, w-* | 3.0 |
| 3 Typing | types, context-free session types, arrows u and l, boxes, existentials, judgment with future F, fact theory, side conditions, rules, creation, recursion, process typing | ex-bit, ex-cs, ex-milner, ex-forkjoin (cited: ex-copycat, ex-factory, ex-gennew, ex-between, ex-ring3, ex-shared, ex-point-reuse, ex-sinst) | fig:types, def:judgment, fig:typing-core, fig:typing-orders, def:creation, fig:process-typing, lem:two-closes | ty-*, t-*, r-*, p-typing, t-lemmas | 5.5 |
| 4 Relation | ownership, V, E, readiness, costs, obligations, bind, P, semantic judgments, semantic P-Term and P-Connect, fundamental theorems, adequacy, soundness | ex-flag (back reference), cited ex-tree, ex-flagpair, ex-ring | def:value-rel, def:readiness, def:term-rel, def:obligations, def:proc-rel, def:sem-judgments, fig:composition-example (optional), thm:compose, thm:fundamental-terms, thm:fundamental-proc, thm:adequacy, thm:soundness, lem:bind | v-rel, e-rel, rd, ct-costs, e-obl, e-bind, p-rel, sj-all, th-* | 5.0 |
| 5 Lock freedom | orders say on whom, counters how long, annotations N a m c, aging, conservativity, ranked worlds, κ_L, fuel, LF process relation, adequacy measure, EM and FC | rx-postpone, rx-delegate (cited: rx-relink, ex-controller, ex-link, ex-guard-neg, ex-guard-pos, rx-chain, ex-forwarder, ex-cs-split) | def:lf, fig:lf-counters, fig:aging, thm:conserv, def:ranked, def:fuel, def:lf-rel, def:lf-judgment, thm:lf-compose, thm:lf-fundamental, thm:lf-soundness, plus the shading of every earlier figure | ty-ann, t-lf-counters, t-agecap, t-lf-wf, fu, fu-obls, soup, th-conserv | 3.5 |
| 6 Algorithmic | placeholder | – | – | – | 0.3 |
| 7 Mechanization insights | one world per arm unsound, point reuse, contractivity, two fixed points, one world notion, transfinite indices, assumptions | ex-branch-ext, ex-point-reuse, ex-sinst (cited) | – | fu-vs, w-world, sr-ord | 0.7 |
| 8 Related work | subsumption by example per system | ex-milner (PCP), rest GAP | tab:subsume | – | 2.5 |
| 9 Conclusion | summary, future work | – | – | – | 0.3 |
| total | | | | | 22.8 |

Optional. fig:composition-example (TikZ, two components, joined world, dead-arm
fact as the cycle) costs about 0.35 page. Cut first if the body runs long.
Further cuts, in this order (ct-costs is in the appendix already). fig:aging into a line of
fig:lf-counters (0.25), ex-milner listing to the appendix with a back reference
from §8 (0.3).

## Body figures

| figure | file | section | content (map blocks) |
|---|---|---|---|
| fig:syntax | figures/syntax.tex | 2.1 | ends, constants, terms, values, processes, derived let (syn-ends, syn-prims, syn-terms, syn-values, syn-let, syn-procs) |
| fig:worlds | figures/worlds.tex | 2.2 | points, moves, worlds, order, consistency, extension, growth, join (syn-labels, syn-points, syn-moves, w-world, w-order, w-wf, w-ext) |
| fig:points-example | figures/points-example.tex | 2.2 | (a) points and facts of ex-cycle, (b) a payload end arriving at x.0 |
| fig:types | figures/types.tex | 3.1 | types, session types, constraints, bounds, active points, payload instantiation (ty-grammar, ty-session, ty-heads, ty-payload) |
| fig:typing-core | figures/typing-core.tex | 3.3 | E-Abs, E-App, E-Case, E-Send, E-Close, E-Link |
| fig:typing-orders | figures/typing-orders.tex | 3.4 | E-New, E-New-Field, E-Box, E-Force, E-Open |
| fig:process-typing | figures/process-typing.tex | 3.5 | P-Term, P-Connect |
| fig:composition-example | figures/composition-example.tex | 4.4 | joined world of ex-flag, the cycle through the arm that never runs (optional) |
| fig:lf-counters | figures/lf-counters.tex | 5.2 | table of the lock-free annotations (ty-ann, t-lf-counters) |
| fig:aging | figures/aging.tex | 5.2 | Age-Credit, Age-Idle, Age-Arr, Age-Free (t-agecap) |
| tab:subsume | 8-related-work.tex | 8 | programs typable by other systems and by us |

Definitions and theorems that replace the former formula figures.

| label | section | content (map blocks) |
|---|---|---|
| def:df | 2.1 | terminated, deadlock free (sem-props) |
| def:judgment | 3.2 | judgment, contexts, order judgment, futures, side conditions, unl, subtyping (t-judgment, t-contexts, t-side) |
| def:creation | 3.4 | tree, the order of a new tree, acyc, conserv (r-new, r-ex) |
| lem:two-closes | 3.5 | first lemma of t-lemmas |
| def:value-rel | 4.1 | V at ends, closures, boxes, existentials (v-rel) |
| def:readiness | 4.2 | readiness of terms and processes (rd) |
| def:term-rel | 4.2 | E, stop, ready, step, costs (e-rel, ct-costs) |
| def:obligations | 4.2 | obligations of beta, new, send, recv (e-obl) |
| lem:bind | 4.2 | e-bind |
| def:proc-rel | 4.3 | P (p-rel, p-obls) |
| def:sem-judgments | 4.3 | term and process judgments (sj-all) |
| thm:compose | 4.4 | semantic P-Term and P-Connect (th-compose) |
| thm:fundamental-terms, thm:fundamental-proc, thm:adequacy, thm:soundness | 4.5 | th-terms, th-fund-proc, th-adeq, th-sound |
| def:lf | 5.1 | lock freedom (sem-props) |
| thm:conserv | 5.2 | th-conserv |
| def:ranked | 5.3 | ranked worlds, rankable (t-lf-wf, w-wf, r-new) |
| def:fuel | 5.4 | fuel and fuel obligations (fu, fu-obls, fv) |
| def:lf-rel | 5.4 | lock-free process relation (soup) |
| def:lf-judgment | 5.4 | lock-free judgment (sj-all) |
| thm:lf-compose, thm:lf-fundamental, thm:lf-soundness | 5.4 | th-compose, th-terms, th-fund-proc, th-adeq, th-sound (lock-free parts) |

## Body or appendix, item by item

An item in the appendix that the body states in words is referenced from the
body (caption or definition). Items marked "slot" are glossed by a `% PAR:`
slot whose `figure/rule` field names the appendix label.

| item | place | body gloss and reference |
|---|---|---|
| ends, constants, terms, values, processes, derived let | body, fig:syntax | |
| configurations q, erase | appendix A.7 | slot (processes, instrumented configurations) |
| fends, fchans | appendix A.6 | def:value-rel, "the set of ends in e" |
| link substitution csub | appendix A.11 | none needed |
| labels, head steps, frames, process steps, events | appendix B.1 to B.5 | fig:syntax caption, B.2 and B.4 |
| deadlock freedom | body, def:df | |
| no internal divergence, maximal, weakly fair runs | appendix B.6 | def:lf, B.6 |
| points, moves, worlds, order, cons, extension, growth, join | body, fig:worlds | |
| world_wf | absorbed | a world has its facts between its own points (fig:worlds) |
| restriction and the join lemma | appendix C.12 | fig:worlds caption |
| types, session types, bounds, ap, payload instantiation | body, fig:types | |
| duality, equivalence, contractivity, unfold | appendix C.2 to C.4 | fig:types caption, "as usual" in the slot |
| pscoped | appendix C.6 | convention, payloads mention only their own point variables (slot) |
| kinds tfree, unlimited | appendix C.8 | in words in rules ("holds no end", "no box type"), unl in def:judgment |
| annotations and tickets | body, fig:lf-counters | |
| judgment, futures, side conditions | body, def:judgment | |
| Ord-World, Ord-Fact, Ord-Trans | appendix D.2 | def:judgment, one sentence and D.2 |
| aging | body, fig:aging | context aging asks a <= m, slot |
| E-Unit, E-Var, E-Chan | appendix D.7 | fig:typing-core caption |
| E-Abs, E-App | body | |
| E-Pair, E-LetP, E-LetU, E-Inj | appendix D.9 | slot, fig:typing-core caption |
| E-Case | body | |
| E-Box, E-Force | body | |
| E-Pack | appendix D.11 | slot, fig:typing-core caption |
| E-Open | body | |
| types of constants | appendix D.12 | fig:typing-core caption |
| E-Send, E-Close, E-Link | body | |
| E-Recv, E-Select, E-Branch | appendix D.13 | slot, fig:typing-core caption |
| E-Spawn | appendix D.14 | slot |
| E-New, E-New-Field, acyc, conserv | body, fig:typing-orders, def:creation | |
| new_ok_N, gen_new | body as the shaded premise rankable, def:ranked | D.15 |
| subtyping and structural rules | appendix D.16 | def:judgment ("subtyping", D.16) |
| two static lemmas | body (first), appendix D.17 (second) | slot for the instantiation lemma |
| P-Term, P-Connect | body | |
| P-Connect^n | appendix D.18 | slot |
| sr-reading | appendix E.1 | slot |
| ordinal indices | appendix E.2 | def:value-rel |
| step costs | appendix E.3 | def:term-rel, def:lf-rel |
| V at ends, closures, boxes, existentials | body, def:value-rel | |
| V at unit, pairs, sums | appendix E.4 | def:value-rel |
| E, readiness | body | |
| obligations of beta, new, send, recv | body, def:obligations | |
| obligations of spawn, close, select, branch, link | appendix E.6 | def:obligations |
| bind lemma | body, lem:bind | evaluation contexts B.3 |
| P | body, def:proc-rel | |
| process obligations | appendix E.10 | def:proc-rel |
| fu-vs | appendix E.11 | slot |
| fuel | body, def:fuel | |
| fuel obligations | appendix E.13 | def:fuel, in words |
| values with fuel | appendix E.14 | def:fuel |
| lock-free process relation | body, def:lf-rel | wa in words, E.15 |
| semantic judgments, grounding G, den | body, def:sem-judgments | E.16 |
| theorems F.1 to F.6 | body, restated | |

## Symbols in reading order

| symbol | first defined | where |
|---|---|---|
| o, c^+, c^-, dual end | fig:syntax | 2.1 |
| k, e, v, values | fig:syntax | 2.1 |
| p = (C, E) | fig:syntax | 2.1 |
| let a = e1 in e2 | fig:syntax | 2.1 |
| steps, reachability | appendix B, caption of fig:syntax | 2.1 |
| terminated, deadlock-free | def:df | 2.1 |
| b, rho, iota, x^+, x.kappa, dual point | fig:worlds | 2.2 |
| where an end moves | fig:worlds | 2.2 |
| W, prec_A, Point_A, prec_W, tc, cons, extension, growth, join | fig:worlds | 2.2 |
| T, S, C, S_x, arrows with u and l, boxes, existentials | fig:types | 3.1 |
| Skip, S.S, mu, Z, dual Z, unfold | fig:types, appendix C.2 | 3.1 |
| dual S, equivalence, contractive | appendix C.2 to C.4, caption of fig:types | 3.1 |
| l, u, v, bottom, top, ap | fig:types | 3.1 |
| T[x.j] | fig:types | 3.1 |
| judgment, Gamma, Delta, split | def:judgment | 3.2 |
| Gamma |-_W x prec y | def:judgment, rules in D.2 | 3.2 |
| F = X u up(v), u prec F, x prec H, l preceq H, F <| H, Gamma |- C[x], unl, subtyping | def:judgment | 3.2 |
| tree, prec^rho_C, acyc, conserv | def:creation, right after fig:typing-orders | 3.4 |
| Sigma, Theta_B, process judgment, chans | fig:process-typing | 3.5 |
| V, Theta, fends | def:value-rel | 4.1 |
| stable, offered, ready | def:readiness | 4.2 |
| E, kappa(l), Obl | def:term-rel, def:obligations | 4.2 |
| evaluation context | lem:bind, appendix B.3 | 4.2 |
| P | def:proc-rel | 4.3 |
| semantic judgments | def:sem-judgments | 4.3 |
| p1 par_SigmaC p2 | thm:compose | 4.4 |
| run, pending, lock-free | def:lf | 5.1 |
| a, m, c, N, epsilon, f(o), tk, eta | fig:lf-counters | 5.2 (shaded in figures of 3, by option A) |
| T - c | fig:aging | 5.2 |
| ranked, rho as rank function, rankable | def:ranked | 5.3 |
| Phi, S^{f,m}, F^N_alpha, frame d | def:fuel | 5.4 |
| (q, K, W_a), L, E[kappa_L], kappa_L | def:lf-rel | 5.4 |
| lock-free judgment | def:lf-judgment | 5.4 |

The shaded parts of the figures of section 3 use annotations that section 5
defines. Option A accepts this forward reference, and the caption of fig:types
points at section 5.2.

## Presentation simplifications

None of these changes what a rule or definition means. The Rocq deviations they
touch are recorded in .claude/notes/map-faithfulness.md where noted.

| item | body form | map and Rocq form |
|---|---|---|
| variables | named, lambda b. e, case e (a.e1)(a.e2), !(f = e) | de Bruijn indices |
| point constants | rho | a |
| choice labels | select_i and branch side i with i in {0, 1}, fields x.i | booleans, kappa_false = 0, kappa_true = 1 |
| sequencing of costs | epsilon_1 + epsilon_2 | epsilon_1 . epsilon_2 = c_1 + c_2 |
| contractivity premises (E-Abs, E-Inj, E-Box, E-New, P-Term) | left out, convention that the types of a derivation are contractive, "as usual" | contr premises |
| instances s of E-Box and E-Force | "for all s" ranges over the allowed instances | sinsts s |
| pscoped premises of E-Send and E-Recv | left out, convention on payload types | pscoped |
| freshness of point variables (E-Box, E-Open) | left out, standard convention | iota # Gamma, Delta, F |
| world_wf | part of what a world is | world_wf W, a separate conjunct (map w-wf, Rocq sworld_wf) |
| strict worlds | gone, the deadlock-free part reads consistent worlds | cons and strict at the lock-free view (map-faithfulness, block t-lf-wf) |
| consistent and ranked | one sentence in def:ranked, at a finite N every cons of P-Term, P-Connect and the semantic judgments reads ranked | wok N W (map-faithfulness, block p-typing) |
| E-New | two rules E-New and E-New-Field | one rule with a triple (map), two constructors e_new and e_new_fld (Rocq) |
| new_ok_N | premises acyc and conserv plus the shaded premise N in Nat implies rankable, rankable includes the well-foundedness of the order of the new tree | acyc_new, new_ok_N = acyc_new and (N finite implies wf and rankable) |
| P-Term, P-Connect bookkeeping | tfree, pfree, sth, disjointness stated in words, eta folded into Sigma^eta with the row of fig:lf-counters | tfree, pfree, dom, chans, disjoint, eta premise |
| P-Term tickets | "credit equal to tickets in Theta_B" in words | Theta_B(c^+) = S_x^{m,m} |
| two-closes lemma | without world_wf | world_wf W premise |
| E-Open | "T is no box type" in words | not unlimited T |
| value relation | unit, pairs, sums by reference, index step beta < alpha | V-Unit, V-Prod, V-Sum rules, beta + kappa_beta <= alpha in the lock-free view |
| obligations in the body | four in words with the key environment as math | eight rules with notation Theta(o) doteq H_x and "at" |
| readiness, term and process relation | itemized definitions | map formulas with stable, offered, Theta restricted to offered |
| semantic term judgment | groundings and futures in words | G relation and den_Y(F) |
| index arithmetic of the lock-free relation | E[kappa_L] is the term relation under the costs kappa_L | beta + kappa(l) <= alpha throughout, payload index beta in O-Send |
| fuel | itemized definition in words, renaming closure left out | Fdef with renamings (map-faithfulness, block fu) |
| lock-free process relation | named L, wa as "K fits q and Sigma", Theta_t and Phi_t | S^{N,W}, wa with eleven conjuncts (map-faithfulness, block soup) |
| aging of a context | the check a <= m of context aging only in the slot | lage asks a <= m |
| theorems | restated, sth and conn as "the premises of P-Term and P-Connect" | sth, conn, pterm_N |

## GAP list

1. Title of the paper.
2. sem-props shows the deadlocking reversed cycle only in its breaks text. No map example with a listing for a deadlocked process.
3. fig:points-example panel (b) is schematic, from syn-moves and the shape of ex-ring. The box constraint Cr of ex-ring is not in the map. GrowRing.v rg_F has five facts per pair.
4. No deadlock-free map example sends an end and states all its facts, the ideal single example for payload points.
5. No map program uses sequencing S.S of context-free session types (ex-sinst only in types).
6. No map example for "counters alone admit a cyclic wait" (§5.1).
7. Algorithmic typing, undecided, placeholder §6.
8. Size of the development and build numbers are not in the map (§7).
9. Recorded map and Rocq differences (map-faithfulness.md) have no place yet (§7 footnote or appendix table).
10. Related work. Only PCP and ex-milner is confirmed by .claude/notes (Dardha and Gay Example 1). GV, PGV, Padovani 2014, Kobayashi 2006, Padovani and Novara, Thiemann and Vasconcelos, Mordido and Pérez, APCP have no confirmed map example. The old notes cover pre-v2 programs.
11. The authors' previous GV paper (logical relation for deadlock freedom) has no entry in main.bib.
12. Predicates defined only in note prose (conn, sth, pterm_N, sinsts, pfree). The body states them in words. The appendix index of notation is gone.

## Open questions for the author

1. Option A or B for the lock-free split.
2. Points example. ex-cycle (complete facts, no payload) or ex-ring (payload, facts missing from the map) or a new map example for payload points.
3. Keep fig:composition-example (0.35 page).
4. ex-flag in the intro as a full example or only a forward reference to §4.4.
5. Appendix index of notation. Dropped, the symbol table above replaces it. Say if a one-table index in the appendix is wanted.
6. Combined form for replacements. The body avoids it (def:ranked says it once). The appendix keeps `cons / ranked` with the shaded part.
7. Conclusion after related work, or related work as the very last section.
8. Which related systems get a row in tab:subsume once examples are confirmed.
