# Paper plan, GV≺ skeleton

The body figures are set by hand in paper/figures/*.tex from the content of
docs/explorer/map.json. The definitions and theorems of the body are restated
in paper form in the section files. The appendix, the example listings and the
rule macros come from the map through .claude/notes/paper/tools/map2tex.py
(`make -C paper gen`). Rerun it after a map change, then check the body
figures against the changed blocks by hand. Paragraph slots are `% PAR:`
comments, gaps are `% GAP:`. This plan and the previews live in
.claude/notes/paper/ (paper/ holds only build inputs).

## Revision 3 (branch paper-rev3)

State. `make -C paper` passes, no undefined references, no overfull boxes,
`make -C paper check` passes. 41 pages, body pages 1 to 16 (the references
start on page 16), appendix from page 18. Previews of pages 2 to 16 in
.claude/notes/paper/preview/. Where the older sections below disagree with
this section, this section holds.

### What changed, per feedback item

1. Running example. Milner's scheduler (ex-milner, `ms_deadlock_free`,
   `ms_dftyped`) is Example 1.1 in the introduction. §2 draws it in
   fig:points-example (a) (threads, ends, points, the order in which each
   agent acts) and fig:world-example (the nine facts of `ms_base`, columns
   by field label, so the facts visibly rise). §3 has ex:milner-typed (the
   protocol S_m = !∗.Close, the type of the first new and the constraint
   C_m of `ms_L`, by agent). PAR slots in §2 to §6 name the scheduler. The
   flag moved to §4.4 as the showcase (ex:flag, fig:composition-example,
   lem:two-closes, prop:flag-rejected, prop:flag-semantic, cor:flag-df).
   The brief named SemFlag.v theorems `sf_underivable_top`, `sf_sem_typed`,
   `sf_deadlock_free`. SemFlag.v exists only in the old development. The
   v2 theorems for the same program (the map's ex-flag) are `sbv_rejected`,
   `sbv_thread_E` and `sbv_deadlock_free` in examples/SemBranch.v, and the
   body cites those. ex-cycle moved to §5 as the lock-free worked example
   (LFCycle.v). ex-close moved to the appendix (slot in §2).
2. No words in rules. E-Box: `∀ s̄ ∈ Inst`, Inst defined in
   conv:implicit. E-Open: `¬ unl T`. P-Term: `tfree T`, `pfree Σ`,
   `pairs^N(Θ_B, C_0)`, `∀ o ∈ dom Σ. tk_η(o) ≤ N`. P-Connect: the tickets
   premise as a formula, the conclusion `p_1 ∥_{Σ_C} p_2`. The moves of
   fig:worlds as `sel`, `bra`, `payload`. All predicates are defined in
   def:side, def:proc-judgment, def:creation and def:proc-conds.
3. Anatomies. def:judgment (typing), def:proc-judgment (processes),
   def:rel-anatomy (V, E, P), def:fuel (fuel), def:lf-rel (annotated
   configurations), def:algo (algorithmic judgments), def:lf-ann (lock-free
   annotations), each a displayed form and a table of components.
4. Nothing undefined. See the symbol audit below. `rankable` is defined in
   def:creation (one phrase plus reference) before fig:typing-orders
   uses it, with the full reading in def:ranked.
5. Disjointness. conv:implicit says "Contexts combined in one rule are
   disjoint". Removed from P-Connect, thm:compose, thm:lf-compose, V-Arrow,
   O-Recv, O-New keeps its freshness premise. Simplification recorded below.
6. V and E as rules. fig:value-rel (V-Unit, V-Sess, V-Prod, V-Sum,
   V-Arrow, V-Box, V-Ex), fig:term-rel (E, At-Free, At-Cost, O-Beta,
   O-Close, O-Spawn, O-New, O-Send, O-Recv, P-Zero, P), fig:proc-obl
   (Q-Tau, Q-Send, Q-Recv). Readiness, fuel and the lock-free relation stay
   itemized.
7. Diagrams. Redrawn and checked in renders. fig:points-example (scheduler
   ring plus payload panel), fig:world-example (new), fig:composition-example
   (flag, with legend), fig:lf-example (new worked table). Each has a
   legend or a caption that says what boxes, dots, dotted lines, arrows,
   dash styles and grey names mean. fig:worlds is formulas only.
8. Lock-free annotations. def:lf-ann gives the anatomy (counter, credit,
   tickets, latent cost, cost, aging, N, η). ex:cycle with fig:lf-example
   is the worked example at N = 4 (tickets 2 per end from `e_new'` and
   `e_new_at'` of examples/LFTools.v, close c ages d from credit 2 to 1,
   the fuel counter of d falls from 2 to 1). fig:aging and fig:lf-counters
   are gone, aging is the gloss "subtracts the credits used" in conv:lf
   and def:lf-ann with a pointer to the appendix.
9. Mechanization section removed (7-mechanization.tex deleted). Its slots
   moved: one world per arm (§3.3, E-Case), point reuse (§3.4),
   contractivity (§3.1), two fixed points (§5.4), one notion of world
   (§2.2), transfinite indices (§4 intro), assumptions (thm:df and thm:lf
   footnote slots, conclusion). Contributions and outline no longer cite it.
10. Limitations. §8 "Limitations" (sec:limitations) with two slots, the
    second for the author's reason why tree structure is not subsumed.
    Contribution 4 now reads "comparison with priority systems by example
    ... what it does not cover", no subsumption claim. The section title
    "How GV≺ Subsumes Other Systems" became "Related Work".
11. Lock freedom. thm:lf in its own subsection §5.5, with EM and FC in the
    statement and a footnote slot, mirrored by thm:df in §4.5 (no axiom,
    footnote slot).
12. Algorithmic. §6 has def:algo, def:oracles (six oracles, one phrase
    each), thm:algo-sound (`algo_sound`), thm:algo-complete
    (`algo_complete`, `algo_iff`), thm:algo-dec (`syn_dec`, `chk_dec`,
    `alg_sound`, `alg_complete`). The map dump figure fig:algorithmic is gone.
13. Cleanup. W dropped from the rule-figure headers, judgment and process
    anatomies before first use, long displays split (pairs, readiness, E, P,
    V-Arrow, V-Box, O-Recv, Q-Recv), figures inside their sections.

Additional feedback from the coordinator.

- A. Shade only behind lock-free material, neutral grey (lfbg = black!11),
  in body and appendix.
- B. Syntax colouring of the first paper: `\kw`, `\tlam`, `\tpair`,
  `\tunit`, `\tbox` in cTm; `\tyc` (Close, Skip), `\sSend`, `\sRecvT`,
  `\arr`, `\tyotimes`, `\tyoplus`, `\tymultimap`, `\tyBox`, `\tyexists`,
  `\tyforall`, `\tymu`, `\tyunit` in cTy; metavariables through lrlight's
  `\ty`, `\tyB`, `\sty`, `\tm`, `\proc`, `\val`, `\valB`, `\lenv`, `\senv`
  and new `\cGamma`, `\cTheta`, `\cPhi`. Listing keywords use kwcolor = cTm.
  Fact arrows use factcolor = cTy. Points, worlds and relations stay black.
- C. "(lfp)" gone. The caption of fig:term-rel says that at a fixed index
  the rules E and P are read inductively. map2tex.py replaces the map's
  `(\mathsf{lfp})` by "(least fixed point over steps of cost 0)".
- D. Receive rules split over lines (O-Recv, Q-Recv). The process
  obligations are in the body (fig:proc-obl) with def:proc-conds naming
  `opened` (send_split), `matches` (recv_ok), `closed` (recv_back) and
  `iface` (recv_env), one bullet each. The disjointness parts
  (`ech[dom Θ₂] ∩ C = ∅`, first conjuncts of send_split and recv_ok,
  `C' ∩ chans Σ = ∅`) are left to the convention.
- E. Reader pass. Fixes. Rocq mentions removed from conv:implicit; `ech`
  renamed chan and glossed; the caption of fig:worlds says what W ⊕_ρ C and
  a constraint are; fig:world-example no longer says "first creation";
  `Sub-Ex` and `E-Pack` no longer named in def:oracles; session subtyping
  ⊑ points to the appendix; tk(o) defined in def:lf-ann; the stop clause of
  P uses ∗ as a term; overfull displays split.
- F. Lock-free parts are marked only by the shade. `lfcolor` is deleted.
  `\lfadd` in running text shades word by word (`\lfw`, map2tex.py
  `shade_words`), the "(LF)" mark of appendix heads too.
- G. Type variables α (`\tvar`), ordinal indices β (`\ix`) and γ (`\ixs`),
  one macro per role in notation.tex. map2tex.py renames Z, α, β in its
  output (a β that names a β step keeps its letter).
- H. Every type in cTy, see B.
- I. paper/ holds only build inputs. Moved to .claude/notes/paper/: PLAN.md,
  README.md, preview/, tools/, rocqrefs.py, old-draft/, llncs.cls,
  splncs04*.bst, rocq-logo.svg. paper/Makefile calls the generators there.

### Symbol audit (body, in reading order)

| symbol | defined or glossed | where |
|---|---|---|
| o, c±, ō, k, e, v, p = (C, E), let | fig:syntax | §2.1 |
| step relations, reachability | caption of fig:syntax, App. B | §2.1 |
| terminated, deadlock-free | def:df | §2.1 |
| ρ, ι, x⁺, x·κ, x̄ | fig:worlds and its caption | §2.2 |
| sel, bra, payload | fig:worlds caption | §2.2 |
| W, ≺_A, Point_A, ≺_W, ≼_W, cons, ⊑, ⊔, W ⊕_ρ C, C[ρ] | fig:worlds and caption | §2.2 |
| T, U, S, C, S_x, ⊸^u_l, □, ∃^l, Skip, S.S, μα, α, ᾱ | fig:types | §3.1 |
| duality, ≈, unfold, contractive | caption of fig:types, App. C | §3.1 |
| ap, bounds ⊥ ⊤, T[x·j̄] | fig:types | §3.1 |
| shade, X / Y, a, m, [c], ε, N, η, Δ − ε, ranked | conv:lf (gloss, forward refs) | §3.1 |
| Inst, disjoint contexts | conv:implicit | §3.1 |
| Γ ; Δ ⊢^F_{W,N} e : T ! ε | def:judgment | §3.2 |
| unl, tfree, 𝒯₀, Γ ⊢_W x ≺ y, ≼, Γ ⊢ C[x̄], F = X ∪ ▵v, F ◁ H, u ≺ F, x ≺ H, l ≼ H, ≤, Δ₁,Δ₂ | def:side | §3.2 |
| tree, base, ≺^ρ_C, acyc, conserv, rankable | def:creation | §3.4 |
| S_m, C_m | ex:milner-typed | §3.3 |
| Σ ⊢^{N,η}_W p : T, tk_η, Σ^η, pfree, chans, Σ̄, ∥_Σ, pairs, ends | def:proc-judgment | §3.5 |
| V, E, P, β, Θ, W ⊢, ap(Θ), fends, ≐ | def:rel-anatomy | §4 |
| stable, offered, link, Θ\|_A, Θ \ A, A ≺_W B | def:readiness | §4.2 |
| at, Obl, κ = κ_DF | fig:term-rel and caption | §4.2 |
| chan, sdual, opened, matches, closed, iface, Pobl, τ | def:proc-conds, fig:proc-obl | §4.3 |
| ⊨ (terms, processes), G, \|Δ\|, den_Y | def:sem-judgments | §4.3 |
| W_a, W_b, thread, other | ex:flag, prop:flag-semantic | §4.4 |
| lock-free, runs, parts, maximal, wfair, pend | def:lf | §5.1 |
| f(o), credit, tickets, tk, cost, aging, N, η | def:lf-ann | §5.2 |
| ranked, ϱ | def:ranked | §5.3 |
| Fuel, Φ, S^{f,m}, σ, d, idle | def:fuel | §5.4 |
| (q, K, W_a), L, E[κ_L], κ_L, "K fits q and Σ" | def:lf-rel | §5.4 |
| ⫦ (lock-free judgment), erase | def:lf-judgment | §5.4 |
| \|·\| (erasure of annotations), ⊨[κ_L] | thm:lf-fundamental | §5.4 |
| ⇒, ⇐, annotated t, \|t\| | def:algo | §6 |
| oracles, ⊑ | def:oracles | §6 |

Glossed only, defined in the appendix: evaluation contexts (lem:bind),
Ord rules, subtyping, aging, step costs, fuel of values, "K fits q and Σ"
(eight of eleven conjuncts), den_Y.

### Simplifications added in revision 3

| item | body form | map and Rocq form |
|---|---|---|
| disjointness | one line of conv:implicit, no premise in P-Connect, thm:compose, thm:lf-compose, V-Arrow, O-Recv, Q-Tau, Q-Send, Q-Recv | disjoint, ##, # premises, sth st_disj, conn cn_* disjointness, send_split and recv_ok first conjuncts |
| W in rule-figure headers | dropped (rules leave W implicit already) | typed W ... |
| P-Term effect | ε | c |
| thm:compose (1) | pfree Σ ∧ pairs(Θ_B, C₀) | sth Θ Σ Θ_B C (with Θ = Σ ∪ Θ_B, disjointness) |
| thm:compose (2), thm:lf-compose (2) | pfree of Σ₁, Σ₂, Σ_C, Σ̄_C as the dual of Σ_C | conn (cut_dual up to ≈) |
| process obligations | Q-Tau, Q-Send, Q-Recv with opened, matches, closed, iface | send_split, recv_ok, recv_back, recv_env |
| E and P | rules E and P with three premises each, inductive reading in the caption | Erel, Prel as least fixed points (Eind, Pind) |
| index letters | β main, γ smaller (\ix, \ixs) | α, β |
| type variables | α (\tvar) | Z |
| ranked | ranked W implies cons W (swf_sacyc), the claim "differ only on infinite worlds" dropped | w-wf |
| ech | chan | ech |
| \dual | uncoloured, it applies to points, ends and session types | none |
| worked LF example | numbers of LFCycle.v (tickets N/2 = 2), counters from the fuel obligations | cy_typedN |

### Open questions for the author

1. Theorem names. The brief cited SemFlag.v theorems that are not in v2.
   The body cites `sbv_rejected`, `sbv_thread_E`, `sbv_deadlock_free`.
2. The flag world W_a = ({x, y}, {x ≺ ȳ}) treats the constants x, y as
   bases, which is how the Rocq names them (NConst 0, 1). Say if the body
   should name them ρ₀, ρ₁ instead.
3. fig:world-example omits the shifted facts x⁺ ≺ y. Draw them, or keep
   the caption remark.
4. Process obligations in the body cost about half a page. Keep them in
   the body (feedback D) or move fig:proc-obl back to the appendix.
5. The first paper sets type metavariables in sans serif (lrlight Ty sort).
   Kept, so T, U, S render as sans serif in cTy.
6. GAP 5 (no map program uses S.S) is resolved by the scheduler, whose
   protocol is !∗.Close. The map's ex-milner does not say so yet.
7. Contribution 6 says "no axioms for deadlock freedom". th-sound says no
   classical hypothesis enters, confirm with `Print Assumptions soundness`.

## Build

- `make -C paper` runs map2tex.py, rocqrefs.py and latexmk. No undefined
  references, no overfull boxes.
- Skeleton today (figures, listings, definitions, theorems, headings, no prose).
  33 pages. Body pages 1 to 11 (intro 1, language 1 to 3, typing 3 to 6,
  relation 6 to 9, lock freedom 9 to 11), of which about 10 pages are figures,
  listings, definitions, a convention and theorems. References pages 11 and 12.
  Appendix pages 13 to 33.
- Appendix parts. Map blocks A to F, pages 13 to 28, each block a numbered item
  (A.1, A.2, ...) that the body references. All 30 example listings G, pages
  29 to 33. The index of notation is gone, the symbol table below replaces it.
- Listings. A letter with a combining macron in the map code (the dual end
  $\bar{c}$) is set as `\bar` by map2tex.py.
- `\raggedbottom` in main.tex only for the skeleton. Remove it once the
  paragraphs fill the pages.
- Previews of four pages in paper/preview/ (syntax and worlds, typing
  rules, process typing and the value relation, lock freedom).

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
| duality, equivalence, contractivity, unfold | appendix C.2 to C.4 | fig:types caption ("standard"), contractivity in conv:implicit |
| pscoped | appendix C.6 | conv:implicit, payloads mention only their own point variables |
| freshness of bound point variables, allowed instances sinsts | appendix D.10, D.11 | conv:implicit |
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
| obligations of beta, new, spawn, send, recv, close | body, def:obligations | |
| obligations of select, branch, link | appendix E.6 | def:obligations, one sentence |
| step costs kappa_DF and kappa_L | appendix E.3 | def:term-rel and def:lf-rel, in words |
| bind lemma | body, lem:bind | evaluation contexts B.3 |
| P | body, def:proc-rel | |
| process obligations | appendix E.10 | def:proc-rel |
| fu-vs | appendix E.11 | slot |
| fuel | body, def:fuel | |
| fuel obligations | appendix E.13 | def:fuel, in words |
| values with fuel | appendix E.14 | def:fuel |
| lock-free process relation | body, def:lf-rel | wa as "K fits q and Sigma", its conjuncts in one sentence, E.15 |
| semantic judgments, grounding G, den | body, def:sem-judgments | grounding and denotation in words, E.16 |
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
| x preceq_W y | fig:worlds | 2.2 |
| T, S, C, S_x, arrows with u and l, boxes, existentials | fig:types | 3.1 |
| Skip, S.S, mu, Z, dual Z, unfold | fig:types, appendix C.2 | 3.1 |
| dual S, equivalence, contractive | appendix C.2 to C.4, caption of fig:types | 3.1 |
| l, u, v, bottom, top, ap | fig:types | 3.1 |
| T[x.j] | fig:types | 3.1 |
| implicit premises (contractive, payload scoping, fresh binders, instances) | conv:implicit | 3.1 |
| judgment, Gamma, Delta, split, unl | def:judgment | 3.2 |
| Gamma |-_W x prec y, Gamma |-_W x preceq y, Gamma |- C[x] | def:judgment, rules in D.2 | 3.2 |
| F = X u up(v), u prec F, x prec H, l preceq H, F <| H, subtyping | def:judgment | 3.2 |
| tree, prec^rho_C, acyc, conserv | def:creation, right after fig:typing-orders | 3.4 |
| Sigma, Theta_B, process judgment, chans | fig:process-typing | 3.5 |
| V, Theta, fends | def:value-rel | 4.1 |
| stable, offered, ready | def:readiness | 4.2 |
| E, kappa(l), E[kappa'], Obl | def:term-rel, def:obligations | 4.2 |
| evaluation context | lem:bind, appendix B.3 | 4.2 |
| P | def:proc-rel | 4.3 |
| semantic judgments | def:sem-judgments | 4.3 |
| p1 par_SigmaC p2 | thm:compose | 4.4 |
| run, pending, lock-free | def:lf | 5.1 |
| a, m, c, N, epsilon, f(o), tk, eta | fig:lf-counters | 5.2 (shaded in figures of 3, by option A) |
| T - c | fig:aging | 5.2 |
| ranked, rho as rank function, rankable | def:ranked | 5.3 |
| Phi, S^{f,m}, F^N_alpha, frame d | def:fuel | 5.4 |
| (q, K, W_a), L, E[kappa_L], kappa_L, K fits q and Sigma | def:lf-rel | 5.4 |
| lock-free judgment | def:lf-judgment | 5.4 |
| erasure of annotations, |Delta| and |T|, the term judgment at kappa_L | thm:lf-fundamental | 5.4 |

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
| contractivity premises (E-Abs, E-Inj, E-Box, E-New, P-Term) | left out of the figures, stated once in conv:implicit (every session type of a derivation is contractive, with the list of the Rocq rules that carry the premise) | contr premises |
| instances s of E-Box and E-Force | "for every instance s" in E-Box, conv:implicit says which lists are instances (contractive, payloads scoped) | sinsts s |
| pscoped premises of E-Send and E-Recv | left out of the figures, conv:implicit | pscoped |
| freshness of point variables (E-Box, E-Open) | left out of the figures, conv:implicit | iota # Gamma, Delta, F, U |
| world_wf | part of what a world is | world_wf W, a separate conjunct (map w-wf, Rocq sworld_wf) |
| strict worlds | gone, the deadlock-free part reads consistent worlds | cons and strict at the lock-free view (map-faithfulness, block t-lf-wf) |
| consistent and ranked | one sentence in def:ranked, at a finite N every cons of P-Term, P-Connect and the semantic judgments reads ranked | wok N W (map-faithfulness, block p-typing) |
| E-New | two rules E-New and E-New-Field | one rule with a triple (map), two constructors e_new and e_new_fld (Rocq) |
| new_ok_N | premises acyc and conserv plus the shaded premise N in Nat implies rankable, rankable includes the well-foundedness of the order of the new tree | acyc_new, new_ok_N = acyc_new and (N finite implies wf and rankable) |
| P-Term, P-Connect bookkeeping | tfree, pfree, disjointness stated in words, eta folded into Sigma^eta and explained in the caption of fig:process-typing | tfree, pfree, dom, chans, disjoint, eta premise |
| P-Term restricted ends | one premise "Theta_B types exactly the ends of C_0, each pair as c^+ : S_x^{m,m}, c^- : dual S_{dual x}^{m',m'}" and m + m' <= N | dom Theta_B = ends(C_0), chans Sigma cap C_0 = empty, P-Term.pairs |
| E-Box instances | "for every instance s" after the premise | forall s. sinsts s => ... |
| E-Case | one premise for both arms, (i = 1, 2) | two premises |
| two-closes lemma | without world_wf | world_wf W premise |
| E-Open | "T is no box type" in words | not unlimited T |
| value relation | unit, pairs, sums by reference, index step beta < alpha | V-Unit, V-Prod, V-Sum rules, beta + kappa_beta <= alpha in the lock-free view |
| obligations in the body | six in words (beta, new, spawn, send, recv, close) with the key environment as math, choice and link in one sentence | eight rules with notation Theta(o) doteq H_x and "at" |
| readiness, term and process relation | itemized definitions, each clause one sentence saying what must hold | map formulas with stable, offered, Theta restricted to offered |
| process obligations | internal steps and messages with the environment in one item of def:proc-rel | Q-Tau, Q-Send, Q-Recv with send_split, recv_ok, recv_back, recv_env |
| step costs | in words in def:term-rel (kappa_DF) and def:lf-rel (kappa_L), E[kappa'] named in def:term-rel | the table of ct-costs |
| semantic term judgment | groundings and denotations in words, with the three cases of den_Y (v = top, v = bot or bot in X) | G relation and den_Y(F) |
| index arithmetic of the lock-free relation | E[kappa_L] is the term relation under the costs kappa_L | beta + kappa(l) <= alpha throughout, payload index beta in O-Send |
| fuel | itemized definition in words (stop, step, action, force, send, new, link), renaming closure left out, FV in the stop item | Fdef with renamings (map-faithfulness, block fu), FV rules of fv |
| lock-free process relation | named L, wa as "K fits q and Sigma" with its conjuncts in one sentence, Theta_t and Phi_t, "a session type and a protocol per held end" for Delta : K | S^{N,W}, wa with eleven conjuncts, Delta : K (map-faithfulness, block soup) |
| lock-free judgment | "some annotated configuration a with erase(q) = p" | exists a. erase(q_a) = p and a in S |
| aging of a context | the check a <= m of context aging only in the slot | lage asks a <= m |
| theorems | restated. thm:compose (1) "the premises of P-Term on the interface", (2) and thm:lf-compose (2) the disjointness in words; thm:lf-compose (1) "apart from ranked W"; thm:lf-fundamental (1) with the erasure |Delta|, |T| and the judgment at kappa_L | sth, conn, pterm_N (keeps world_wf W), Delta_df, T_df |
| world_wf in theorems | absorbed (th-terms, th-compose lock-free P-Term, t-lemmas) | world_wf W premise |
| ranked worlds | def:ranked says "the two notions differ only on infinite worlds" | w-wf why text |
| rankable | exits witnessed by finite sets of context points descending along the tree order, in words | gen_new_rel (note new.rank) |

## Quirks found

Things the paper form exposes about the system. Nothing here was changed,
each one is for the author.

1. E-New-Field asks nothing of the point $x$. The rule has the premises
   $\mathsf{unl}\,\Delta$ and the tickets only, so a thread may create a
   channel at a field $x\cdot\kappa$ of a point it does not hold, of a base
   that is not in its world, and several times at the same field (the map
   example ex-point-reuse creates twice at the field of the constant 0 over
   the empty world). Set next to E-New, which asks acyc and conserv, the
   field rule reads as a loophole. The map explains that a field point is an
   old point whose facts were fixed with its base, so no fact is added. The
   author may want a sentence on why this is sound, or a premise that $x$
   is a point of the context.
2. A thread holding an unopened result of $\mathsf{new}$ cannot act. The
   existential of E-New has the lower point $\bot$, $\mathsf{ap}$ of it is
   $\{\bot\}$, so $F \triangleleft H$ with the pair in $H$ makes every
   $x \prec F$ fail. A subterm that runs while the thread holds the unopened
   pair of a fresh creation performs no action. Intended by the design (no
   fact of the context mentions the new points), but a reader of
   fig:typing-orders sees only the $\bot$. The listings write
   `let <c, c'> = new in`, and the body never says where E-Open applies in
   such a let (E-Open opens an entry of $\Delta$, E-LetP needs a product).
3. At a finite bound the E-New premise $\mathsf{rankable}$ includes
   $\mathsf{wf}(\prec^{\rho}_{C})$, which implies $\mathsf{acyc}_\rho(C)$.
   So the rule carries a redundant premise at a finite $N$, and the shaded
   part reads as an addition where it is a strengthening.
4. E-Link in the lock-free instance with the interface annotation of the
   relation. The lock-free process relation gives each interface end at
   most $\lfloor N/2 \rfloor$ tickets (map-faithfulness, note sp.own), and
   E-Link asks $a_1 + m_2 > N$. Two interface ends at $\lfloor N/2 \rfloor$
   fail the premise at every even $N$, so no component links two of its
   interface ends at the annotation the relation uses. The map's example
   ex-link gets around it with $N$ and $0$. The typing rule P-Term lets
   $\eta$ choose, the relation does not.
5. E-Open never reads the lower point $l$ of the existential it opens. $l$
   matters only while the value is held unopened, through
   $\mathsf{ap}(\exists^{l}\ldots) = \{l\}$. The figure shows $l$ in the
   premise and nothing uses it, which looks like a missing premise.
6. Fuel and the relation disagree on what a link checks. E-Link and F-Link
   check the tickets condition, O-Link checks only duality. The body states
   both (def:obligations, def:fuel), and the asymmetry is visible.
7. The cost of E-Case is $\varepsilon_0 + \max(\varepsilon_1, \varepsilon_2)$
   while the contexts of the arms age by $\varepsilon_0$ only. A reader may
   expect the held entries after the case to have aged by the arm as well.
   They do, through the result type: both arms return the same $T$ at the
   same credits, so the max is in the result. Worth one sentence in the
   lock-free section.
8. P-Term asks $\mathsf{cons}\,W$ although the derivation of $t$ reads $W$
   only through Ord-World, and E-New never grows $W$. A world of typing is
   thus a set of facts the thread assumes, not a record of its creations.
   The body never says this in a definition, the slot "P-Term, one thread,
   restricted channels, consistent world" should.

## Faithfulness questions

Simplifications I did not make because they would deviate from the Rocq
beyond .claude/notes/map-faithfulness.md.

1. def:ranked says "a ranked world is consistent, and the two notions differ
   only on infinite worlds", the map's own words (w-wf, why). The Rocq has
   `swf_sacyc` for the first half. The second half has no Rocq lemma that
   the map cites. Keep it as a remark, or drop the second half.
2. thm:lf-compose (1) states "the premises of P-Term apart from ranked W".
   The Rocq predicate `pterm_N` keeps `world_wf W`, which the body absorbed
   into the notion of a world (simplification "world_wf"). Faithful under
   that simplification, listed here because the theorem row of the map
   shows the conjunct.
3. def:lf-rel states "K fits q and Sigma" in one sentence with eight of the
   eleven conjuncts of `soup_consistent`. Left out: finiteness of each
   counter (`sp_fin`, the map writes N for the counters anyway), the
   protocol of an interface end equal to the session type of its entry, and
   duality of protocols up to the annotated subtyping. Say if the sentence
   should list all eleven or none.
4. def:obligations now states O-Spawn and O-Close in the body. The thunk
   type in O-Spawn is $\ast \multimap^{\top}_{\bot} \ast$ as in the map. The
   map's E-Spawn (appendix D.14) types a written $\lambda$ at $u = \top$,
   $l = \bot$, and the body never shows E-Spawn. A reader meets $\top$ and
   $\bot$ on an arrow first in O-Spawn. Either E-Spawn joins
   fig:typing-core (one line) or the slot before def:obligations says it.

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
9. E-Spawn in the body (quirk 8 of the list above, faithfulness question 4).
