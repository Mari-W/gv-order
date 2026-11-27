# Paper plan, GV≺ skeleton

The body figures are set by hand in paper/figures/*.tex from the content of
docs/explorer/map.json. The definitions and theorems of the body are restated
in paper form in the section files. The appendix, the example listings and the
rule macros come from the map through .claude/notes/paper/tools/map2tex.py
(`make -C paper gen`). Rerun it after a map change, then check the body
figures against the changed blocks by hand. Paragraph slots are `% PAR:`
comments, gaps are `% GAP:`. This plan and the previews live in
.claude/notes/paper/ (paper/ holds only build inputs).

## Revision 6 (branch paper-rev6)

State. Branch paper-rev6 from main (3479b882). Where older sections
disagree with this one, this one holds.

### Processes have named threads (simplification)

One kind of process, from §2 on: P = (C, E) with C the restricted channels
and E a finite map from thread names t to terms, P(t) = E(t). The body has
no configuration q, no annotated configuration over q and no erase.
(C, {e₁, …, eₙ}) is the process whose threads have distinct names (P-Term,
prop:flag-rejected, P-Stop of fig:term-rel). def:runs ends with one
sentence: typing and the relations read only the restricted channels and
the terms. P₁ ∥ P₂ composes at disjoint thread names (def:proc-judgment).
The lock-free relation reads a = (P_a, K, W_a), and def:lf-judgment asks
P_a ∼ P, "P_a is P with its threads renamed" (app:syn-procs).

Checked against the Rocq.

| body | Rocq | why it is faithful |
|---|---|---|
| process P = (C, E) | `config` (lang/Process.v), `gset chan * gmap nat expr` | the same type |
| P —ev→ P' | `istep`, the only definition of process steps | the same relation |
| typing, P⟦·⟧, readiness, obligations, sem. judgments of P | stated for `proc` (multiset), read at `erase P` | they read only C and the terms; the soup steps of `erase P` are the erasures of the steps of P (`istep_pspec`, `pspec_lift`, `pstep` is defined as the erasure) |
| deadlock free P | `deadlock_free (erase P)` | equivalent by the same two lemmas |
| lock free P, runs from r₀ = P | `lock_free (erase P)`, runs from any r₀ with `erase r₀ = erase P` | the Rocq form implies the body form (take r₀ = P), and the theorems conclude the Rocq form |
| P_a ∼ P | `erase (s_q a) = p` in `lf_sem` | same multiset of terms iff a bijection of thread names maps one map to the other |
| P₁ ∥ P₂ at disjoint names | `pconn`, multiset sum | the union erases to the sum |

### Deadlock and lock freedom in §2 (task 2)

def:runs (§2.1) introduces steps with events and parts(ev), internal events
and closed steps, runs, maximal, weakly fair and pending, in words with
appendix pointers (app:sem-proc, app:sem-events). def:df, also labelled
def:lf, states terminated, deadlock-free and lock-free side by side. §5
refers back (its first slot says so), def:lf is gone from §5, thm:lf still
cites def:lf. Shading: none. By conv:lf a shade marks the annotations and
premises of the lock-free instance of typing at a finite N. Deadlock
freedom and lock freedom are properties of untyped processes, so both stay
unshaded. The map keeps lock freedom in its lock-free view (its modes are
views, not the shading convention), so the generated appendix shades the
lock_free line of sem-props. The map now has runs beside the events
(sem-events "Events and runs").

### Renames (task 3)

| was | now | where |
|---|---|---|
| p, p', p₁, p₂ (processes) | P, P', P₁, P₂, and Q (`\procB`) for a second process | `\proc` in lrlight.sty, body, figures, map |
| q, configurations, q_a | P, P_a | body def:lf-rel, def:lf-judgment, map |
| M (thread map) | E | map sem-proc, P-Act-*, se.echans, se.upd |
| counter relation F^N_β⟦Φ ⊢ σ ! d⟧, FV | Z^N_β⟦…⟧, ZV | `\Fuel` in notation.tex, map fu, fu-obls, fv, soup, notes |
| raw t for a thread term in P-Term, thm:compose, thm:fundamental-terms, thm:lf-compose, thm:lf-fundamental | e (`\tm`) | t is now a thread name |

Clash check. Q appears only in rule names (Q-Tau, Q-Send, Q-Recv, Q-Link),
no set or relation uses Q. P is also the name of the process relation
P^W_β⟦Σ ⊢ T⟧, as V and E are; "P ∈ P⟦…⟧" reads like "e ∈ E⟦…⟧". Z is
not used elsewhere in the map or the paper. The collector threads of
Milner's scheduler are called P₀, P₁, P₂ in the listing and in
fig:points-example; they are code names, left as they are (open question
for the author whether to rename them).

The renames were done in the map itself (scripts
.claude/notes/map-procs-P.py and map-procs-P-2.py) with deviations:
syn-procs (merged proc/config/erase, notation ∼), proc.proc, proc.same,
se.r0 (simplified, run from r₀ = P), sp.lfsem (P_a ∼ P), tp.msunion
(union at disjoint names), fu (letter Z), one deviationRule for every
definition the Rocq states on `proc`. Notes proc.config, proc.erase,
type.Config are gone.

### Map backport

The presentation changes of revisions 3 to 5 and of "Presentation
simplifications", checked one by one against docs/explorer/map.json.
Applied by .claude/notes/map-backport-rev3-5.py (after map-procs-P.py and
map-procs-P-2.py). Where the map is the detailed reference and the paper
only moves a formula to the appendix, the map keeps the formula and takes
the paper's names. Every departure from the Rocq has a deviation.

| change (revision) | map | why |
|---|---|---|
| Milner's scheduler leads (r3.1) | applied, ex-milner is the first example | |
| no words inside rules (r3.2) | already so, no \text words in rule premises. P-Term reads pairs^N(Θ_B, C₀), defined below the rules | |
| anatomies (r3.3) | not applied | the map's notes give each component, an anatomy table would repeat them |
| disjointness by one convention (r3.5, D) | applied to P-Term, P-Connect, Q-Tau, Q-Recv. Convention "∪, ⊎", deviationRule kind omitted. Notes P-Term.disj, P-Connect.disj, tp.Sigma removed | the conjuncts inside the definitions of opened and matches stay, they define named predicates |
| V, E, P, obligations as rules (r3.6) | applied. V, obligations, process obligations were rules. E is now rule E, P the rules P-Zero and P | |
| "(lfp)" replaced by the inductive reading at a fixed index (C) | applied. Tag gone from e-rel and p-rel, captions and note rel.lfp say it. map2tex.py no longer rewrites the tag | |
| opened, matches, closed, iface (D) | applied, renamed with deviations on Q-Send.split, Q-Recv.ok, Q-Recv.back, Q-Recv.env | |
| ech is chan (E) | applied, deviation on end.ech | |
| α, β, γ letters (G) | already in the map (revision 5) | |
| futures as sets of points (r4.3) | applied as one sentence in t-contexts. The general form F = X ∪ △v stays the definition | the map is the reference for the general form |
| η dropped, annotations in Σ (r4.4) | applied. P-Term asks tk(o) ≤ N, P-Connect tk(o) + tk(ō) ≤ N, ⊢^N without η, note tp.tk added, tp.lift removed. Deviation on p-typing (iann, tenv_ofk, ptyped_iann_local, p_connect_iann) | |
| P-Term premises tfree, pfree, pairs glossed (r4.5) | applied for pairs (named predicate with its definition). tfree and pfree were named already | |
| acyc, conserv, rankable explained (r4.6) | already. Notes new.acyc, E-Open.cons, new.rank state them in the paper's terms | |
| E-Abs, E-New-Field, E-Force, E-Open only in captions (r4.7) | not applied | the map shows every rule, the paper only hides them |
| readiness and process conditions in words (r4.10, r4.11) | not applied | the map keeps the formulas, its captions say the cases in words already |
| E-App premise ε₂ ≤ a (r5) | already (map-eapp-premise.py) | |
| lock-free composition asks tk(o) + tk(ō) ≤ N (r4 correction) | applied to th-compose and note th.lf-p-connect | `lf_p_connect` asks `tsum_ok` |
| interface tickets bounded by Σ (r4 correction) | applied to sp.own, deviation names soup_invk, SoupK, khalf. soup sources list SoupK, soup_invk | |
| signal and wait (r3 E, map2tex rename) | applied in the example code with deviations. map2tex.py CODE_RENAME dropped, signal and wait stay keywords | |
| counters and cost wording (r5) | already, checked: no fuel, aging or frame (other than evaluation frames) in the prose | |
| worlds and points wording (r3 E) | partly. The map's ex-milner still says "the first creation states these 18 facts" | the paper's fig:world-example counts the nine facts of ms_base without shifts. Which count the map should give is left to the author |
| named variables, ρ constants, select_i, ε₁ + ε₂, contractivity and freshness in conv:implicit, E-Case one premise, value relation by reference (Presentation simplifications) | not applied | presentation devices of the body, the map is the detailed reference and keeps the separate premises |

Checks after the backport: docs/explorer/check.sh 0 errors (one warning,
bare-word Connect, as before), page-test 15 passed, map-faithfulness.py
regenerated.

## Revision 5 (branch paper-rev5)

State. Branch paper-rev5 from main (cde8ae7f). `make -C paper` builds
main.pdf and supplement.pdf, no undefined references, `make -C paper check`
passes. main.pdf has 29 pages (40 before): body pages 1 to 16, references
16 to 17, appendix 18 to 29 (12 pages). supplement.pdf has 7 pages.
Previews of pages 2 to 16 in .claude/notes/paper/preview/. Where older
sections disagree with this one, this one holds.

### Lock freedom in two styles (task 1)

The body counts in two ways only. Counters: each held end o has a counter
f(o) at run time, an action on o resets it to its reset value, every action
lowers the counters of the other held ends by one, a send lowers the
counters of the sent ends by one. The credit a of S_x^{a,m} is a static
lower bound on f(o), the tickets m are the reset value, N bounds the tickets
of a channel, the credit of a closure bounds the counters of its captured
ends that are not idle. Cost: ε of a term, [c] on arrows, and Δ − ε is Δ
with each credit lowered by ε (one line in def:lf-ann). §5 now opens with
the three ways to wait forever (ex:postpone, ex:delegate, rx-relink in the
supplement) and fig:lf-failures says which counter rule excludes each, then
def:lf-ann, ex:cycle with fig:lf-example, ranked worlds, def:counters, the
lock-free relation, the theorems. E-App shows the premise ε₂ ≤ a.

| body now | Rocq and map | kind |
|---|---|---|
| credit, a static lower bound on the counter | credit (`TSess`, `fle a f` in `Vty`) | renamed (gloss only) |
| tickets, the reset value of the counter | tickets, `refill` | renamed (gloss only) |
| def:counters "a term keeps its counters", F^N_β⟦Φ ⊢ σ ! d⟧ | fuel, `FuelE`, `Vfuel`, `fsem`, map block fu (now titled "Counters of a term") | renamed |
| cost bound d | frame (argument `c` of `FuelE`) | renamed, merged with the notion of cost in the text |
| "the counters" of a thread in def:lf-rel, E[κ_L] together with the counters | `SoupK` conjuncts `Erel` and `FuelE` | merged in the wording, two predicates in the formula |
| Δ − ε, "each credit lowered by ε" | aging, `tage`, `lage`, `thage`, rules Age-* | renamed, rules now Lower-Free, Lower-Credit, Lower-Idle, Lower-Arr |
| counter obligations, counters of values | `Fobl` (fuel obligations), `Vty` (values with fuel) | renamed |
| a spawn lowers no counter | `f_spawn` (the header comment of Fuel.v says minus one, the definition does not) | body follows the definition |
| E-App asks ε₂ ≤ a | `e_app` `fle c2 a1` | was missing in body and map, added |

Kept as they were, because a simpler form would be false or would hide a
second fixed point. The counters stay a predicate of their own beside E (the
map's fu-vs explains why one judgment with a counter component is a
different fixed point). Their steps lower the index at every step, while E
at κ_L keeps it at free steps. The symbol F of the counter relation is the
map's and clashes with the future F, it stays so that body and appendix
agree. tk(o) keeps its name.

### Colour (task 2)

map2tex.py colours every generated formula as notation.tex does: term
keywords \kw, Close and Skip \tyc, e v w in cTm, T U S in cTy (not in sub-
or superscripts, not the S of S^{N,W}), Γ Δ Σ Θ Φ as \cGamma \lenv \senv
\cTheta \cPhi, ⊗ ⊕ ⊸ □ ∃^l ∀ μ as \tyotimes … \tymu, α as \tvar, λ and
⟨ ⟩ in cTm. Words in \text, \textsf, \mathsf (other than keywords) and the
like are copied. Lock-free parts keep only their shade. Body figures: the
variables a, b, f, u, the ends o (\eo, new in notation.tex), channels c
(\ch) and constants k (\cst) are in cTm.

### Appendix and supplement (task 3)

The appendix keeps only the map blocks the body refers to and does not
state itself (APPENDIX in map2tex.py), each a numbered Definition or Figure
(rule groups) with its label app:<id> and Rocq links, no source lines. Left
out as duplicates of the body: syn-ends, syn-prims, syn-terms, syn-let,
syn-values, syn-labels, syn-points, syn-moves, ty-grammar, ty-heads, ty-ann,
w-world, w-order, t-judgment, t-lf-counters, t-lf-wf, v-rel, e-rel, e-bind,
p-rel, all theorems (th-*), alg-oracles, alg-thms. Moved to the supplement
(paper/supplement.tex, SUPPLEMENT in map2tex.py): every example listing and
the unreferenced blocks t-consts, t-lemmas, sr-reading, fu-vs, ty-kinds.
Every appendix item is referenced from the body (checked by script). The
cref names are Definition and Figure.

### The map follows the paper

docs/explorer/map.json: letters of the paper (type variables α, ordinals β
and γ, a β step keeps its letter, a thread label is ℓ), the lock-free blocks
and notes in the two styles (titles Counters of a term, Counter obligations,
Counters of values, Credits after a cost, The relation and the counters side
by side, rules Lower-*), renamed deviations with the Rocq names on fu and
t-agecap, readiness caption in the three cases of def:readiness, E-App with
ε₂ ≤ a. Scripts in .claude/notes/map-letters-paper.py, map-counters-cost.py,
map-counters-cost-2.py, map-readiness-wording.py, map-eapp-premise.py.
check.sh 0 errors, page-test 15 passed.

## Revision 4 (branch paper-rev4)

State. Branch paper-rev4 from main (ae11fd2b). `make -C paper` passes, no
undefined references, `make -C paper check` passes. 40 pages (41 before),
body pages 1 to 15 with the references from page 15 (16 before), appendix
from page 17. Previews of pages 2 to 15 in .claude/notes/paper/preview/.
Goal of the revision: the body defines less, stays true, and points to the
appendix for the precise form. Where the older sections below disagree with
this section, this section holds.

### Simplifications

| # | body now | the body omits | where the precise form is |
|---|---|---|---|
| 1 | conv:implicit keeps one bullet (disjoint contexts) and one sentence: a derivation uses only well-formed types and instances (contractive session types, payloads that mention only their own point variables) and binds only fresh point variables. E-Box reads `∀ s̄` | the separate bullets for contractivity, payload scoping, freshness, the set Inst | App. ty-session (contr), ty-payload (pscoped), r-boxes (sinsts, freshness) |
| 2 | def:side defines Γ ⊢_W x ≺ y in one sentence as the transitive closure of ≺_W and the facts of the instances in Γ, ≼ and Γ ⊢ C[x̄] in one sentence | the three closure rules Ord-World, Ord-Fact, Ord-Trans | App. t-contexts |
| 3 | a future F is a set of points, x ≺ F says x lies below each point of F, F ◁ H = F ∪ ap(H), x ≺ H and l ≼ H compare with each active point of H, the body of a closure runs under △u with x ≺ △u iff Γ ⊢ x ≼ u, one sentence says the general form also admits ⊥ and ⊤. den_Y(F) of def:sem-judgments is "the finite set F stands for when Y stands for △u" | F = X ∪ △v, X a finite set of bounds, the cases ⊥ ≺ F and ⊥ ∈ X ∨ v = ⊥ ⇒ x ⊀ F, the three cases of den_Y | App. t-contexts, t-side, sj-all |
| 4 | no η. Interface ends carry their annotations in Σ (o : S_x^{a,m}, shaded). Judgment Σ ⊢^N_W p : T. P-Term types t under Σ, Θ_B and asks tk(o) ≤ N on Σ. P-Connect asks tk(o) + tk(ō) ≤ N on Σ_C, and the dual interface carries credits and tickets of its own. Anatomy tables of def:proc-judgment and def:lf-ann lose the η row, conv:lf no longer names η, prop:flag-rejected quantifies over N and W, thm:lf-fundamental (2) and thm:lf drop η | the interface annotation η, tk_η, Σ^η | App. p-typing (η, P-Term.ann, P-Connect.tsum). Faithful because a derivation reads η only at its interface ends and restricted ends (ptyped_iann_local, p_connect_iann) |
| 5 | def:proc-judgment glosses the conditions in one item each: tfree T (built from ∗, boxes, products and sums, so its values hold no ends), pfree Σ (never both ends of a channel), pairs (Θ_B holds exactly the two ends of each channel of C₀ at dual points and protocols, shaded: credit equal to tickets, tickets summing to at most N), the dual interface and p₁ ∥_{Σ_C} p₂ (runs both, restricts the channels of Σ_C) in one item, tk(o) in one shaded item. tfree moved here from def:side | the formulas of pfree, chans, Σ̄, ∥_Σ, pairs, ends(C₀), the grammar 𝒯₀ | App. p-typing, ty-kinds |
| 6 | def:creation in words: new points of ῑ (base in ῑ) and old points, acyc (C among the new points plus program order x ≺ x⁺, x ≺ x̄⁺ has no cycle), conserv (each fact between old points that Γ, C(ῑ) derives, Γ derives alone), rankable shaded (C and program order well-founded on the new points, plus a relation pairing new points with finite nonempty sets of old points: each fact u ≺ y from a new to an old point pairs u with a set below y, each new point one step below a paired point gets a set whose points lie below points of the set above, each fact z ≺ s from an old point lies below a point of each set of s). def:ranked no longer restates rankable | tree(ῑ), ≺^ρ_C, the formulas | App. r-new, r-ex. Checked against acyc_new, tree_acyclic, new_step, conserv, new_ok, gen_new_rel in theories/static/Contexts.v |
| 7 | fig:typing-core shows E-App, E-Case, E-Send, E-Close, E-Link; fig:typing-orders shows E-New and E-Box. Captions gloss E-Abs (body under △u, l ≼ Δ), E-New-Field (channel at a field x·κ of any point, no facts), E-Force (points x̄ with Γ ⊢ C[x̄] and u[x̄] ≺ F), E-Open (opens a held existential, assumes its constraint, conservative over Γ), E-Pack. def:oracles names E-Force and E-Open with appendix references | the rules E-Abs, E-New-Field, E-Force, E-Open | App. r-fun, r-new, r-boxes, r-ex |
| 8 | §3 has two examples: ex:milner-typed and ex:cs. ex:forkjoin moved to §5.3 (sec:lf-ranked), where its slot uses it. ex:bit cut to the appendix with its slot kept | the listings of ex-bit and ex-forkjoin in §3 | App. app:ex-bit; ex:forkjoin in §5.3 |
| 9 | def:rel-anatomy says once that the side conditions of §3 are read in W with ≺_W for Γ ⊢_W, and states the convention that a closure or box owns exactly the ends in its body. The future of the relation is a finite set of points. Instances s̄ are well formed as in conv:implicit | the re-reading of W ⊢ u ≺ F, l ≼_W H, W ⊢ C[x̄]; the premises dom Θ = fends(e) of V-Arrow and fends(e) = ∅ of V-Box; Inst in V-Box | App. v-rel, syn-fends |
| 10 | def:readiness in words, three cases for terms (value; offers a held end and is at a link; offers a held end and the point of each offered end lies below the dual point of each held end it does not offer and each point of F) and three for processes (at a link; terminated with empty interface; offers an interface end and each interface end it does not offer has an offered end below its dual point) | the formulas with stable, offered, Θ|_A, Θ \ A, A ≺_W B | App. rd. Checked against ready_t, below_rest, ready_p, above_offered in theories/relation/Readiness.v, the case split is equivalent (a value has no step, and with nothing offered above_offered holds only for the empty interface) |
| 11 | def:proc-conds is two items in words, what a send (gives away the restricted ends Θ_e of its payload, each with its dual at dual point and protocol, the duals that stay join the interface as Σ_e) and a receive (adds the arriving ends, an arriving end that meets its dual sits at the dual point with a dual protocol, the channel becomes restricted and both ends leave the interface) do. The names opened, matches, closed, iface stay on the clauses and in Q-Send, Q-Recv | the four formulas | App. p-obls (send_split, recv_ok, recv_back, recv_env) |

### Corrections made on the way (needed to keep the body true after item 4)

- thm:lf-compose (2) now has the premise tk(o) + tk(ō) ≤ N for o ∈ dom Σ_C.
  `lf_p_connect` asks it, the earlier body left it out.
- def:lf-rel and def:lf-judgment now read the interface annotations: each
  end of Σ carries the point and protocol of its entry and at most the
  tickets of that entry (`sp_sigcap`). The earlier body said "at most
  ⌊N/2⌋ tickets", which is `Soup` and `lf_sem` (η fixed to N/2), while
  thm:lf-fundamental (2) cites `lf_fundamental`, whose conclusion is
  `lf_sems` with η. The definitions now cite `SoupK` and `lf_sems`.

### What could not be put in words faithfully in one phrase

- rankable needs three clauses about a relation of partner sets, so its
  shaded item in def:creation is one long sentence rather than one phrase.
- The ⊥ and ⊤ cases of futures stay a pointer ("the general form also
  admits the bounds ⊥ and ⊤"). The body reading "F is a set of points" is
  exact only for futures without bounds. △u is not read as a set: x ≺ △u is
  defined as Γ ⊢ x ≼ u, because "below every point above u" is weaker.

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

## E-New as one rule (2026-11-27)

The body shows E-New as the map's single rule: a fresh base ρ with facts C, or a field x·κ with no base and no facts, where the existential over no base is its body. The Rocq keeps two constructors, e_new and e_new_fld. In the field case acyc, conserv and rankable hold trivially (no new points, empty C), so the single rule is exact.
