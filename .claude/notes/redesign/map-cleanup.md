# Final map clean-up, 2026-11-24

Three passes over docs/explorer/map.json, as docs/redesign/map-cleanup-brief.md
defines them. Each pass appends its report here.

## Pass 1, Opus, faithfulness

Branch map-pass1 from redesign 33978aa. Content of map.json only. No change to
the tools, check.sh, index.html, ext/ or the Rocq. MathJax ran from a copy of
the gitignored tools/proof-map/node_modules of the redesign worktree.

### What I fixed, by block

Theorems.

- `th-terms`. The caption had the let lemma backwards. It said a term types
  wherever it types bound to $x$, which is the direction that fails. Now it
  says that a term bound to $x$ and returned types wherever the term types
  (`let_intro`). The row of `typed_pinst` gains the premise
  $\mathsf{world\_wf}\,W$, which the Rocq asks as `facts_const W`. The note
  `th.pinst` follows.
- `th-adeq`. The lock-free caption called `live_sub_df` a statement about a
  lock-free thread used by `th-terms`. It is a statement about closed
  processes in the semantic judgment at $\kappa_L$, under excluded middle and
  functional choice, with an end-free and box-free result type, and
  `th-terms` does not use it. The stale `usedIn` entry of `th-terms` is gone.
- Note `th.lf-tp-gen`. It claimed that lock-free adequacy establishes the
  three premises of `thread_progress`. Adequacy gives lock freedom and the
  lock-free process relation gives restricted links (`soup_links_restricted`).
  No internal divergence stays a hypothesis of `lf_thread_progress` since the
  force cost change.
- Note `th.let-var`. The converse of the let lemma also needs a well-formed
  world and contractive contexts (`let_elim`).
- 33 theorem notes said "Nothing. It is a definition." in their breaks field.
  They now say "Nothing. It is a theorem." The definition notes (`th.Erel`,
  `th.soup`, `th.pcomps` and the like) keep the old text.

Semantic typing.

- `ct-costs`. A cost table has four conditions, not three. $\kappa_L$ makes
  $\beta$ steps, creations, spawns and links free, not all internal steps,
  because a force costs one level. "A send costs nothing" now names
  $\kappa_{DF}$, because a send costs one level in $\kappa_L$.
- Note `ct.beta`. A force has its own cost, so the cost of $\beta$ no longer
  lists it.
- `soup`. The caption wrote the annotated configuration as $(q, K)$ while the
  table and `lfstate` have $(q, K, R_a)$. Notes `sp.owner` and `sp.fin` wrote
  $K(o)$ as a triple, `hold` has four fields.

Typing.

- `t-contexts`. The future may have no rest, `(X, None)` in `sfuture`. The
  formula and the caption now show $F = (X, \cdot)$.
- `t-agecap`. Age-Idle exists for end types of variables only (`age_idle` of
  `tage`). An end the term names directly ages by `thage`, which asks
  $c \leq a$ even for an idle protocol. The caption now says so. See question 1.
- Future without the $\bot$ flag. Notes `tj.F` (an argument $\bot$ "flag"),
  `side.act` ($F \neq (X, \bot)$), `E-App.fut1`, `E-Abs.lb` and `E-New.bot`
  still described the flag. A held value with hidden ends now sets the rest
  of the future to ${\uparrow}$, as `sf_unionb` does.
- Note `tp.sub-credit`. $\mathsf{new}$ and the actions return an end at credit
  equal to its tickets, not at credit $N$.
- Notes `ty.lbound` and `V-Ex.lb` used the retired name $\mathsf{new}_\ell$.
- Note `P-Term.wf`. The signature said $\mathsf{wf}\,W$ for the premise
  $\mathsf{ok}_N\,W$ (`wok`).
- `t-lf-wf`. The example said that E-New rejects the creation of the growing
  waiting chain. The Rocq rejects it by descent. Its box would have to call
  itself at a strictly lower dual point in each round (`rc_grow_no_model`).

Examples.

- `ex-cs`, `ex-cycle`, `ex-between`, `ex-many`, `ex-factory`, `ex-ring`. The
  deadlock-free badge cited only typing theorems. It now also cites the world
  lemma (`W_cs_wf` and so on) and says that deadlock freedom follows by
  `soundness_source` and is not stated as a theorem. See question 2.
- `ex-controller`. The lock-free badge cited `ctl_lftyped` only. It now cites
  `ctl_lock_free` as well.
- `ex-guard-neg`, `ex-link`. The lock-free badge claims "lock free", while the
  Rocq types the boxes or the link alone, with no closed program. The badge
  part now says what is proved. See question 4.
- `ex-guard-pos`. `spawn_loop_rejected` proves the step on aging
  ($a \leq a - 1$ fails), not the rejection of the program. The meaning and
  the badge now say that the rest is argued.
- `ex-flagpair`. The static rejection had no Rocq name and read as proved.
  The badge and the meaning now say it is argued, with `fp_unrealizable` as
  the mechanized part.
- `rx-chain`. The lead claimed the rejection "whatever premise E-New asks".
  The Rocq proves it for today's E-New. The general claim is now marked as
  argued. The badge part of `rx-chain` and of the lock-free verdict of
  `ex-forkjoin` said "E-New" and now names the descent of ranks.
- `ex-forkjoin`. A person's name in prose is gone.

Rule violations met on the way. Six metaphor warnings (carries, sees, sit)
and one pronoun ending are fixed.

### Recent merges, checked against the Rocq

Each item below matched the map, apart from the fixes above.

- examples/BranchExt.v. `bx_not_E`, `bx_rejected` with its conditions on Θ,
  the three arm typings, and the code of `ex-branch-ext`.
- examples/Descent.v. `rx_chain_rejected`, `fjr_lf_rejected` and their process
  corollaries, all under excluded middle and in contexts with a ranked model,
  as `rx-chain` and `ex-forkjoin` say.
- examples/PointReuse.v. `pr_round_typed`, `pr_term`, `pr_deadlock_free`, the
  code and the claim about a labelling of points.
- examples/Rejects.v and static/Skeleton.v. The three rejections hold at every
  finite bound, world and context, as the examples say. The code of the three
  examples matches the Rocq terms.
- examples/CopycatTwoN.v. `fwdq_term_fin` and `fwdp_expand2_fin` at $N \geq 4$.
- static/PointSubstTyped.v. `typed_pinst`, with the missing world premise
  added.
- static/ConnectNExact.v. The fold world of P-Connect$^n$ and the inclusion
  in the restricted join, in `p-typing` and note `P-Connect.n`.
- The rule changes since the audit of 2026-11-22. E-Send asks one premise
  $x \prec T$. P-Connect has no derived premises. $\mathsf{new\_ok}$ is
  $\mathsf{acyc\_new}$ plus the part for ranks, with the bridge condition of
  E-Open. A force costs one unit of effect and one level. A spawn costs
  nothing. One process judgment with `ptyped_sem` and `ptyped_ren`. The map
  agreed with each, apart from the $\bot$ flag notes above.
- Statements of every theorem row of the theorem section against v2, by
  name. The rows agree with the Rocq up to the merged notation of $\Theta$
  into $\Delta$, apart from the fixes above.

### What I could not verify

- The liveness files the brief names, `LivePConnect`, `LivePTerm` and
  `LiveGuardProc`, are not in v2. They live in theories/liveness of the old
  development. The map cites the v2 liveness results of compat/LiveDF.v and
  compat/LiveRules.v, which I left as they are.
- The formulas of `v-rel`, `e-obl`, `rd`, `p-rel`, `p-obls`, `fu`, `fu-obls`,
  `fv`, `sj-all` and the worlds blocks were not re-derived clause by clause.
  The audit of 2026-11-22 checked them, and no Rocq change since touches
  them except the force cost and the future, which I traced.
- About 350 notes outside the rule, theorem, fuel, obligation and soup groups
  (`V-*`, `rd.*`, `w.*`, `ty.*`, `sty.*`, `ord.*`, `proc.*`, `prop.*` and
  others) got only a search for stale names and retired notions.
- The code of the older examples against their Rocq terms. I compared the code
  of the `rx-*` examples, `ex-point-reuse`, `ex-branch-ext` and `ex-flagpair`.

### check.sh

Before, at 33978aa.

| step | errors | warn | info |
|---|---|---|---|
| 1 schema | 0 | 0 | 0 |
| 2 proof-map | 0 | 1 | 7 |
| 3 DF-LEAK | 0 | 0 | 0 |
| 4 writing | 0 | 65 | 0 |
| 5 MathJax | 0 | 0 | 0 |
| total | 0 | 66 | 7 |

After, at the tip of map-pass1.

| step | errors | warn | info |
|---|---|---|---|
| 1 schema | 0 | 0 | 0 |
| 2 proof-map | 0 | 1 | 7 |
| 3 DF-LEAK | 0 | 0 | 0 |
| 4 writing | 0 | 58 | 0 |
| 5 MathJax | 0 | 0 | 0 |
| total | 0 | 59 | 7 |

Warnings left, for pass 2.

- 44 every/any/all. Many are in argument notes whose definition does
  quantify, the rest are prose.
- 14 sentences over 35 words. Several are artefacts of the sentence splitter,
  which does not split at a period followed by the brace of `\inmode`. The
  caption of `th-chain` counts as one sentence of 149 words for that reason.
- 1 bare-word, "Connect" in `\textsf{P-Connect$^{n}$}` of `p-typing`. The
  checker reads the rule name as a product of variables.

### Questions for the author

1. Aging of idle ends. `tage` truncates the credit of an idle end type
   (`age_idle`), but `thage` asks $c \leq a$ of every end in $\Theta$, idle or
   not. An idle end the term names directly therefore cannot be held across a
   costly subterm, while the same end bound to a variable can. Should
   `thage` get the idle case too?
2. Six deadlock-free examples prove typing and the world lemmas but state no
   `*_deadlock_free` theorem. Should each get the one-line corollary of
   `soundness_source`, as ForkJoin, GenNew and PointReuse have?
3. Two rejections are partly argued. `ex-flagpair` has no static rejection
   theorem, and `ex-guard-pos` proves only the aging step. Should they get
   full rejection theorems in the style of Rejects.v?
4. The lock-free badge reads "statically typed, lock free". For
   `ex-guard-neg`, `ex-link` and `ex-forwarder` the Rocq types open terms and
   proves no lock freedom of a closed program. Should the page get a badge
   for typing alone, or should these examples get closed programs?
5. `ex-copycat` types the forwarder and the expansion at $N \geq 4$ but has no
   lock-free badge. Is a lock-freedom corollary for the expanded composite
   wanted?
6. The liveness port. Should the map wait for v2 versions of the liveness
   files the brief names, or are compat/LiveDF.v and compat/LiveRules.v the
   intended final form?

## Pass 2, Fable, content and prose

Branch map-pass2 from redesign 08bb92b, which includes pass 1. Content of
map.json only. No change to the tools, check.sh, index.html, ext/ or the
Rocq. MathJax ran from a copy of the gitignored tools/proof-map/node_modules
of the redesign worktree. `node tools/proof-map/test/page-test.js` passes
16 of 16 after the changes. Every faithfulness fix of pass 1 is kept.

### What I changed, by section

Markup that cost the deadlock-free reader sentences. Several captions nested
`\inmode{lf}{… \inmode{lf}{…} …}` and put deadlock-free sentences inside the
outer lock-free wrapper. The deadlock-free view lost three sentences this
way. `r-new` lost "The fundamental theorem proves E-New against O-New" and
"The constants have no entry for new", `th-sound` lost "The proof combines
the fundamental theorem and adequacy", and `th-adeq` lost "The proof reads
readiness". These sentences now stand outside the lock-free part, and each
caption has one flat `\inmode{lf}{…}` block at its end. The same flattening
removes the splitter artefact on `ty-grammar`, `w-world`, `r-new`,
`p-typing`, `sr-reading`, `sr-ord`, `ct-costs`, `sj-all`, `th-chain`,
`th-sound`, `th-adeq` and `th-terms`.

Cross-links to examples. The page resolves `[[example-id|words]]` to the
example, so every "the X example in the examples tab" is now a link. Blocks
`ty-session`, `w-wf`, `t-lf-wf`, `r-ex`, `r-new`, `p-typing`, `th-sound`,
`th-compose` and `th-terms`, and the notes `w.wok`, `lfi.link`, `new.acyc`,
`new.gen`, `new.ok`, `lfi.credit`, `lfi.hop`, `age.ctx`, `tp.sub-boxc`,
`E-App.fut1`, `E-New.wf`, `P-Connect.wf`, `th.fundamental`,
`th.lf-fundamental`, `th.soundness`, `th.soundness-source`,
`th.lf-soundness` and `th.cl2-needs`. The file name in `tp.sub-boxc` is
gone. The link from `p-typing` to the two-thread close is lock-free only,
because that example is lock-free only (question 6).

Syntax. `syn-labels` why, the sentence about fields read as "payload ends
and the continuations of a choice points", now "points of their own to
payload ends and to the continuations of a choice".

Types and worlds. `w-world` caption, "A strict world is any such order" is
now "has no further structure". `w-world` why split into four sentences.
`w-order` example, "in any state of its protocol" is "at each offset".

Typing. The section intro drops "The idea in one sentence." and says "dual
end" for "partner". `t-subs` caption said subtyping compares session types
by $\approx$. Sub-Sess uses `sequiv`, which is $\simeq$, as `ty-equiv`
already said. `t-lf-counters` caption named one of the two E-Link
inequalities, now both, as `e_link` asks. `r-new` why had three self-posed
questions ("Why not one rule." and so on), now statements. `t-subs` why,
"Subtyping exists for one reason." folded into the sentence that gives the
reason. `r-ex` and `p-typing` why, "Hiding buys" is gone.

Semantic typing. `sr-reading` caption merges the lock-free sentence on
ranked worlds into the sentence on strict worlds. `sr-ord` caption and why
say "one witness that serves each index" for "for all indices". `fu-vs`
why said the process relation "is where they meet", now "requires both".
`fu-obls` caption ends on "counters" instead of a pronoun.

Theorems. `th-chain` caption is one lock-free paragraph after the two
deadlock-free arrows and the sentence that names the proofs. `th-sound`
caption splits the lock-free sentence and states what the fair run gives,
each pending thread of a reachable configuration takes part in a later step
(`lf_soundness_padovani`, `lock_free_padovani`). `th-adeq` caption splits
the 39-word sentence. `th-terms` names the two rejections that use the
two-close lemma (`cl2_needs` in the flag, `fj_wait_needs` in fork-join).

Notes. 37 quantifier warnings rewritten, "any extension of $R$" to "an
extension", "ranges over all positions" to "the positions of the run",
"once for all indices" to "once and used at each index", and so on. Two
long notes split, `sty.contr.why` and `th.live-sub-df.meaning`.
`sty.contr.why` no longer calls the recursion bound of `unfoldS` "fuel",
which is the name of the lock-free predicate, and no longer hides that
sentence in the lock-free view. It now says "a number of unrollings bounded
by the size of the type", which is `unrN (sfuel s) s`.

Examples. `ex-gennew` named `gen_new` and `wf_new` in prose, two Rocq names
of which the deadlock-free view defines neither. The lead and the meaning
now describe the two conditions in words, and the part about the sets $Y$
is lock-free only. The meaning adds the fact the close of $d$ asks,
$\pi \prec \overline{\rho}$, which is what `te_rejected_wf_new` proves
underivable. `ex-copycat` meaning reordered, the ring rejection follows the
five facts, then the single expansion, the composite, the expansion between
two partners, and the acyclicity argument. `ex-link` linked E-Link to the
counters block, now to `r-act`. `ex-guard-pos` linked E-App to `r-act`, now
to `r-fun`. `ex-forkjoin` drops a parenthetical. `ex-cs` lead and
`ex-flagpair` meaning lose "all" and "any".

### Examples checked against the Rocq

I compared the code and the meaning of each example with the definitions
and theorem statements in its source files. ClientServer, Cycle,
FreshBetween, FreshMany, FactoryEx, GrowRing, LFClose, GuardEx (the four
boxes), cost/Forwarder (`fw`, `dead_thunk`, `S_fw`), LFController, SemBranch
(`sb_not`, `sb_flag`, `sbv_thread`), LFClientServerSplit, TreeTopo, LFLink,
Copycat with CopycatTwo and CopycatTwoN, Ring (`tA`, `tB`, `tC`, `tC'`),
ForkJoin (`wk`, `wkr`, `fct`, `fib`), SharedRoots, GenNew (`tu_main`,
`te_main`), SinstStuck. Each program in the map is the Rocq term up to the
re-binding sugar `let (a, ⟨b, b′⟩) = new a` for a creation at a field, which
the map writes as `let ⟨b, b′⟩ = new` with the placement in a comment, and
up to `recvclose` for a receive of unit followed by a close. The badges
agree with the theorems, including the bounds $N = 6, 4, 4, 8, 4, 8$ of the
six lock-free loops. The header of LFController.v says $N = 3$, the lemmas
use $6$, the map says $6$. Pass 1 compared the `rx-*` examples, PointReuse,
BranchExt and FlagPair.

### check.sh

Before, at 08bb92b.

| step | errors | warn | info |
|---|---|---|---|
| 1 schema | 0 | 0 | 0 |
| 2 proof-map | 0 | 1 | 7 |
| 3 DF-LEAK | 0 | 0 | 0 |
| 4 writing | 0 | 58 | 0 |
| 5 MathJax | 0 | 0 | 0 |
| total | 0 | 59 | 7 |

After, at the tip of map-pass2.

| step | errors | warn | info |
|---|---|---|---|
| 1 schema | 0 | 0 | 0 |
| 2 proof-map | 0 | 1 | 7 |
| 3 DF-LEAK | 0 | 0 | 0 |
| 4 writing | 0 | 0 | 0 |
| 5 MathJax | 0 | 0 | 0 |
| total | 0 | 1 | 7 |

Warnings left, and artefacts met.

- 1 bare-word, "Connect" in `\textsf{P-Connect$^{n}$}` of `p-typing`. The
  checker reads the rule name as a product of variables. A tool matter, not
  a content one.
- The sentence splitter of `tools/proof-map/lib/prose-rules.js` splits at a
  period followed by white space and a capital letter, `$` or `X`. It does
  not split before `\inmode` or before a `[[link]]`, so a sentence that ends
  in `.}` or is followed by a link counts together with the next one. Of the
  14 long-sentence warnings of pass 1, 8 were this artefact (`ty-grammar`,
  `r-new` twice, `p-typing`, `sr-reading`, `sj-all`, `th-chain`, one of
  `th-adeq`). I removed them by moving lock-free sentences to the end of the
  caption or by merging them into the preceding sentence, which also fixed
  the lost deadlock-free sentences above. The other 6 were real and are
  split.
- The 7 info lines are unchanged. Four uncovered constructors (`NField`,
  `LSess`, `tstep_head`, `sub_unit`), the unused note `sr.thunk`, the
  external `Acc`, and no stamped fingerprints.

### Questions for the author

Pass 1's six questions stay open. These are new.

1. Subtyping of session types. Sub-Sess compares by `sequiv` ($\simeq$),
   which sees the credits and costs inside payload types, while V-Sess
   relates ends up to `seqv` ($\approx$), which erases them. Two ends whose
   protocols differ only in a payload credit are related by the value
   relation but E-Sub cannot retype one as the other. Is the asymmetry
   intended, or should Sub-Sess use $\approx$ and compare the payload
   credits by a separate rule?
2. Interface tickets. P-Term gives each interface end $N/2$ tickets
   (`fhalf`), while a creation chooses $m_1 + m_2 \leq N$. A link of two
   interface ends therefore types at no even $N$, which is why the link
   example creates both channels inside the thread. Should P-Term let the
   interface ends carry chosen tickets, as creations do?
3. Field reuse. E-New-Field asks no freshness of the field, so two
   creations in one thread place channels at the same field $x\cdot 0$
   (point reuse example). Is this generality wanted, or should a field be
   creatable once per thread?
4. Fuel and renaming. Fuel quantifies over a renaming $g$ injective on the
   held ends, while the relation handles renaming by the fusion clause of
   $P$. Could fuel drop $g$ and let the lock-free process relation rename
   through fusion, which would make fuel the term relation without the
   ready clause and with counters?
5. Dependent choice in the headline. `lf_soundness_h` concludes
   `lock_free p`, a statement over weakly fair maximal runs, and such a run
   exists only under dependent choice (`lf_soundness_run`). Should the
   soundness block show the run form as the main lock-free result, so that
   the reader sees the non-vacuous statement first?
6. The two-thread close as a deadlock-free example. `cl_lftyped N` holds
   at each bound, $N = \infty$ included, yet `ex-close` is lock-free only.
   Showing it in both views would give the deadlock-free reader the smallest
   P-Term and P-Connect example, which the process typing block now links
   only in the lock-free view.
7. Three turnstiles for one idea. The map writes the semantic judgment
   $\vDash$, the judgment at $\kappa_L$ as $|\!\!\vDash$ and the lock-free
   process judgment as $\Vvdash$, next to $\vDash[\kappa]$ in `sj-all`.
   Should the two lock-free judgments be written as $\vDash[\kappa_L]$ and
   $\vDash^{N}$ over the one symbol?
8. The measure of lock-free adequacy. `th-chain` writes
   $\mu(t) = (\varrho(\mathsf{pt}\,o), f)$ with $\mathsf{pt}$ undefined on
   the page. It is the point $K$ records for $o$. Should the lock-free
   process relation block name that projection, or should the caption say
   "the point of $o$ in $K$" and drop the symbol?

## Pass 3, Opus, verification

Branch map-pass3 from redesign ab16e8b, which includes passes 1 and 2.
Content of map.json only. I re-read each of the 96 fields pass 2 changed
(`git diff 08bb92b ab16e8b`), in its deadlock-free projection and in full,
and checked the faithfulness changes against v2. MathJax ran from a copy of
the gitignored tools/proof-map/node_modules of the redesign worktree.

### What pass 2 got right

- The flattened lock-free blocks. In `r-new`, `th-sound`, `th-adeq`,
  `th-chain`, `th-terms`, `p-typing`, `sr-reading`, `sr-ord`, `ct-costs`,
  `sj-all`, `ty-grammar` and `w-world` each deadlock-free sentence of 08bb92b
  shows in the deadlock-free view, and no lock-free sentence leaks into it.
- The faithfulness changes. Sub-Sess asks `sequiv`, which `ty-equiv` writes
  $\simeq$ (`sub_sess`). E-Link asks both `lgt N a1 m2` and `lgt N a2 m1`
  (`e_link`). E-Link is a rule of `r-act` and E-App a rule of `r-fun`. The
  forwarder sentence of `ex-copycat` matches `fwd_expand`, a process that
  holds $\overline{o_1}$ types with the forwarder put behind that end. The
  words of `ex-gennew` match GenNew.v, the second program has the exits
  $\pi \prec \overline{\rho}$ and $\pi \prec \overline{\rho\cdot 0}$ and pairs
  $\pi$ with $\rho\cdot 1$ and $\rho$, and both programs type through
  `d_new_acyc` under $\mathsf{acyc\_new}$. `sty.contr.why` matches
  `unfoldS`, which unrolls `sfuel s` times.
- Each new `[[example-id|words]]` link resolves to the example the old text
  named. Links to lock-free-only examples (`rx-*`, `ex-close`) sit only in
  lock-free notes, lock-free blocks or `\inmode{lf}`.

### What I fixed

- `th-terms`. The deadlock-free caption said that the rejection of recursive
  fork-join uses the lemma on two closes. Fork-join types and is deadlock
  free in that view, and its rejection is lock-free only (`fjr_lf_rejected`).
  The deadlock-free sentence now names the self-computed flag and the
  creations with exits, the two users of `cl2_needs` in that view
  (`sbv_rejected`, `te_rejected_wf_new`). The fork-join use moved into the
  lock-free part.
- `th-sound`. Pass 2 wrote that each pending thread of a reachable
  configuration "takes part in a later step". `lf_padovani` is existential.
  Some configuration reachable from there has a step in which the thread
  takes part. The caption now says that.
- `th-adeq`. "Under the same hypotheses" followed a sentence about a
  well-founded static world, which `live_sub_df` does not ask. The caption
  names excluded middle and functional choice again.
- `ex-cs` lead and note `E-New.facts`. "Orders the points of each round at
  once" lost the point of the sentence, one constraint for infinitely many
  rounds. Both now say "its infinitely many rounds at once".
- `ct-costs`. The deadlock-free caption said "in each table", and cost tables
  exist only in the lock-free view. The words "in each table" are lock-free
  now.
- `ex-link`. "Its partner none" is now "its dual end none".
- `ex-gennew` lead. "A condition that keeps each fact of E-New inside the new
  tree" is now two sentences that name exits and say that E-New accepts them
  and the simpler condition rejects them.

I reverted nothing else. The prose rewrites and sentence splits of pass 2
keep their meaning.

### Page

`node tools/proof-map/test/page-test.js docs/explorer/map.json` passes 16 of
16. The light screenshots of `tools/proof-map/shoot.sh` at 1400 pixels show
each section in both modes. In the theorem section the deadlock-free view
shows no lock-free sentence, and the lock-free captions of soundness and
adequacy follow the deadlock-free ones as one coloured paragraph.

### check.sh

At the tip of map-pass3.

| step | errors | warn | info |
|---|---|---|---|
| 1 schema | 0 | 0 | 0 |
| 2 proof-map | 0 | 1 | 7 |
| 3 DF-LEAK | 0 | 0 | 0 |
| 4 writing | 0 | 0 | 0 |
| 5 MathJax | 0 | 0 | 0 |
| total | 0 | 1 | 7 |

The one warning is the bare word "Connect" in `\textsf{P-Connect$^{n}$}` of
`p-typing`, a checker artefact. The info lines are the four uncovered
constructors, the unused note `sr.thunk`, the external `Acc` and the
unstamped fingerprints. Tool matter for later: the sentence splitter of
tools/proof-map/lib/prose-rules.js does not split before `\inmode` or
`[[`, so it counts two sentences as one there.

### Open questions for the author, all three passes

The question of pass 1 on the liveness port is settled. compat/LiveDF.v and
compat/LiveRules.v are the current files, and the map cites them.

Typing rules.

1. Aging of idle ends. `tage` drops the credit of an idle end type, but
   `thage` asks $c \leq a$ of each end in $\Theta$, idle or not. Should
   `thage` get the idle case, so that an idle end named directly ages like
   one bound to a variable?
2. Subtyping of session types. Sub-Sess compares by $\simeq$, which sees
   payload credits, while the value relation uses $\approx$, which erases
   them. Is it intended that E-Sub cannot retype between two protocols that
   differ only in a payload credit?
3. Interface tickets. P-Term gives each interface end $N/2$ tickets, while a
   creation chooses $m_1 + m_2 \leq N$, so a link of two interface ends types
   at no even $N$. Should P-Term let interface ends carry chosen tickets?
4. Field reuse. E-New-Field asks no freshness of the field, so one thread may
   create two channels at the same field. Is that wanted, or should a field
   be created once per thread?
5. Fuel and renaming. Fuel quantifies over a renaming injective on the held
   ends, while the relation renames through the fusion clause of $P$. Could
   fuel drop the renaming and leave it to the lock-free process relation?

Rocq results for examples.

6. Six deadlock-free examples (`ex-cs`, `ex-cycle`, `ex-between`, `ex-many`,
   `ex-factory`, `ex-ring`) prove typing and the world lemma but state no
   deadlock-freedom theorem. Should each get the one-line corollary of
   `soundness_source`?
7. Two rejections are partly argued. `ex-flagpair` has no static rejection
   theorem and `ex-guard-pos` proves only the step on aging. Should they get
   full rejection theorems as in Rejects.v?
8. `ex-guard-neg`, `ex-link` and `ex-forwarder` type open terms and prove no
   lock freedom of a closed program, yet sit under a lock-free badge. Should
   the page get a badge for typing alone, or should these examples get
   closed programs?
9. `ex-copycat` types the forwarder and the expansion at $N \geq 4$ but has
   no lock-free badge. Is a lock-freedom corollary for the expanded
   composite wanted?
10. The header of LFController.v says $N = 3$ while `ctl_lftyped` and the
    lemmas use $6$. The map says $6$. Should the comment change?

Presentation.

11. Should the soundness block lead with the run form
    `lf_soundness_run`, which shows that a weakly fair maximal run exists
    under dependent choice, so that the reader sees the non-vacuous
    statement first?
12. `cl_lftyped N` holds at each bound, $N = \infty$ included, yet `ex-close`
    is lock-free only. Should it show in both views, as the smallest example
    of P-Term and P-Connect for the deadlock-free reader?
13. The map writes $\vDash$, $|\!\!\vDash$ for the judgment at $\kappa_L$ and
    $\Vvdash$ for the lock-free process judgment. Should the last two become
    $\vDash[\kappa_L]$ and $\vDash^{N}$?
14. `th-chain` writes $\mu(t) = (\varrho(\mathsf{pt}\,o), f)$ with
    $\mathsf{pt}$ undefined on the page. Should the lock-free process
    relation block define it, or should the caption say "the point of $o$
    in $K$"?
15. "Partner" occurs 123 times in map.json, for the thread or end on the
    other side of a channel ("partner bound $N - m$", "a new partner",
    "two partners $P$ and $Q$"). The forbidden list names "partner end".
    Should the remaining uses go too, in favour of "dual end" and "the
    other component"?

## Review pass, 2026-11-24

Branch map-review from redesign 56ecb51. Content of map.json only. No change
to the tools, check.sh, index.html, ext/ or the Rocq. I reviewed every field
that changed since 3ddf5c9 against the Rocq at 56ecb51 and the text rules,
and swept the whole map for the leftovers and words named in the brief.

### What I fixed

Partner. Every reader-facing "partner" is gone, about 170 occurrences in 160
sentences. An end on the other side of a channel is now "the dual end", the
thread there is "the thread holding the dual end" or "the other thread",
and a process on the other side of a cut is "the component". The note title
`fuse.partners` now reads "New dual pairs only on $D$" and `rd.below-held`
"Below the dual points of held ends". The thread named `partner` in the
code of `ex-flag` is now `other`. The phrase "the partner bound $N - m$ of
the other" now says "$N - m$ for the tickets $m$ of the other" (r-act,
fu-obls, F-Link, ann.tsum). Rocq names and the sym id `fuse.partners` keep
their names.

Undefined symbols.

- `th-chain` wrote $\mu(t) = (\varrho(\mathsf{pt}\,o), f)$ with
  $\mathsf{pt}$ undefined. It now writes $\mu(t) = (\varrho(x), f)$ and says
  that the ownership map $K$ of `soup` records the point $x$ of $o$ and the
  counter $f$ of $\overline{o}$. The row of `t-lf-wf`, the note
  `lfi.measure` and the note `th.lf-adequacy` use $x$ as well. This matches
  `we` and `fu` of soup/LFAdequacy.v.
- `ty-heads` defined ${\vartriangle}x = \{y \mid x \prec y\}$, a set read
  off the order, while `t-side` and the note `ty.up` define the comparison
  $x \prec {\vartriangle}u \iff \Gamma \vdash x \preccurlyeq u$, which is
  `rest_below` and asks more than the set reading. The formula now states
  the comparison $y \prec {\vartriangle}x \iff y \preccurlyeq x$ with
  ${\vartriangle}\bot = \mathsf{Point}$ and ${\vartriangle}\top = \varnothing$,
  and the caption follows.
- $\Gamma \vdash x \preccurlyeq y$ was used in 40 places and never defined.
  `t-contexts` now says that it means $x = y$ or $\Gamma \vdash x \prec y$,
  as `sle` states. `w-order` defined the reflexive order as $\preceq$ while
  every rule wrote $\preccurlyeq$. The definition, the note `ty2.le` and the
  notes `ty.arrow.lb` and `ty.ex.lb` now write $\preccurlyeq$.
- The ordinal index is $\alpha$ everywhere. Notes `rel.lfp`, `E.kripke`,
  `O-Beta`, `O-Spawn.thunk`, `O-Link.distinct`, `ct.take-pos`,
  `ct.give-pos`, `ct.spawn`, `ct.link` and `sj.at` still wrote $E_n$, $V_n$,
  $P_n$ or "level $n$". The convention row for $m, n$ no longer calls $n$
  the step index.
- `sp.rel` wrote $K_t(A)$ where the soup table writes $A|_t$.

Leftovers of removed notions.

- Restriction in process typing. The sentence on the rules that restrict
  each conclusion world is gone from `p-typing` why, `P-Connect.wf` why and
  `th.ptyped-apart` why, and the second example of `w.restrict` with its
  `hides` deviation. `P-Term.wf` no longer speaks of restrictions of the
  world. The sources drop `rptyped_ptyped`, `ptyped_rptyped`,
  `connect_hidden`, `hides`, `hides_restrict` and `swrestrict_wok`, which
  only that prose cited. `W|_S` stays, because the join lemma `w.R7` uses
  it.
- "The annotations $\eta(o) = (\lfloor N/2 \rfloor, \lfloor N/2 \rfloor)$
  give back the earlier rule" (p-typing, LF) cited a past design. It now
  says that under this annotation the ticket premise of P-Connect holds at
  each cut (`p_connect_half`).
- Bridges. The deviations of `r-ex`, `E-Open.cons` and `r-new` defined the
  word "bridge". They now say that the rules check the finite form
  `cons_open` of $\mathsf{conserv}$, describe the paths `bridge_at` by the
  Rocq name, and cite `cons_open_iff`.
- Model. The deviations of `sj.sw` and `sp.allR` spoke of "worlds of the
  relation that model $W$". They now name the Rocq type `world` and
  `wmodels`. No R world, $\vDash^{h}$, hidden world, root, ${\uparrow}$ or
  $F_u$ case split is left. "Transfinite Iris assumes it in its model" in
  `th.em` is about the Iris model and stays.
- `ty.heads` deviation said "The paper writes". It says "The map writes".

DF view. I stripped `\inmode{lf}{…}`, `\inmodeplain{lf}{…}`, `\annot`,
`\annraw` and `\annp` from each DF-visible string, of the blocks, the
examples and every note that a DF-visible formula, table or signature
reaches, and searched the rest for credits, tickets, costs, $\eta$, $N$,
ranks, strict and ranked worlds, $\mathsf{new\_ok}$, $\mathsf{gen\_new}$
and $\mathsf{ok}_N$.

- $N$ leaked in `t-judgment` caption, `ex-ring`, `ex-forkjoin`,
  `ex-gennew` ("at $N = \infty$"), `th-sound` formula and the notes
  `th.connect-n`, `th.pcomps` ($\mathsf{comps}_{\infty}$,
  $\mathsf{comps}_N$), `tp.pjudg`, `tp.sinsts`, `E-New.dual`, `E-New.wf`,
  `P-Connect.wf`, `P-Term.wf` and `P-Term.pairs` (the tickets $m, m'$ and
  $m + m' \leq N$). Each is LF-only now. The args $N$, $m_1, m_2$, $m, m'$
  and $\varepsilon$ of these notes carry `modes: ["lf"]`.
- The cost $\varepsilon$ of the judgment and the aging $\Delta - \varepsilon$
  leaked in the signatures of `E-Abs.body`, `E-App.fut2`, `E-Pair.fut2`,
  `E-Case.branches`, `E-Box.body`, `E-Open.body`, `tp.letp`, `tp.letu` and
  `tp.vdash`. The meanings of `tp.letp` and `tp.letu` were LF-only, so the
  DF reader saw an empty meaning. Both now have a DF text.
- `th.connect-n` had its whole meaning inside `\inmode{lf}`, so the DF
  theorem row opened an empty note.
- Ranks leaked in `E-New.field` breaks, `O-New.grow` (meaning, why,
  breaks, example, arg) and `w.grow` breaks. Each has a DF text now.
- $\mathsf{new\_ok}_N$ and $\mathsf{wf}$ leaked in the titles and
  signatures of `E-New.wf`, `E-New.pos`, `P-Connect.wf` and `P-Connect.n`.
  They now show $\mathsf{acyc\_new}$ and $\mathsf{cons}$ in DF. The
  signatures of `P-Connect.wf` and `P-Connect.n` wrote $\mathsf{wf}$ in LF
  as well, where the rule asks $\mathsf{ok}_N$. They now write
  $\mathsf{ok}_N$.
- `tp.lift` signature showed the two annotation components in DF.
- $\eta$-expansion in `ex-copycat` and `syn.op` used the letter of the
  interface annotations. Both now say eta-expansion, as `t-consts` does.

Other.

- `ty-equiv` said that subtyping compares session types by $\simeq$. It
  compares them by $\approx$ in DF and by $\sqsubseteq$ with annotations,
  as `t-subs` states.
- `ex-copycat` LF. The lock freedom of the expanded composite
  (`fwdp_expand2_lf`) takes excluded middle and functional choice. The text
  says so.
- `ann.tsum` read "a bound read off its own type" after the rewording,
  which now names the type of the first end.

Checked and left as they are. Idle ends of $\Theta$ age freely (`t-agecap`,
`age.idle`). The payload variance of Sub-Sess matches `crT` and `sub_step`
of types/Types.v. E-New and its field case are one rule with the triple
$(p, \bar\rho, C)$ (`e_new`, `e_new_fld`). The interface annotations,
`ptyped_iann_local` and `p_connect_iann` match the LF caption of
`p-typing`. P-Term concludes at $W$ and P-Connect at $W_1 \sqcup W_2$, the
fundamental theorems read the derivation's world, and `ptyped_apart` and
`ptyped_ren` are stated as in static/Hiding.v. The six DF corollaries,
`fwdp_expand2_lf` and the guard-pos rejection carry the right names.

### Hidden ends and points, not changed

"Hidden" occurs in `ty-heads` (caption and deviation), `w-world` why,
`t-judgment` (caption and deviation), `t-side` deviation, `r-new` (caption
and why), `ex-factory` lead, and the notes `ty.arrow` (arg $l$),
`ty.arrow.lb` (arg), `ty.ex` (arg $\bar\iota$), `ty.heads` (why and
deviation), `ty.lbound`, `side.lb` deviation, `E-Abs.lb` (arg),
`E-App.fut1`, and `E-Send.heads` (meaning, why, breaks, deviation).

### Questions for the author

1. Annotations in the DF view. `ty-equiv` (caption and why), the title of
   `sty.seqv`, `ty2.stydf`, `v-rel` ("up to annotations"), `V-Sess` (arg
   7), `tp.sub-sess` and `P-Connect.cut` speak of annotations to the DF
   reader, who has none. In DF, $\approx$ and $\simeq$ coincide. Should the
   DF view drop the distinction and the word?
2. `ct-costs` lists $\kappa_L$ in `introduces`, and the list has no mode,
   so the DF reader sees it. `w-wf` has the title "Consistent and
   well-founded worlds" in both views. Should titles and `introduces` take
   modes, or should these entries change?
3. static/Hiding.v keeps the restricting judgment `rptyped` with
   `rptyped_ptyped` and `ptyped_rptyped`, and `hides`, `connect_hidden` and
   `swrestrict_wok` serve only them. The map no longer cites them. Should
   the Rocq keep them as a reference?
4. The header of lockfree/Criterion.v says that the measure is the pair of
   the tickets left and the counter of the partner end. soup/LFAdequacy.v
   uses the counter alone under the rank, and the map follows it. Is the
   Criterion.v comment stale?
5. `source.revision` in map.json still says 9d2c6d4. Should it name the
   revision the map was last checked against?

### Checks

`docs/explorer/check.sh` ends with 0 errors and the one known warning
(bare-word Connect in p-typing). The writing step has no warning.
`tools/proof-map/test/page-test.js` passes 15 of 15.

## Faithfulness check, 2026-11-24

Branch map-faithful from redesign dd71273, after the Fable pass. The
question was whether the map says exactly what the Rocq at HEAD defines
and proves, with each difference recorded as a deviation whose reason is
correct. I read each block and theorem row the Fable pass touched, the 61
notes it changed, the eight examples it changed, and the statement of
each theorem row by name against v2/. No design change, and no Rocq change
apart from one stale comment.

### The bounds reading, case by case

The reading is exact for the checks it claims. With $\bot \prec u$ and
$u \prec \top$ for each bound $u$, $\mathsf{ap}(T)$ is `heads T` plus
$\bot$ when `hbot T` holds plus $\top$ for each closure or existential at
`LNone`. $X$ is the Rocq set plus $\bot$ where `sf_unionb` sets `RAll`,
plus $\top$ where `lb_heads LNone` adds nothing.

- `ub_below_u`. `UNone` is $\bot \prec F$, true for each future. `UTop`
  asks `F = (∅, None)`, and $\top \prec X \cup {\vartriangle}v$ holds iff
  $X \subseteq \{\top\}$ and $v = \top$. A map future with $\bot \in X$ is
  a Rocq future with `RAll`, so both sides agree. `UPt x` is `ub_below_s`.
- `ub_below_s`. `None` is $\bot$, true. `Some x` asks $x$ below each point
  of the set and `rest_below`. In the map $x \prec \top$ holds, and
  $x \prec \bot$ fails exactly where the Rocq has `RAll`. $x \preccurlyeq v$
  is `sle`, false and true for `RAbove u`, `RAll` and no rest.
- `below_ty` is `hbot T = false` and $x$ below each head, which is
  $x \prec \mathsf{ap}(T)$.
- `lbx_below_h`. `LBot` is $\bot \preccurlyeq \cdot$, true. `LNone` asks no
  head and no `hbot`, which is $\top \preccurlyeq y$ only for $y = \top$.
  `LPt x` asks `sle` for each head and no `hbot`, and $x \preccurlyeq \bot$
  fails.
- E-App, second premise, holds `sf_unionb F (lb_heads lb) (lb_bot lb)`.
  At `LNone` the map adds $\top$ to $X$, and $\top \prec \top$ keeps
  $\top \prec F \cup \{\top\}$ equal to $\top \prec F$.
- The relation (`ub_ltu`, `lbx_le`) compares bounds with sets of points,
  and the reading agrees there too.

Where $\bot \prec \bot$ and $\top \prec \top$ must not hold. The worlds
(`sacyc`, `swf`, the record `world` with `w_ord_irrefl`), readiness
(`below_rest`, `above_offered`) and the futures of the relation
(`gset point`) compare points only, and the map writes them with point
letters. The caption of ty-heads and the note side.top said, however,
that the orders $\prec_W$ and $\Gamma \vdash$ themselves extend to bounds,
which reads as if $\prec_W$ were no longer strict. Both now say that a
comparison of a bound with a point or a set reads the order extended to
bounds, that the extended order is no strict order, and that the
conditions on worlds and readiness compare points. Ord-Trans through
$\bot$ or $\top$ yields no new fact between points, so the order judgment
between points is unchanged.

One place was not equivalent. sj.den wrote
$\mathsf{den}_Y(X \cup {\vartriangle}v) = X \cup Y$. That puts $\bot$ and
$\top$ into a semantic future, and for $\bot \in X$ with $v$ a point it
restricts $Y$ to points above $v$, where the Rocq (`sf_den`, `rest_ok` at
`RAll`) takes each finite $Y$. Fixed to $(X \cap \mathsf{Point}) \cup Y$
with $Y$ unrestricted when $\bot \in X$. The deviations of sj.den and
t-contexts say so.

The t-side caption said that $\top \prec F$ holds when "$F$ has no point"
and $v = \top$. With $\bot \in X$ that is false. It now says
$X \subseteq \{\top\}$.

### Removed Rocq results

No map citation names a removed result (check.sh), and no prose relies on
one. A search for the restricting judgment, `hides`, `connect_hidden`,
`join_vis`, `lexlt`, the swrestrict lemmas, "hidden" and the old measure
of Criterion.v finds nothing.

### Theorem rows by name

Each row matches its Rocq statement, hypotheses included, except these,
now fixed.

- th-chain. The row of `live_fundamental_ranked` lacked
  $\mathsf{world\_wf}\,W$ and $N \in \mathbb{N}$, and the row of
  `lf_fundamental` lacked $N \in \mathbb{N}$.
- th-compose, `lf_p_term`. The Rocq asks `sworld_wf W`, which neither the
  row nor $\mathsf{pterm}_N$ stated. Added to the row and to the note.
- p-typing, P-Term. `p_term` asks `sworld_wf W ∧ wok N W`. The premise
  showed $\mathsf{cons}\,W$ (or $\mathsf{ok}_N\,W$) alone, while its note
  spoke of a well-formed world. Premise, title and signature now read
  $\mathsf{world\_wf}\,W \land \mathsf{cons}\,W$. The title had shown
  $\mathsf{ok}_N$ in the deadlock-free view as well.
- `cl2_needs` and `typed_pinst` ask `facts_const W`, the map
  $\mathsf{world\_wf}\,W$. These are the same condition. `sworld_wf` has
  the one field `wf_facts`, whose statement is `facts_const`. Not changed.

Checked and correct: `soundness`, `live_soundness`, the three n-ary
soundness theorems of ConnectN.v and LFConnectN.v, `lf_soundness_run`
(EM, DC, FC, the run from `fair_run_exists_proc`), `lf_soundness`,
`lf_soundness_padovani`, `lock_free_padovani`, `fundamental_proc`,
`live_fundamental_proc`, `lf_fundamental`, `adequacy`, `adequacy_sw`,
`live_sub_df`, `lf_adequacy`, `lf_thread_progress`, `thread_progress`,
`lf_sems_adequacy`, `sem_p_term`, `sem_p_connect`, `sem_p_connect_sw`,
`lf_p_connect`, `lf_soup_term`, `ptyped_apart`, `ptyped_ren`, `typed_ren`,
`conservative`, `typed_dftyped`, `soundness_source`, `lf_soundness_source`,
`fundamental`, `fundamental_typed`, `live_fundamental`,
`live_fundamental_typed`, `Erel_bind`, `cost_fundamental`,
`fsem_of_cost`, `let_intro`, `let_var_counter`.

### The items of the Fable pass

- Turnstiles. $\vDash[\kappa_L]$ for `⊫` and $\Vvdash^N$ for `lf_sem` are
  faithful. The deviations on sj.sw and sj.term name $\kappa_L$ and showed
  in the deadlock-free view. They carry mode lf now. sp.lfsem did not
  mention the annotations $\eta$ of `lf_semk`. Its deviation does now.
- `lf_soundness_run` row and note. Correct.
- Typing-only badges. Correct for ex-guard-neg. The lead of ex-forwarder
  still said "is lock free" next to a badge that proves no closed program.
  It now says that the thread types in the lock-free judgment and has fuel
  at each bound, which `fw_ptyped` and `fw_fsem` state.
- ex-close in the deadlock-free view. `cl_dftyped` and `cl_deadlock_free`
  match.
- r-new. $\mathsf{rankable}_\Gamma(\rho, C)$ is `∃ Sr, gen_new_rel W Γ C Sr`
  clause by clause, and restricting $\mathcal{S}$ to tree points loses
  nothing. The caption said that a creation never orders two old points.
  `cons_open` and the second clause of `gen_new` allow such a fact when
  $\Gamma$ derives it, so the caption now says "orders two old points only
  as $\Gamma$ already does".
- v-rel measure. The deviation of rel.vsize still spoke of "the formula"
  and of a symbol $\mathsf{measure}$, neither of which appears any more.
  Rewritten after `RelA`, `Vtop` and `tsize`. Its why was empty in the
  deadlock-free view and has a deadlock-free sentence now.
- ord.fix said that $V$, $E$, $P$ and fuel are each one family. In the Rocq
  $V$, $E$ and $P$ are one family (`RelA` over `larg`) and fuel a second.
  Fixed, and the deadlock-free view shows the first sentence.

### The deadlock-free view

I resolved each string a deadlock-free reader reaches to its deadlock-free
form (blocks, examples, deviations without mode lf, and the 386 notes
their symbols reach, closed under the symbols of notes) and searched for
lock-free vocabulary and for fields that come out empty.

- $\simeq$ appeared in eleven deadlock-free strings (E-Box.inst,
  E-Sub.contr, sty.contr, sty.mu, tp.sinsts, tp.sub-boxc, tp.sub-sess,
  tp.sub-teq), while the deadlock-free ty-equiv defines only $\approx$. On
  the types of that view the two coincide, so these strings show $\approx$
  there and $\simeq$ in the lock-free view.
- Deadlock-free content inside lock-free markup, so that the deadlock-free
  reader saw nothing. The meaning of th.soundness, the why of
  V-Arrow.level, the why of O-Send.payload, the first half of the example
  of sub.tsub, the meaning of ev.admin and the why of ord.fix. Unwrapped.
- The signatures of V-Arrow.level and O-Recv.forall showed
  $\beta + \kappa \leq \alpha$ in the deadlock-free view against the
  meaning $\beta < \alpha$. They switch by mode now.
- syn-terms said "no annotation" in the deadlock-free view. Moved to lf.
- E-New.bot said that no point of the context is related to $\rho$. $C$
  may relate the tree to context points. It now says that no fact of
  $\Gamma$ mentions a point of the tree.

### The Rocq

lang/Process.v. The comment above `ev_admin` said that administrative
events cost nothing in the live table. A force costs one there. The
comment now says that each of them but a force costs nothing. Comment
only.

### Remaining gaps

- Twenty-two notes have a field whose text is lock-free only, for example
  ct.new.why, rel.lfp.why, tp.vdash.why and V-Sess.why. The page tests the
  raw string before it resolves the mode, so the deadlock-free view shows
  the heading of such a field over an empty body. The fix belongs in `row`
  of tools/proof-map/page/index.html, outside this pass.
- The theorem rows write $\vdash^{N}_W$ and leave $\eta$ implicit. This is
  recorded on sp.lfsem, not on each row.
- `cl_dftyped` and `cl_lftyped` take an unused argument `x : point`.

### Questions

1. P-Term now shows $\mathsf{world\_wf}\,W \land \mathsf{cons}\,W$. Should
   well-formedness instead be folded into $\mathsf{cons}$ and
   $\mathsf{ok}_N$ on the map, with a deviation, to keep the rule short?
2. The page shows empty field headings in the deadlock-free view. Fix the
   page, or give each such note a deadlock-free sentence?
3. Should `cl_dftyped` and `cl_lftyped` drop their unused `x`?

### Checks

`docs/explorer/check.sh` ends with 0 errors and the one known warning
(bare-word Connect in p-typing). `tools/proof-map/test/page-test.js`
passes 16 of 16.
