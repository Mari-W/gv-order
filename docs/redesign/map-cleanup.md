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
