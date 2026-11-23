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
