# Fable pass over v2 and the map, 2026-11-24

Approved by the author on 2026-11-24. Branch fable-final from redesign
9497061, which equals main. Eight commits, nothing pushed, nothing merged.
No typing rule, no clause of the relation and no theorem statement
changed, apart from the removed dead results listed below. No Admitted, no
Axiom, no new Parameter. `make` builds, `make check` reports 273 of 273
closed (275 before, minus 4 dead results, plus 2 new ones), `make test`
passes, `docs/explorer/check.sh` ends with 0 errors and the one known
warning (bare-word Connect at P-Connect), and
`tools/proof-map/test/page-test.js` passes 16 of 16.

## 1. The map, by section

### Types and worlds

- `ty-heads`, now "Bounds and active points". The bounds $l$, $u$ and $v$
  range over $\mathsf{Point} \cup \{\bot, \top\}$, and each order the
  rules read extends to them by $\bot \prec u$ and $u \prec \top$ for each
  bound $u$, $\bot$ and $\top$ included. With that, $\mathsf{ap}$ is a set
  of bounds with no case split, $\mathsf{ap}(T \multimap^{u}_{l} U) =
  \mathsf{ap}(\exists^{l}\bar\iota.\,C.\,T) = \{l\}$, and the rest of a
  future is read by one clause, $u \prec {\vartriangle}v \iff u
  \preccurlyeq v$. The old formula had three clauses for ${\vartriangle}$
  and a two-case definition of $\mathsf{ap}$ at a closure. The deviation
  records the reading of `hbot` ($\bot \in \mathsf{ap}$), `LNone` ($\top
  \in \mathsf{ap}$) and the six constructors of `lbound` and `ubound`, and
  says that each check agrees with the Rocq case by case. I checked the
  seven Rocq cases of `ub_below_u`, `ub_below_s`, `rest_below`, `below_ty`
  and `lbx_below_h` against the one comparison, including the corner $u =
  \top$ with a closure at `LNone` in the held context, which is why
  $\top \prec \top$ has to hold.
- `ty-equiv`. The deadlock-free view shows one equivalence $\approx$ and
  $\mathsf{sdual}$. The lock-free view adds $\simeq$ and $\approx$ as
  $\simeq$ after $\mathsf{sty\_df}$. Deviation on the block, notes
  `sty.seqv`, `sty.sdual`, `tp.sub-sess`, `V-Sess` and `P-Connect.cut`
  reworded so that the word annotation appears in the lock-free view only.
- `w-wf` is "Consistent worlds", and the note `w.R7` "Consistent joins".
  BLOCKS.md follows.
- The level letter is $\beta$ in every clause. `v-rel`, `e-obl`, `p-obls`
  and `fv` wrote $j$ in V-Arrow, O-Recv, Q-Recv, FV-Arrow and FV-Box next
  to $\beta$ in the same rule.
- `v-rel` no longer shows the recursion measure $(\alpha, \mathsf{size}\,T)$
  and the two size clauses in the formula. The caption names the measure
  and hovers `rel.vsize` and `sr.size`, whose signature now indexes $V$ by
  an ordinal.

### Typing

- `t-contexts`. The future is $F = X \cup {\vartriangle}v$ with $X$ a finite
  set of bounds. A held value at the lower point $\bot$ puts $\bot$ into
  $X$, where the Rocq sets the rest to `RAll`. Both make each $x \prec F$
  fail. Deviation reworded.
- `t-side`. Three clauses in place of six. $u \prec X$ pointwise, $u \prec
  X \cup {\vartriangle}v \iff u \prec X \land \Gamma \vdash u \preccurlyeq
  v$, and $l \preccurlyeq X$ pointwise, the rest unchanged. The caption
  states the three consequences a reader needs, $\bot \prec F$ always,
  $\top \prec F$ only for a future without points and $v = \top$, and
  $x \prec F$ fails when $\bot \in X$ or $v = \bot$. The deviation lists
  the Rocq cases and their reading.
- `t-judgment`, `r-fun`, `r-boxes` captions and the notes `ty.up`,
  `ty.heads`, `ty.lbound`, `ty.ubound`, `side.ub`, `side.lb`, `side.top`,
  `side.act`, `E-Send.heads`, `tj.held`, `tj.F`, `ctx.fvarF`, `E-Abs.lb`,
  `E-App.fut1`, `E-New.bot`, `E-Box.body`, `V-Arrow.lb`, `V-Arrow.ub`,
  `V-Ex.lb`, `ty.arrow`, `ty.arrow.lb`, `ty.ex`, `ty.ex.lb` follow the new
  reading. No reader-facing text says "hidden end" or "hidden point" any
  more. The lower point $\bot$ is "no bound", and ends behind it are "at
  points the context cannot name". Existentials "abstract" their points
  (`w-world`, `r-new`, `ex-factory`).
- `r-new`. The part for ranks is one named premise,
  $\mathsf{rankable}_{\Gamma}(\rho, C)$, next to
  $\mathsf{wf}(\prec^{\rho}_{C})$. The three conditions with the relation
  $\mathcal{S}$ moved into the signature of the note `new.rank`, whose
  deviation names `∃ Sr, gen_new_rel W Γ C Sr`. The main formula lost
  four lines.
- `r-fun`. The hover `E-Abs.cap` ("Capture as aging") sits on the
  lock-free part $- a$ only, so the deadlock-free reader no longer opens
  it from $\Delta$.
- `p-typing` links the close example in both views.

### Semantic typing and theorems

- One turnstile for the judgment at $\kappa_L$. The eleven
  $|\!\!\vDash$ are $\vDash[\kappa_L]$, the instance of the family
  $\vDash[\kappa]$ that `sj-all` defines. Deviations on `sj.term` and
  `sj.sw` record the Rocq turnstile `⊫`. The lock-free process judgment
  keeps $\Vvdash^{N}$, which is the Rocq notation of `lf_sem`, and
  $\vDash^{N}$ stays the cost judgment `csem` (`cs.csem`). See question 1.
- `th-sound`. The lock-free rows open with `lf_soundness_run`, excluded
  middle, dependent choice and functional choice giving lock freedom and a
  weakly fair maximal run. `lf_soundness` follows, then the n-ary form and
  the reachability form. The separate row `fair_run_exists` is folded into
  the new note `th.lf-soundness-run`, which cites `fair_run_exists` and
  `fair_run_exists_proc`. The caption says that dependent choice serves
  the run alone.
- Hovers of the deadlock-free view no longer show the general cost table.
  `V-Unit`, `V-Sess`, `V-Prod`, `V-Sum`, `th.Erel`, `th.Prel`,
  `th.sem-p-term` write $[\kappa]$ in the lock-free view only, and the
  argument $\kappa$ of the `ct.*` notes has mode lf. `ty.tfree.why` and
  `ty-kinds.why` hide the sentence on aging, and the deviation of
  `w.models` names `swf` in the lock-free view only.

### Examples

- `ex-close` shows in both views, with the new results `cl_dftyped` and
  `cl_deadlock_free` (section 2) behind a deadlock-free badge. The code
  comments no longer name $N$.
- `ex-guard-neg` and `ex-forwarder` carry a typing-only badge. The field
  `claim: "typed"` of `x-gv-accepts` makes the badge read "statically
  typed" without "lock free", and the part says that no closed program
  is proved. `ext/gv-page.js` renders it and `ext/gv-check.js` accepts
  only this value. These are the only tool changes.
- The four `rx-*` examples call their program deadlock free in the lead.
  They now carry a deadlock-free badge whose part and Rocq field say
  "argued, no Rocq proof", as `ex-flagpair` does.
- `source.revision` is deffac9, the Rocq tip the map was checked against.

### The deadlock-free view by hand

A script stripped `\inmode{lf}`, `\inmodeplain{lf}`, `\annot`, `\annp` and
`\annraw` from each string a deadlock-free reader reaches, the blocks and
examples without mode lf, their deadlock-free variants, and the 386 notes
their symbols open, closed under the symbols of those notes. It searched
for credit, ticket, cost, $\varepsilon$, $\eta$, rank, strict, annotation,
$\kappa_L$, $\mathsf{wf}$, $\mathsf{ok}_N$, well-founded, lock free, fuel,
counter, $N$, $\mathsf{new\_ok}$, $\mathsf{gen\_new}$ and aging. What it
found and I changed is listed above. What stays is a deadlock-free notion
with the same word: the costs of $\kappa_{DF}$, the strict order of a
consistent world, well-founded ordinals and the well-founded world of
recursive fork-join, and the letter $n$ of the n-ary connect.

## 2. The Rocq

- static/Hiding.v, 687 to 284 lines. Removed the restricting judgment
  `rptyped` with `rptyped_ptyped` and `ptyped_rptyped`, `hides`,
  `hides_restrict`, `hides_ren`, `connect_hidden` with the section
  `join_vis` (`vis_side`, `side1`, `side2`, `shared_vis`, `cross`,
  `join_vis`), `join_sub`, `iface_connect`, `pt_ren_fix_croot`,
  `croot_in_union_l`, `croot_in_union_r`, `croot_in_same`,
  `croot_in_mono`, `swrestrict_lt_in`, `pt_consts_dual`,
  `swrestrict_empty_bare`, `swshared_ren`, `set_map_inter`,
  `swrestrict_ren_facts`, the composition lemmas `bcs_ren_comp`,
  `ren_comp_mut`, `ty_ren_comp`, `senv_ren_comp`, `fact_ren_comp`,
  `sw_ren_comp`, and the constants lemmas `pt_consts_ren`,
  `env_consts_ren`, `ren_consts_mut`, `senv_consts_ren`, `iface_ren`.
  Nothing outside the file used them, and inside the file only the
  removed results did. Kept, because examples or ConnectN use them:
  `swrestrict_iff`, `sw_lt_by`, `senv_pt_iface`, `typed_ren`, the
  renaming lemmas of interfaces, `sw_lt_facts`, `swf_sub`, `sacyc_sub`,
  `wok_sub`, `wok_join_bare_l/r`, `cb_id`, `cb_avoid`, `ptyped_ren`,
  `ptyped_ren_fix`, `ptyped_side`, `ptyped_apart`. The header describes
  the file as it is now.
- static/Typing.v. `swrestrict_swf`, `swrestrict_sacyc` and
  `swrestrict_wok` removed, nothing used them. The comment above `ptyped`
  no longer cites `rptyped_ptyped`.
- lockfree/Criterion.v. The header said that the measure is the pair of
  the tickets left and the counter of the partner end under `lexlt`. The
  proof in soup/LFAdequacy.v uses the counter of the dual end alone under
  $<$ on $\mathbb{N}$, and `lexlt`, `lexlt_dec` and `lexlt_wf` had no
  user. Header fixed, the three removed.
- examples/LFClose.v. `cl_typed`, `cl_term` and the new `cl_ptyped` hold
  at every bound `N : fuel`. `cl_lftyped` is the instance at `Some N`.
  New `cl_dftyped` (`∃ W, ∅ ⊢_W cl c⁺ ∥ cl c⁻ : ∗`) and
  `cl_deadlock_free`, one line through `soundness`.
- CheckAll.v. Removed `join_vis`, `connect_hidden`, `rptyped_ptyped`,
  `ptyped_rptyped`. Added `cl_dftyped`, `cl_deadlock_free`. 275 to 273.
- Notes `P-Connect.wf` and `th.ptyped-ren` of the map cited `join_vis`
  and `iface_ren`. They cite `ptyped_ren` and `ptyped_apart` now.

Not done. A sweep of every comment in v2 for stale descriptions. I fixed
the three I met (Hiding.v header, Typing.v above `ptyped`, Criterion.v
header). The header of soup/LFAdequacy.v says "partner end" throughout,
which is a Rocq comment and not reader-facing text.

## 3. Open problems

Solved on this branch.

- Annotations in the deadlock-free view. Gone, one $\approx$.
- Titles and `introduces` with lock-free notions. `w-wf` and `w.R7`
  renamed. The `introduces` list of `ct-costs` is read by the checker
  only (tools/proof-map/lib/tex.js) and never rendered, so $\kappa_L$
  there reaches no reader.
- "Hidden end". Gone from reader-facing text. `hbot` stays in deviations.
- The turnstiles. $|\!\!\vDash$ is $\vDash[\kappa_L]$. $\Vvdash^{N}$ stays,
  see question 1.
- The close example in the deadlock-free view. Done, with two one-line
  Rocq results.
- Soundness leading with `lf_soundness_run`. Done.
- A typing-only badge. Done, two examples use it.
- The deadlock freedom of the `rx-*` programs is marked argued.

Analysed, with a recommendation.

- The flagpair static rejection. examples/SemBranch.v already proves
  `sbv_rejected`, no `ptyped` of the self-computed flag process at any
  bound, world or annotation, through `sbv_thread_needs`, which reads the
  two closes of each arm of a case through `cl2_needs`, and `ptyped_two`,
  which splits the P-Connect. Thread A of flagpair has the shape of
  `sbv_thread` with a received variable as scrutinee instead of
  $\mathsf{not}\,(\mathsf{inj}_2\,\ast)$, and thread B the same with the
  dual ends. So the static rejection of flagpair is `sbv_rejected` twice,
  one thread per component, plus the cycle of the joined world. The
  variable scrutinee needs an inversion of E-Case under E-Sub with a
  variable, which `sbv_thread_needs` does for a $\beta$-redex. I estimate
  150 lines and no new machinery. The fx-small report expected point
  inversions to be new. They exist in SemBranch.v. Recommendation: do it
  in a small branch, with `fp_static_rejected : ¬ ptyped N η W ∅ fp_config
  TUnit`.
- The descent $n$ times. The language has no numbers, so the variant of
  rx-chain that descends $n$ levels and then stops needs a counter
  encoded as a channel of choices and a step lemma through E-Case. The
  one-level descent already proves the rejection. Recommendation: skip
  unless the paper states the $n$-fold variant as a theorem.
- rx-chain at $N = \infty$. The map claims deadlock freedom and the
  deadlock-free typing of `grow` without proof, now marked argued. A
  derivation needs a box constraint that orders the tree of each round,
  as `fjr_dftyped` does for recursive fork-join, which is the template.
  Recommendation: prove `rc_dftyped` and `rc_deadlock_free` the way
  `fjr_dftyped` and `fjr_deadlock_free` are proved. Then the lock-free
  rejection theorems speak about a program that the deadlock-free system
  accepts, which is the point of the example. Half a day.
- The PGV, PN and MP translations. theories/pgv, theories/pn and
  theories/mp hold about 21000 lines against the old end-point system.
  Porting them is a project of its own, and the proposal keeps the
  translations out until stage S5. Recommendation: leave them on
  old-main and port when the algorithmic system exists, so that the
  translations target a checker and not only the declarative judgment.
- The old examples v2 lacks. theories/examples has the bit program
  (EndPoints.v), the forwarder with an existential payload
  (Forwarder.v), Congruence.v, the cfst examples, DataBranch.v,
  ReceivedChain.v, MilnerSched.v and the literature examples under lit/.
  Each is a typing derivation in v2 or a rejection for Appendix B. The
  bit program and the existential forwarder show the payload binder and
  the field points, which no v2 example shows in this form. Milner's
  scheduler is the classical ring. Recommendation: port those two and the
  scheduler as typing checks, one file each, and record the cfst and lit
  verdicts in Appendix B without mechanizing them. One day.
- Per-branch orders, point reuse and the state judgment route are
  decisions the author took on 2026-11-23 and 2026-11-24. Not touched.

## 4. Questions for the author

1. The lock-free process judgment is written $\Vvdash^{N}_{W}$, the Rocq
   notation of `lf_sem`. Writing it $\vDash^{N}_{W}$ over the one turnstile
   collides with the cost judgment $\Delta \vDash^{N} e : T\ !\ \varepsilon$
   of `csem`. Keep $\Vvdash$, or rename the cost judgment, for example to
   $\Delta \vDash_{\mathsf{fuel}}^{N} e : T\ !\ \varepsilon$?
2. The extension of the order to bounds makes $\bot \prec \bot$ and
   $\top \prec \top$ hold. The Rocq has no such order and states each
   check by cases. Is the one-order reading acceptable on the map, or do
   you prefer the Rocq cases spelled out?
3. E-New shows the two constructors `e_new` and `e_new_fld` as one rule
   with the triple $(p, \bar\rho, C)$, a case split written as set
   membership. An alternative is a rule E-New for a fresh base and one
   line "E-New-Field is E-New at $p = x\cdot\kappa$ with no binder and
   $C = \top$". Which do you prefer?
4. Should the flagpair static rejection be proved as recommended above
   (`sbv_rejected` twice plus the cycle)?
5. Should rx-chain get `rc_dftyped` and `rc_deadlock_free` so that the
   map's deadlock-free badge stops saying argued?
6. Which of the old examples should v2 port, and should the translations
   stay on old-main until the algorithmic system exists?
7. `rel.vsize` and `sr.size` are hovers in the caption of `v-rel` now, not
   in the formula. Keep the measure out of the formula?
8. The header of soup/LFAdequacy.v and other Rocq comments say "partner
   end". Should the Rocq comments follow the vocabulary of the map?
