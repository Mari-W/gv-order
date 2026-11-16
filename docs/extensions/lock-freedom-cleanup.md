# Lock freedom: cleanup and simplification plan

For a later agent. Goal: a clean, workable lock-freedom result whose static
side is a typing discipline with compositional rules, not a pile of
syntactic checks. Read docs/extensions/lock-freedom-quirks.md first (every
quirk with its reason), then the progress file's decisions, then plan §16
to §18.

## Standing rules (from the author)

- No syntactic condition inside any relation (base, live, fuel, soup). The
  only exceptions are value-level conditions (a value's environment holds
  exactly the channels it contains, mirroring `sentc`) and conditions on
  step labels. Never add one under delegation. Ask first.
- Property definitions over the untyped semantics (`waits`, `lock_free`)
  may read syntax.
- Semantic premises over syntactic ones. Fewest rules. Encode or derive
  before adding a rule.
- Protected statements keep their form unless the author agrees: the
  soundness family, `fundamental`, `adequacy`, the composition lemmas, the
  live theorems, `lf_criterion`, `lock_free`, `thread_progress`,
  `lf_adequacy`, `LFP_term`, `LFP_connect`, `LFP_join`.
- At most two agents at once. Builds in the background
  (`ulimit -s 1000000`, retry on Error 139). `simpl`/`cbn` on FuelE blows
  the stack, use `vm_compute` on terms. Targeted edits. No AI attribution
  in commits.

## Part 1. Simplify the relations

Ordered by value for effort. Each item names what it removes.

**R1. Obligations explicit in the soup.** The soup carries an obligation
map (waiting end, serving end, counter). The per-thread fuel predicate reads
the obligations its thread serves. Send, spawn and link *move* an
obligation and charge one, acting on the end discharges it and refills.
Removes the replacement clause `frep`, the overwrite `flr`, one index level
per soup step, and quirk A13b at its root. This is the principled form of
option 2 (author, 2026-11-16). Do it before any further patching of floors.

**R2. Distinct names for the two ends.** Replace `Chan c b` by two end
names c and c̄. Removes the polarity bit, `pt_pol k = b` everywhere,
`tenv_bipol`, the bit check in `tenv_hd_end`, and the sender-keyed oddity of
the delegation floor (the floor can be read at the carrier end itself).
Mechanical but wide: lang, types, every relation, every example. Do it in
its own stage with a full build after.

**R3. A determinism lemma.** Show that soups at two indices agree on
points and ownership at every position of a run (syntactic points plus
value conditions make every split forced). Then P and F become derived from
the environments, and `LFP` loses `∃ q P F`. Also check whether the first
conjunct `∀ n, LPrel n …` of `LFP` follows from the soup and drop it if so.

**R4. One "lock-free world".** Bundle `world_wf`, `well_founded (w_lt W)`
and the budgets into one record. If R1 makes floors a property of
obligations, fold `w_pay` into `w_bud` or drop it.

**R5. Smaller side conditions.** Drop `ftravel` if F-Wait alone carries the
argument. Weaken `wbud_agree` to the cut if FuelE only reads budgets at
points the world knows. Remove lemma premises that only served E-Fit.

**R6. Optional, large.** One relation with a switch instead of the base and
the live copy (quirk A4). Only if the paper presents them as one relation or
the duplication blocks further work.

## Part 2. Replace the static fragment by typing rules

Today `lfptyped` and `lfsource` are the typing judgment plus a list of
global analyses: the guard, R1 (recursion in tail position), R2-recv with
fed slots, the type hand-off graph, the root graph with `stab`, `foreign`,
`bleak`, `troots`, the stretch bound `stretch_len = 2·seg_len` via `scost`,
the annotation `ann` backed by derivations, the count of leading `TPt`
parameters, and `wf_world (cworld Ψ)`. Each closes one counterexample. The
fundamental theorem then has to rebuild per-thread facts from them.

The clean version makes each concern a local rule of a typing judgment, so
`lf_fundamental` is again one compatibility lemma per rule, like
`fundamental` and `live_fundamental_guarded`.

**T1. Liveness by guarded recursion.** Replace the syntactic guard by a
typing rule for box bodies: the self is available only after one channel
action of the round (a later modality on the self, or a cost index in the
judgment). Compositional and standard (guarded recursion). It also lifts
quirk B6, because a point argument is just an argument.

**T2. Fuel by bounds in the typing context.** The judgment tracks, per held
end, a static bound: acting on the end resets it to the end's budget, every
other channel action decrements it, a hand-over (send, spawn, link)
requires it to be at least one plus the floor. Box types state what their
point parameters need as budget atoms in the box's constraint set, next to
the order atoms (for example β(ι) ≥ k beside ι ≺ κ). This replaces the
stretch bound, R1, R2-recv, the fed-slot clause, the hand-off graph, the
root graph and the annotation in one go. Non-tail recursion becomes
admissible where the bounds work out, which may admit TreeSum (quirk D3).
**Needs the author's decision.** Budget atoms in constraints are not
tickets in session types (session types stay as they are), but they are
numbers in box types. Present the difference before building.

**T3. Rank.** Keep `well_founded (w_lt W)` as a semantic premise. The only
global static check left is that the creation hypotheses give a
well-founded starting world (`wf_world (cworld Ψ)`), which is a property of
the world, not of code.

**T4. What remains of the old checks.** Nothing, if T1 and T2 work. If T2
is rejected, keep the current fragment but drop the rules that option 2
made redundant: the self-loop rule for links inside boxes (quirk B5), and
whatever R1 (Part 1) makes unnecessary in the root graph.

A minimal alternative, if the author prefers it to T2: drop the static
fragment from the headline. Lock freedom is semantic (`LFP`, adequacy,
composition), examples get direct semantic proofs, and the static
discipline becomes future work.

## Part 3. Calculus-level items (author decisions)

- TreeSum's box result carrying a `TPt` would bring back SegmentInterleave
  and SegmentDeleg.
- ChoiceTranslate is impossible under syntactic points. Accept the loss or
  add point expressions that read the current point of a held end.
- Source-level soundness no longer covers channel creation. State it in the
  paper or retire `soundness_source` in favour of `soundness_created`.
- The translations PGV, PN and MP need the port to syntactic points.
- SemFlag's underivability is open since the end-points port.

## Suggested order

1. Finish §18 (replacement against the send floor) only as far as needed to
   decide between a quick patch and R1. Prefer R1.
2. R1, then L6 (`lf_fundamental`) on the current fragment, so a complete
   result exists.
3. R2 and R3 as separate stages, each with a full build and CheckAll.
4. T1 and T2 after the author decides on budget atoms. Then retire the old
   analyses in Fragment.v.
5. R4, R5, then R6 if wanted.

Acceptance for every stage: full build, no Admitted, no axioms, CheckAll
regenerated with every active entry closed, protected statements diffed
against the stage's base commit, one log bullet in the progress file, and
quirks file updated (remove what was lifted).
