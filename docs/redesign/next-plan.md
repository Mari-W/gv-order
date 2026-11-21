# Next plan (draft for the author, 2026-11-20)

## Current plan (author, 2026-11-21), supersedes the phases below where they differ

1. Running now. The Rocq stages 2 to 4 of overnight.md on redesign-clean3
   (generalized arrows, no future variables, inversion lemmas and static
   rejections). Entries 4 and 5 (fair runs, the Padovani corollary) on
   redesign-fair, with dependent choice and excluded middle as explicit
   hypotheses.
2. Decided. Tickets are one cap per end, `tk(o) + tk(ō) ≤ K`, and the old
   tickets ϑ go (check-links-without-tickets.md, last section). Excluded middle
   and choice are allowed as explicit hypotheses of lock-free adequacy, so
   transfinite step indices replace χ (check-transfinite.md).
3. Design write-up A3, running (check-layers.md). Points mean ordinal layers
   at run time, as in Lantana (`obl_new`, strict `obl_move`,
   `nonstrict_move.v`), so the union of the worlds of a run is well-founded
   and `wfworld` and the family laws go. Fuel extension
   (`oblP_fuel_extend`) in place of a fixed N and K. The client-server
   constraint is tested against both.
4. Then one Rocq run for 2 and 3 together (tickets, transfinite indices,
   layers), then plain `new` (entry 2) on top, then the map drafts. Until then
   no Rocq work builds new proofs on ϑ, χ, families or `wfworld` beyond what a
   running stage needs.

Nothing here starts before the author's go. Order is the author's: two design investigations
first, then several agents for Rocq, plausibility and the paper, then the map skill.

## Phase A. Design investigations (write-ups, then a planned draft on the map)

**A1. Links without tickets.** Goal: tickets, ticket needs `ϑ`, `tlink`, `tspawn`, `tok` and the
ticket half of the lock-free measure go.

- Fact to start from. A link already resets no counter. `own_next` (v2/soup/Soup.v:130) deletes
  `o1`, `o2` and renames the other ends by `csub`, and every counter stays. The trouble in the
  relink example is that the link moves the wait of thread B from the end it waited on onto a
  different end, one that `new` created with counter N. Each round the wait starts over.
- Candidate. The link carries the old counter over: the end that becomes the new partner of the
  waiting end gets `min(its counter, counter of o1 − 1)`, as a Lantana obligation keeps its fuel
  when it moves and burns one unit (`lantana2027`, OBLS-OFFLOAD).
- What to check. (1) The thread holding that end was typed with its own credits, so lowering its
  counter can break its fuel. Find whether the typing of E-Link can pay for it instead, for
  example by asking credit of the linked ends. (2) Spawn then needs no ticket split. (3) The
  relink example must be rejected, every lock-free example must still type, the measure must still
  decrease. (4) The rejected programs of `rejects.js` stay rejected.
- Output. `docs/redesign/check-links-without-tickets.md` with a verdict and the rule changes, then
  the change on the map, tagged planned.

**A2. Transfinite step indices.** Goal: the existential property, so that the creation choice of
O-New is an ordinary existential inside the relation and χ and the `∃ a, χ` before `∀ n` go.

- Precedents in the store: Transfinite Iris (`spies2021transfinite`), whose abstract states that
  ordinal indices validate the existential property, at the price of later-exists commuting; and
  Lantana (`lantana2027`), which builds liveness on it in Rocq.
- What to settle. (1) Which index the judgments use, so that one choice holds along a whole run
  and not only for the first step from a limit. (2) How a step of cost c subtracts at a limit
  ordinal, and how the least fixpoint for cost-0 steps reads. (3) Which lemmas of ours use the rule
  Transfinite Iris loses. (4) What the Rocq change costs: today one `sfix` over `nat`
  (relation/Sfix.v), Lantana uses an ordinal library.
- Output. `docs/redesign/check-transfinite.md`, then the map draft, tagged planned. Plain `new`
  (entry 2) is then redone on top of it: the deadlock-free relation allows more freedom, the
  lock-free relation constrains it.

## Phase B. Agents, once there is quota (at most two at a time)

1. **Rocq.** The queued next run of `overnight.md` (per-end capture, generalized arrows, no future
   variables, inversion lemmas and static rejections, fair runs with dependent choice as a
   hypothesis, the Padovani-style corollary), then A1 and A2 if the write-ups hold.
2. **Plausibility.** An agent that checks each Rocq change and each planned map block against the
   known counterexamples and the examples, before and after it lands.
3. **Paper.** Catch up the paper with the plan (the paper phases of `paper-plan-phases`), after
   the Rocq side of A1 and A2 is decided.

## Phase C. The map skill (`docs/explorer/MAP-SKILL.md`)

Rewrite the map with JSON as the single source and build a skill that (1) creates a map from the
proof code, (2) checks a map against the code (names, statements, variables introduced before use,
hovers, cross-links), and (3) handles the writing, ordering and structure rules. The page renders
any map, keeps the mode switches as a generic mechanism, has no scrollbars at any zoom and a
better theme.
