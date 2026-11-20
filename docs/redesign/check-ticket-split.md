# Design check, type-directed ticket split at spawn

Overnight run of 2026-11-20, branch redesign-clean3. Write-up only, no Rocq
change.

## Verdict

It does not go through as stated. The split cannot be fixed outside the step
index unless the relation reads the type of the spawned thunk, or unless the
proof uses a choice principle that v2 does not assume. With the split fixed,
ticket needs would add up and `tok` and the doubling form would go.

## Where the split lives today

- F-Spawn (fuel/Fuel.v, `f_spawn`) gives the child `⌈tk/2⌉` tickets
  (`Nat.div2 (S tk)`) and the parent `⌊tk/2⌋` (`Nat.div2 tk`), both at the
  next level n′.
- The soup follows a run by the index-free update `tk_next` (soup/Soup.v),
  which splits the tickets of the spawning thread by the same halving. The
  soup fixes its state once for every index (`lf_sem := ∃ N a, ∀ n, …`).
- The transformer of a spawn (types/Costs.v, `tspawn`) doubles the slope and
  takes `max(2·b, 2·b_c − 1)` as the offset, so that the half the child gets
  covers `b_c` and the half the parent keeps covers b. Sequencing composes
  `ϑ(r) = 2^s r + b` (`tseq`) and asks `tok`, which rules out a first part of
  infinite slope before a second part that needs tickets.

## Why the split cannot be type-directed

The child's need `b_c` is the transformer in the type of the thunk. FuelE and
the soup read no types, so F-Spawn can only state the split by the tickets.
Two forms remain.

- An existential split, `∃ k ≤ tk` with the child at k and the parent at
  `tk − k`. FuelE chooses k at each level, and the soup needs one k for all
  levels, because `tk_next` computes the child's tickets from the event. The
  choices are finite and FuelE is antitone in the level, so a classical
  pigeonhole argument finds one k valid at every level. Without excluded
  middle the argument does not go through, because validity of a split at a
  level is a proposition of FuelE, and v2 has no procedure that decides it. This is the same obstacle as risk (a) of entry 2,
  with a finite instead of an infinite choice.
- A split read off the term, for example the least k that fuels the child.
  It needs such a procedure as well, and reading the term in the soup
  is a syntactic clause in the relation, which the rules exclude.

## What would replace tok and the doubling form

If the child received exactly `b_c` and the parent kept `tk − b_c`, every
need would be an offset alone, `ϑ(r) = r + b`. Sequencing adds the offsets,
a spawn adds the child's offset to the parent's, and a link adds one. The
slope s, `tok` and the `2^s` factors of `tapp`, `tseq` and `tspawn` would
go, and `meets ϑ r tk` would read `r + b ≤ tk`. An infinite need would stay
as the offset ∞.
