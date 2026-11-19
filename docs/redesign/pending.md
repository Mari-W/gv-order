# Pending changes: the map leads, the Rocq follows

Since 2026-11-19 the author reviews the explorer map (docs/explorer) and
asks for changes. Each change goes into the map at once and into this list.
One proof-repair agent later implements the whole list in the Rocq in a
single run. Where a change turns out implausible in the Rocq, the agent
reports and the author decides.

Each entry: what changes, where the map already shows it, what the Rocq
must do, open questions.

## Open

1. **Events folded into labels (N.2).** Three cases `solo i α`,
   `sync i j o σ`, `offer i σ`. Started on branch redesign-clean3 in the
   worktree .claude/worktrees/redesign-s4: N.1 (P-Term asks `tfree`,
   `prim` gone) is committed there (6986a1c), N.2 is uncommitted and
   built, without make test, make check or the map. The agent stopped when
   the session ended. Map: not yet. Rocq: finish N.2 on that branch.

2. **One `new` with an optional interval.** `new [L | U]` with L, U sets
   of held ends, both optional. The new channel gets a point variable ρ
   with exactly the facts l ≺ ρ (l ∈ L) and ρ ≺ u (u ∈ U). `new` alone is
   the empty interval. Replaces `new_ℓ`, `new_κ o`, E-New, E-NewAt,
   O-New, O-NewAt, the two labels and the family laws Λ_ℓ. Map: not yet
   (design first). Rocq: world growth at creation, a strictness check at
   every creation, how the semantics picks the fresh point. Open: does
   the interval for one end give the partner end's thread the facts it
   needs (dual end), or does `new` need an interval per end; are fields
   x·κ still needed. Design note to be written before any Rocq work.

## Done in the Rocq

(entries move here once the repair agent has implemented and merged them)
