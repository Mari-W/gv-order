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

2. **One `new` with an optional position and an interval per end.**
   `new@π [L⁺ | U⁺ ; L⁻ | U⁻]`, every part optional. L, U are sets of
   held ends. The position π is either absent (a fresh root ρ) or a field
   `o·κ` of a held end o at point x (then ρ = x·κ). The end c⁺ sits at ρ
   with exactly the facts l ≺ ρ (l ∈ L⁺) and ρ ≺ u (u ∈ U⁺), and c⁻ sits
   at ρ̄ with the facts from L⁻, U⁻ (decided 2026-11-19: one interval per
   end, it is more general). Replaces `new_ℓ`, `new_κ o`, E-New,
   E-NewAt, O-New, O-NewAt, the two labels and the family laws Λ_ℓ.
   Fields x·κ stay, both as positions for `new` and as delivery points
   of messages and choices. Map: not yet. Rocq: world growth at creation,
   a strictness check at every creation, fresh point choice. Open: may an
   interval add facts to a field x·κ that already carries facts, and may
   two creations use the same field.

3. **No GV constants.** `k_send`, `k_new`, `k_new_at` are unused
   eta-expansions of primitives. A primitive as a function value is
   written `λx. k x` directly. Map: done (block removed). Rocq: delete the
   three definitions in lang/Syntax.v and the sentence about constants in
   its header comment.

## Done in the Rocq

(entries move here once the repair agent has implemented and merged them)
