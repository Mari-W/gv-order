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

2. **One plain `new`; position and facts live in the type.** Decided
   2026-11-19. The term is `new`, label `new c`, event `new_i c`. E-New
   types it at `∃^⊥ ῑ. C. ((S@π)^N ⊗ (S̄@π̄)^N)` with
   `(ῑ, π) ∈ {(ρ, ρ)} ∪ {(ε, x·κ)}` (a fresh root, or a field of a point
   of the context) and premise `strict(Γ ∪ C)`. C is any constraint in the
   existing constraint language (possibly infinite) over π, its shifts and
   fields, and context points. An interval per end is the special case
   `L⁺ ≺ π ≺ U⁺, L⁻ ≺ π̄ ≺ U⁻`. Finite intervals of held ends do not
   suffice: the client-server example needs `ι+k ≺ (κ+k)‾` for all k.
   Worlds become `W = (A, ≺_A)` with growth `W ⊕ C`; families L, laws Λ_ℓ,
   generated roots g_ℓ, `new_ℓ`, `new_κ o`, E-NewAt, O-NewAt, T-Act-NewAt,
   the labels LNew ℓ / LNewAt and P-Connect's disjoint-families premise go.
   O-New: `c fresh ⇒ ∀ a ∉ A_W ⇒ ∃ S π C. π ∈ {a} ∪ {x·κ} ∧
   strict(W ⊕ C) ∧ e' at_{W⊕C} Θ[c⁺ ↦ S@π, c⁻ ↦ S̄@π̄]`. The examples are
   translated one to one: new_ℓ becomes new with C = Λ_ℓ(ρ) stated on the
   new that needs it, new_κ o becomes new at x·κ. Map: done.
   Rocq: E, V, P and the soup become Kripke in W along creations (W grows
   along a run), world growth lemmas (strict and well-founded preserved by
   one strict growth), every theorem over the grown world.
   Risks to report back on, not to paper over:
   (a) O-New chooses C by an existential at each level. The lock-free
       argument needs ownership the same at every level, and the root is
       universal for that reason. C chosen per level may break it. Possible
       fix: the soup fixes the world of a run once, as it fixes ownership.
   (b) Each grown world is well-founded, but a run may grow the world
       forever (a loop that creates below the previous channel). Check that
       lock freedom only needs the world at each position, not the limit.
   (c) Two creations at one field x·κ share a point. Allowed (loose), the
       strictness check decides.

3. **No GV constants in the Rocq; constants are values on the map.**
   `k_send`, `k_new`, `k_new_at` are unused. Rocq: delete them and the
   sentence about constants in the header of lang/Syntax.v. The map shows
   constants `k` as values with `k v` stepping by the head step of `k`.
   The Rocq keeps saturated `Op k e`, and the value `k` is `λx. k x`.
   The map shows a block "Types of constants" (typing section, DF form):
   send : T[x·i] ⊗ S₀@x ⊸^x S@x⁺ (conditions of E-Send), recv, close,
   select_i, branch at upper point x, link : S@x ⊗ S̄@x̄ ⊸ ∗,
   spawn : (∗ ⊸^u_l ∗) ⊸ ∗, force : □(∀ῑᾱ.C. ∗ ⊸^u U) ⊸^{u[x̄]} U[s̄][x̄]
   under Γ ⊢ C[x̄]. Rocq: prove each as a derived rule, λy. k y typed at
   that schema (dftyped, and the merged typing with the annotations of
   the rule of k), or report which schema needs changing.

4. **Lock freedom is not vacuous (low priority, queued 2026-11-19).**
   `lock_free p` quantifies over every maximal weakly fair run from p. Keep
   that universal (an existential would let a good scheduler hide a lock).
   Add a semantics lemma, independent of typing: every configuration has a
   maximal weakly fair run (round-robin over its finitely many threads;
   the constructive form needs a choice of step at each position). State
   the main result with it, e.g. `lf_soundness` also concludes
   `∃ r l. erase (r 0) = p ∧ maximal r l ∧ wfair r l`, or package both in
   the definition. Map: add the existence lemma to the theorems section
   once proven.

5. **Padovani-style lock freedom as a corollary (low priority, queued
   2026-11-19).** From `lock_free p` and item 4: for every q reachable
   from p and every thread pending in q, some q' reachable from q has a
   step in which that thread takes part (Padovani 2014, Def. II.1, in our
   per-thread form). Map: one line in the theorems section once proven.

## Done in the Rocq

(entries move here once the repair agent has implemented and merged them)
