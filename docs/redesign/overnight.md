# Overnight run: one agent, the whole pending list

One repair agent works through these stages in order, in worktree
`.claude/worktrees/redesign-s4` on branch `redesign-clean3`. Each stage
ends with a build (`ulimit -s 1000000; make -j2`, retry on Error 139),
`make test`, `make check`, a commit, and a line in `pending.md` under
the entry it closes. A stage that turns out implausible stops with a
report in `pending.md` and the agent moves to the next independent stage.
Never push, never add AI attribution, no syntactic clauses in the
relation, no semantic premises in typing rules.

The map in `docs/explorer` already shows every decided change. The agent
does not edit the map except to fix a statement the Rocq proves false, and
then reports it.

## Stages

1. **Finish entry 6, credits only on ends and closures.** Resume from the
   two WIP commits (2c2168a, b9d0c05). Credits on `(S@x)^a` and
   `(T ⊸ U)^a` only, aging and capture structural, E-Send asks the
   payload aged by one hop, no payload credit b.
2. **Entry 13, P-Connect over the shared roots.** p_term asks
   `strict W`. p_connect asks only `strict (W1|_S ⊔ W2|_S)` for the
   shared roots S (and disjoint families until stage 4 removes them).
   Prove the invariant "every process derivation sits over a strict world"
   and drop p_join and the `strict W` premise of process soundness where
   it follows.
3. **Entry 14 cleanups.** heads into `Point ∪ {⊥}` with hbot and the
   ⊥ flags folded in (optional, only if it shortens proofs). Keep the
   arrow bound `LNone` apart from `LBot`.
4. **Entry 2, one plain `new`.** Position and facts in the existential,
   worlds grow, families go. Report on risks (a), (b), (c) before
   pushing through. Stop point after the feasibility check of (a).
5. **Entry 7, mechanize the rejected examples.** One Rocq lemma per
   example of `docs/explorer/gen/rejects.js` showing the lock-free typing
   fails (postponement, delegation, relink, growing chain). Add the flag
   program outside the relation in every world, as
   `db_component_unrealizable` does for the dispatcher.
6. **Entry 4, a weakly fair run exists** (low priority).
7. **Entry 5, Padovani-style corollary** (low priority).
8. **Notation of the map in the Rocq** (map changes of 2026-11-19, display
   only so far). Give the Rocq the notations the map uses, or rename, so that
   statements read the same in both:
   - fuel `e ∈ F^N_n⟦Φ ; tk ⊢ σ ! (d, r)⟧` and `v ∈ FV^N_n⟦Φ ⊢ T^a⟧`, with one
     map `Φ : o ↦ S^f` for the two maps `Π`, `φ` of `FuelE` (a notation over the
     pair, or a refactor to one map if it shortens proofs), `Φ↓` for
     `ftick`, `refill`, `fhand`, and `spare Φ` for `fspare`;
   - `ϑ(r) ≤ tk` for `meets ϑ r tk`, and `ϑ(0) ∈ ℕ` for `∃ tk, meets ϑ 0 tk`
     in `p_term`, `fsem_of_cost` and `lf_soundness_source`;
   - `cr(Δ) ≤ N` for `∀ o te, Θ !! o = Some te → fle (te_cr te) N`;
   - the soup as relation, fuel and `consistent(a, A, Π)` (`soup_gen`).
   Open question for the author, do not decide: one existential for the
   protocol of a new channel shared by O-New and F-New, so that the soup can
   ask `Π = sty ∘ A` and drop `Π`.
9. **Entry 11, faithfulness audit** of the map against the merged Rocq.
   List every difference that is not a queued entry.

## Design checks, write-ups only (no Rocq change without the author)

Each produces a short note in `docs/redesign/` with a verdict and, if it
holds, the exact rule and lemma changes.

- **No future variables (entry 14b).** Check that `Γ ⊢ x ≺ φ` iff
  `Γ ⊢ x ≼ u` for the unique `φ ↦ u`, against `fl`, `hc_fvar` and
  `sf_den`. If so, F becomes "X and everything above u" and Γ keeps only
  constraint instances.
- **Per-end capture (entry 12).** The body sees `Δ − a` instead of the
  floor h, FV-Arrow asks counters at call time at least the counters at
  creation minus a. Check FV-Arrow, capture, Sub-Arr. Decides whether
  E-SpawnLam is derivable without loss.
- **Type-directed ticket split.** The child gets exactly its need b_c.
  Check that the split can be fixed outside the step index without the
  relation reading types, and what replaces `tok` and `2^s r + b`.

## Not in this run

Points on actions (not wanted), named variables in Δ (cosmetic, map
only), link budgets per end, the topological discussion (needs the
author). The Process.v restricted-channel asymmetry and the law
`x ≺ x̄⁺` wait for the cleanup and the points discussion.
