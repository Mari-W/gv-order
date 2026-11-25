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
   - the soup as relation, fuel and `consistent(a, A, Π)` (`soup_gen`);
   - the step clause of `Pbody` over `pstep` (lang/Process.v), so that P
     reads `p' →^{ev} p'' ⇒ Pobl_ev(p'')` and `erase` leaves the
     deadlock-free relation, as the map already shows.
   Open question for the author, do not decide: one existential for the
   protocol of a new channel shared by O-New and F-New, so that the soup can
   ask `Π = sty ∘ A` and drop `Π`.
9. **Remove the clause (fuse) of P** (author, 2026-11-19). P should not
   quantify over fusions `(h, D)` with `fuse_ok`. It came from two repairs
   (progress.md S4.12 and S4.18, proposal.md near "P is closed under fusion
   by definition"). Hard constraints: the link stays the substitution
   `csub` of lang/Process.v, never a forwarder thread. No syntactic clause
   in the relation.
   - Restricted channels as bound names. Today a process is `(C, E)` with
     `C` a concrete set of names, and nothing identifies processes that
     differ by a renaming of `C`. Either quotient (P invariant under
     renaming of restricted channels, proved as a lemma) or make `C` a
     binder, whichever is shorter. Report which.
   - Interface renaming as a theorem. `Prel_rename` (compat/Rename.v:915)
     is today a projection of the clause. Prove it by induction on the
     level, as `Erel_rename` (compat/Rename.v:743) is proved for E.
   - The link case of P-Connect. `csub o1 o2` renames the held ends of the
     other component and can create a new dual pair when that component
     holds `ō2` as well (the comment above `fuse_ok_csub_cut`). Close this
     case from the two lemmas above plus internalizing that pair inside
     P-Connect's own proof.
   - First test: the counterexample of S4.18 (a renaming that joins two
     unrelated interface ends), which must stay excluded.
   - Stop and report if a lemma fails, with the failing goal. Do not
     restore (fuse) under another name. Update docs/explorer/gen (p-body,
     p-fuse, the notes P.fuse, sr.fuseok) when it lands.
10. **Entry 11, faithfulness audit** of the map against the merged Rocq.
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

## Next run (queued 2026-11-20, start only on the author's go)

The run of 2026-11-20 is done (report at the top of pending.md). The next
run follows the author's decisions of 2026-11-20 in pending.md, same rules
as above, incremental `make -j2` per stage, `make test` and `make check`
once at the end, map updated in docs/explorer/gen for every landed stage
(and the "planned" tag in gen/layout.js removed where a stage lands).

1. **Entry 12, per-end capture.** Capture becomes aging by a, FV-Arrow
   asks `φ′ ≥ φ − a`, Sub-Arr asks `a′ ≤ a`, the floor h goes
   (docs/redesign/check-per-end-capture.md).
2. **Entry 12, generalized arrows.** Lower point `⊥` and upper point `⊤`
   on arrows, `spawn (λe)` by E-Abs plus E-Spawn, E-SpawnLam and V-Thunk
   go. Check every lock-free example still types.
3. **Entry 14b, no future variables** (docs/redesign/check-future-variables.md).
4. **Inversion lemmas for `typed`** through E-Case, E-Close, E-Let and
   P-Connect, then the static rejections: `sb_untypable` (SemBranch), the
   static half of FlagPair, and the programs of `rejects.js` where an
   inversion suffices.
5. **Entry 4, a weakly fair run exists**, with dependent choice as an
   explicit hypothesis of the lemma, no axiom. Then entry 5.

Deferred by the author (2026-11-20), not in the next run: plain `new`
(entry 2). Direction: the deadlock-free relation allows more freedom in
O-New, and the lock-free relation then constrains it (the creation choice
χ on the map is one proposal). To be worked out with the author.

## Not in this run

Points on actions (not wanted), named variables in Δ (cosmetic, map
only), link budgets per end, the topological discussion (needs the
author). The Process.v restricted-channel asymmetry and the law
`x ≺ x̄⁺` wait for the cleanup and the points discussion.
