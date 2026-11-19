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

6. **Decided 2026-11-19 (author): credits only where ends sit.**
   Today every slot of a type carries a credit: components of ⊗ and ⊕,
   the body of ∃, the argument and result of ⊸, the result of a box, the
   payload (b), and every Δ entry (static/Contexts.v: `ty` in
   types/Types.v; `TSess` itself has none). The aggregate cases of aging
   and capture (`age_prod`, `age_sum`, `age_ex`, `cap_prod`, `cap_sum`,
   `cap_ex`) push the outer credit into the parts (a + aᵢ) and reset it to
   0, so an outer credit on ⊗, ⊕, ∃ is only a shared offset. Only two kinds
   of position need a credit of their own: an end `S@x` (its counter) and a
   closure `T ⊸ U` (its captured ends are invisible in its type, Cap-Arr).
   Proposal: credits as part of exactly these two type formers,
   `(S@x)^a` and `(T ⊸ U)^a`; drop the credits of ⊗, ⊕, ∃, box results,
   arrow argument and result, and payloads (the payload's own leaves carry
   them, E-Send's floor becomes aging the payload by 1). Aging and capture
   then recurse structurally and the summing rules go. Open: whether any
   proof uses the outer offset to age an aggregate in one step
   (`age_credit` on an aggregate) in a way the leaf form cannot match, and
   whether subtyping of aggregates (Sub-Prod with a + aᵢ) loses anything.
   Map: Types section done (grammar `(S@x)^a`, `(T ⊸ U)^a`, no credits on
   ⊗ ⊕ ∃ box results or payloads; the map calls ϑ a "ticket need"). The
   typing, semantic-typing, fuel and theorem blocks still show the old
   credits and must follow the Rocq once this is implemented.
   Rocq status: the repair agent was stopped by the author on 2026-11-19
   during stage C. Branch redesign-clean3 (worktree redesign-s4) holds
   entry 3 done (5907cd0), a merge of redesign (f0b97af) and two WIP
   commits for this entry (2c2168a, b9d0c05) that do not build. Resume
   from b9d0c05: the credits section of the types was next.

7. **One rejected example per lock-freedom mechanism (2026-11-19).** The
   map's examples page shows four programs that step forever without a
   deadlock while a thread waits forever: postponement (rx-postpone, aging),
   endless delegation (rx-delegate, payload credit / one hop), link refresh
   (rx-relink, tickets), a growing waiting chain (rx-chain, well-founded
   world); τ-divergence is covered by the guard rejections. Rocq: for each,
   the process, a proof that it is not lock free, and a proof that it is
   not lock-free typable at any N (or that the named premise fails for
   every derivation); then fill the badges' Rocq names. rx-chain depends on
   entry 2's risk (b) once worlds grow. Map: done (badges say "to be
   mechanized").

8. **Readable typing notation (draft, under review).** Map: draft blocks at
   the end of the typing section (Draft notation, Draft E-App, E-Send,
   E-Abs): one linear context Δ for ends and variables, W and N implicit,
   held entries `∥ H` (future ∪ heads(H), and in LF the aging H − c), and
   one effect ε = (c, ϑ) with sequencing ε₁·ε₂ (defined iff tok). Pure
   notation over the current rules. If the author approves: convert every
   rule on the map. Rocq: optional definitions and unfolding lemmas.
   Approved by the author 2026-11-19: convert all rules after the repair
   run. Also replace heads(H) by a lighter notation (proposal: H̄, the
   points the partners of H wait at, with S@x ↦ x̄, closures and ∃ ↦ their
   lower point l, boxes ↦ ∅).
   Map done 2026-11-19: every typing rule uses the notation, one form per
   rule with the lock-free parts marked (no separate D- rules on the map),
   and the draft blocks are gone. Heads: no H̄, because an overline on a
   context already means the dual interface (P-Connect). Instead heads
   hide inside `∥ H`, and the two places that still need them lift the
   order to types and contexts, `x ≺ T` (E-Send) and `l ≼ Δ` (E-Abs,
   E-Pack). The typing rules also follow entry 6 (credits only on ends and
   closures, aging and capture structural, E-Send asks `T' − 1 ≤ T[x·i]`,
   no outer credits on results). Process rules and the semantic-typing and
   theorem sections still use the old judgment (entry 9).

9. **Readable semantic typing (to design).** Same treatment as entry 8 for
   V, E, P, the obligations, readiness, fuel and the soup: show the relation
   at κ_DF in DF mode, the general κ form with the differences coloured in
   LF, and lighter notation where one idea is written out several times.
   Map only. Draft after entry 8 is converted.
   Map done 2026-11-19: a new marker `\dfo{…}` shows the deadlock-free
   reading of a part whose lock-free reading is an `\annot`, so DF shows
   `j < n`, level `n` for a send payload and `κ_DF(α)` where LF shows the
   general table. The general cost table is LF only, the DF table labels
   its last row as a message. The obligations write the head of the
   subject end once, `Θ(o) ≐ S@x` (Θ(o) = S₀@x with unfold S₀ = S). The
   semantic judgment takes the typing context, `Δ ⊨^F_W e : T`, with
   `|Δ|` its ends. Payloads lose `^b` and FV follows entry 6.

10. **Readability pass over every section (map only, after the repair
    run).** Syntax, semantics, types, typing, semantic typing, theorems,
    examples: lighter notation where one idea repeats, explanations and
    examples a newcomer can follow, every symbol defined and hoverable,
    hover texts proofread (also the DF texts the annotation filter cut).
    Entries 8 and 9 are part of it.
    Scope narrowed by the author 2026-11-19: theorems and examples only,
    the other sections are fine. Map done 2026-11-19: theorem statements
    use the new judgments (`∅ ; Δ ⊢^F_W t : T`, `T ! ε` for the annotated
    one, `Δ ⊨^F_W t : T`, erasure `Δ_df`), "merged judgment" became
    "annotated typing judgment", general-κ rows and `[κ]` show only in LF,
    and the captions state the DF result first. Examples use the source
    syntax of the syntax section (`let ∗ =`, `let ⟨a, b⟩ =`), the
    forwarder protocol reads `?((∗ ⊸ ∗)^2).Close`, and the controller
    states idle aging in the entry-6 form.

11. **Faithfulness audit of the map against the Rocq (after the repair
    run is merged).** Check every block, rule, signature and theorem on the
    map against the definitions in v2/, list every difference that is not a
    queued entry, and fix the map or queue the Rocq change.

12. **Generalized arrows, E-SpawnLam derived (decided 2026-11-19 by the
    author, design to confirm).** Today E-SpawnLam exists beside E-Spawn
    because E-Abs asks a common lower point `l ≼ Δ` and types the body
    under a fresh future above `u`, and a λ spawned in place needs neither.
    Generalize the two points of an arrow instead.
    (a) Lower point `l = ⊥` allowed (`lbound` already has `LBot`, used by
    `∃^⊥`). E-Abs drops `l ≼ Δ` when `l = ⊥`, `hbot` reports such arrows,
    and holding the closure puts `⊥` into the future, which forbids
    blocking while it is held, as for `∃^⊥`.
    (b) Upper point `u = ⊤`. E-Abs types the body under the empty future
    `(∅, ·)`, and E-App needs `⊤ ≺ F`, which holds only for the empty
    future, so such a closure is applied only in tail position of a thread.
    E-Spawn asks nothing of `u`.
    Then `spawn (λe)` types by E-Abs at `l = ⊥, u = ⊤` plus E-Spawn, and
    E-SpawnLam goes. The value clause at `u = ⊤` is exactly `Vthunk` (body
    at the empty future), so V-Arrow absorbs V-Thunk and one value clause
    goes too. Check: E-SpawnLam ages the handed context by one hop while
    E-Spawn asks closure credit `a ≥ 1`, so capture at `h, a = 1` must give
    the same credits as `Δ − 1`, and the ticket need of E-SpawnLam
    (`tspawn` of the body at reserve 0) must match E-Spawn on the arrow.
    Tickets match (both write tspawn(ϑ'(0))). Credits do not: capture
    restates every captured end at one floor h, with h + a ≤ a₀, while
    E-SpawnLam keeps each end at its own credit minus one. Lost example:
    A at N and B at 1 handed to a child that acts on B while holding A.
    E-SpawnLam gives A at N − 1, capture at a = 1 forces h = 0 and A at 0.
    Proposed fix, to check first: per-end capture, the body sees Δ − a
    instead of the floor h, and FV-Arrow asks counters at call time to be
    at least the counters at creation minus a (FV knows the creation
    counters). Then the derivation loses nothing, ordinary closures get
    more precise, and the floor h (and Cap-Arr's h − h₀) may go. Touches
    FV-Arrow, capture, Sub-Arr. Fallback if it fails: generalized arrows
    with the loss, after checking every lock-free example still types.
    Order: check per-end capture, then generalize arrows.
    Rocq: after the repair run (entry 6) is merged. Map: after the design
    is confirmed.

13. **P-Connect compares only the shared roots (2026-11-19, author).**
    Today p_connect asks world_wf W1, world_wf W2, disjoint families and
    strict (W1 ⊔ W2), and the lemma p_join states the overlap form, strict
    W1, strict W2, strict (W1|_S ⊔ W2|_S) for the shared constants S,
    equivalent by p_join_iff_connect (strict_join_iff). world_wf is not
    trivially true, because p_term asks nothing of its world. New form:
    p_term asks strict W, and p_connect asks disjoint families and only
    strict (W1|_S ⊔ W2|_S). By induction every process derivation sits over
    a strict world (strict_join_iff for the connect case), so the old rule
    is derivable, p_join disappears, and the `strict W` premise of the
    process soundness theorems follows from the derivation. The map writes
    S = A_{W1} ∩ A_{W2} and no families premise, because entry 2 removes
    families. Map done. Rocq: after the repair run is merged.

14. **Typing QA against static/Typing.v (2026-11-19).** Beyond entries 2,
    6, 8, 12, 13 the map differed in three places, all fixed on the map:
    `¬hbot T` at E-Send is gone: the map lets heads return ⊥ for hidden
    ends (heads(∃^⊥) = {⊥}, no fact relates ⊥ to a point), so `x ≺ T`,
    `l ≼ Δ` and held futures need no separate hbot or ⊥_Δ (Rocq: heads
    with ∅ plus the flag hbot, sf_unionb, lbx_below_h; optional Rocq
    cleanup, heads into Point ∪ {⊥}); the arrow lower bound "absent"
    (`LNone`, no end) is written `·`, not `⊥`, which is the hidden bound
    `LBot` of `∃^⊥`; held futures add the flag ⊥ when H holds an `∃^⊥`
    (`sf_unionb … (lenv_bot Δ2)`). Entry 12 must keep the two apart: the
    new arrow bound there is `LBot`, and hbot must report such arrows, so
    a spawn-only closure cannot be sent (no loss, it cannot exist today).
    Open questions from the author, to discuss:
    (a) Named variables on the map instead of de Bruijn indices in Δ, as
        for points (the Rocq keeps indices).
    (b) Future variables: Γ holds φ ↦ u (the fact u ≺ φ) and F names φ as
        the unknown rest. Each φ has exactly one fact, so Γ ⊢ x ≺ φ iff
        Γ ⊢ x ≼ u. Candidate: F = (X, above u) and no future variables in
        Γ. To check against fl and the semantic den_{ρ,B}.

## Done in the Rocq

(entries move here once the repair agent has implemented and merged them)

## Open discussion (not scheduled)

- **Link budgets per end.** Per-thread link tickets reject a box that links
  once per round forever (e.g. a server linking each new client to a
  worker) and received closures that link. A budget per end in the session
  type, like payload credits for hops, might accept the server. The plan
  (docs/extensions/lock-freedom-plan.md §18) rules out per-end tickets only
  together with replacement. The author judged it not the cleanest move for
  now (2026-11-19). No Rocq work.
- **Points on actions instead of one point per end.** Kobayashi and
  Padovani annotate every action with its priority. We keep one point per
  end, S@x, and compute later points (x⁺, fields x·κ). Equal
  expressiveness for finite protocols, finite types for recursive ones,
  point-free session types. Written points would only read better. Author
  (2026-11-19): queue it as a discussion item. No Rocq work.
- **Type-directed ticket split at spawn.** Today a spawn halves the
  tickets (child ⌈tk/2⌉, parent ⌊tk/2⌋), which forces the doubling form
  ϑ(r) = 2^s r + b and the side condition tok. If the child got exactly
  its need b_c, needs would just add up. That needs the split to be fixed
  outside the step index without the relation reading types. Discuss
  together with per-end link budgets. No Rocq work.
- **Programs the topological relation accepts and ours rejects.** The
  earlier relation (D'Osualdo, van den Heuvel, Thiemann, Weidner) needs no
  order, only a per-extruded-channel split at the interface. Candidate:
  thread A sends a flag to thread B, then both close a and b in the order
  the flag picks. Deadlock free. Ours rejects it: A needs x_a ≺ x̄_b and
  x_b ≺ x̄_a, B needs x̄_a ≺ x_b and x̄_b ≺ x_a, a cycle, and the points
  are fixed before the flag exists. Check the earlier relation accepts it
  (internal channels only, so the interface split is not involved).
  Later: a hybrid that cuts along one channel without order facts
  (Wadler-style) and uses points only for cycles.
  **Important, to discuss (author 2026-11-19).** The author wants the
  relation to admit, inside a component, whatever can be proved by hand.
  Today it does not: readiness is stated against a strict order of points
  that grows only at creation, so a hand proof must exhibit points, and
  the flag program (channels created before the flag) is outside the
  relation in every world, not only untypable. Mechanize that, as
  db_component_unrealizable (examples/DataBranch.v) does for the
  dispatcher. Options discussed:
  (a) one-end lemma: a process with one free end, in either relation,
      offers that end when stuck; this would allow a mixed P-Connect along
      a single channel (cut of one channel, payload condition as in
      docs/extensions/regions.md §3, cut points stay on our side); needs
      their definitions (dosualdo2026logical is metadata only in the
      store, read and record facts first);
  (b) a single-channel cut rule in our own relation that needs no world
      agreement, orders only inside cycles (the hybrid);
  (c) world growth at a decision with an owner token (data-dependent
      constraints, regions.md §1 pending choices, BranchWorlds.v), and
      facts guarded by shared values (regions.md §6);
  (d) state and check that we subsume their static system, which types
      trees (one point per end may already suffice). Semantic inclusion of
      their relation in ours is false in general.
