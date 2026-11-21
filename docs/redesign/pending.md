# Pending changes: the map leads, the Rocq follows

## Morning report, overnight run of 2026-11-20

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed.
Step 0 merged redesign (0c7756e). The explorer sources conflicted where
one side had removed `prim` and the other `hbot`, and the merge removes
both. One note of the merged map (ev.pick) used the word "holder" and a
sentence of 37 words, and the merge rewords it.

- Stage 1, entry 6, credits only on ends and closures. Done (61ad17b,
  dccb8a4). E-Send ages its payload operand by one and subtypes it to the
  declared payload. Sub-Ex now compares bodies by `tsub`, so V's
  monotonicity along subtyping is proved under every point instantiation.
- Stage 2, entry 13, P-Connect over the shared roots. Done (69526fa,
  f0f9344). `ptyped_strict`, `p_connect_join`, `strict_bare`. p_join is
  gone and the process theorems lost their `strict W` premise.
- Stage 3, entry 14, ⊥ folded into heads. Left out by the rule "only if it
  shortens proofs" (d5ff8e6), with the counts in entry 14.
- Stage 4, entry 2, one plain new. Stopped at the feasibility check of
  risk (a) (d5ff8e6). The soup fixes its state for every index and
  updates it from the event, which names neither the point nor the
  constraint of a plain new, so a choice per level cannot be fixed. Three
  repairs and a note on risk (b) are in entry 2. No Rocq change.
- Stage 5, entry 7. Partly done (f756da5, 86c4991). `fp_unrealizable`
  (v2/examples/FlagPair.v) shows two threads that branch on one received
  flag are in E together in no pair of worlds with a strict join. The four
  programs of rejects.js are not mechanized, v2 can neither build an
  infinite run nor invert `typed`.
- Stage 6, entry 4, a weakly fair run exists. Not done (4d37d51). A run is
  a function, and building it from Prop-level steps needs dependent choice
  or a step function that v2 lacks.
- Stage 7, entry 5. Not reached, it needs stage 6.
- Stage 8, the map's notation in the Rocq. Partly done (96d5f7e, 4d2ec2b).
  `tfin` is ϑ(0) ∈ ℕ, `cr_le` is cr(Θ) ≤ N, `soup_gen_iff` reads the soup
  as relation, fuel and `soup_consistent`. Not done: one map Φ in the
  fuel layer, and Pbody over pstep. The open question is written up
  under entry 8 and nothing is decided.
- Stage 9, remove the clause (fuse) of P. Not done (dca9d20, entry 15).
  A probe that dropped the clause fails first in Relation.v
  (`Pbody_mapX`), and the clause has uses in 14 files. Entry 15 lists
  what the work needs. The probe was reverted.
- Stage 10, entry 11, faithfulness audit. Done for the cited Rocq names and
  the theorem statements (ca7c7a7). Six dangling names, names cited in
  the wrong file, and four theorems on the map that still ask `strict W`.
- Design checks (c258c50, 8823fb2), write-ups only. No future variables
  holds, checked by two lemmas in a scratch file
  (docs/redesign/check-future-variables.md). Per-end capture holds on
  paper and removes the floor h (docs/redesign/check-per-end-capture.md).
  The type-directed ticket split does not go through as stated
  (docs/redesign/check-ticket-split.md).

Final state of v2 at e64095d. `make -j2` builds with no error.
`make test` passes, after the expected outputs of CostNotations,
FuelNotations, GuardNotations and SoupNotations were updated to the new
signatures (e64095d). `make check` reports 93 of 93 results closed under
the global context. No Admitted, no new axiom. Map. No edit after the
merge. check.js reports 0 mathjax errors and lint-map reports 0 coined
words and 0 sentences over 35 words.

Since 2026-11-19 the author reviews the explorer map (docs/explorer) and
asks for changes. Each change goes into the map at once and into this list.
One proof-repair agent later implements the whole list in the Rocq in a
single run. Where a change turns out implausible in the Rocq, the agent
reports and the author decides.

Each entry: what changes, where the map already shows it, what the Rocq
must do, open questions.

## Decisions of the author on the overnight report, 2026-11-20

- **Entry 2, plain `new`.** Families stay in the Rocq for now. The author
  does not want families, facts fixed in the world instead of in the type
  of `new`. Proposal of 2026-11-20, on the map as planned: a creation
  choice χ, fixed before the level as A and Φ are. The lock-free semantic
  judgment reads `∃ N, a, χ. erase(q_a) = p ∧ ∀ n. a ∈ S^{N,W,χ}_n`, the
  thread relation is `E[κ_L, χ]`, O-New under lock freedom asks
  `(π, C) = χ(e, Θ)(a)` for the fresh root a, and `lf_next^χ` places the
  new ends at π and grows the world by C. Under deadlock freedom O-New
  keeps its existential. For a typed thread χ is the choice of its E-New
  step. Open: whether χ applied to the creating term counts as reading
  syntax (it is an existential function the relation applies, no clause
  inspects the term), and what χ is keyed on if not (e, Θ). A write-up
  checks the proposal on O-New and the fundamental theorem. The same
  write-up checks a condition on C that keeps the union of
  the worlds of a run well-founded. Test it against the client-server
  constraint `ι+k ≺ (κ+k)‾` and against the growing chain `rx-chain`. A
  criterion that compares ranks within one position only is unsound,
  because it accepts `rx-chain`, which is not lock free. Decide after the
  write-up.
- **Entry 15, the clause (fuse).** Kept. The map writes it readably as
  `(h, D)·p` for `pfuse h D p` and `(h, D) ∈ Fus(Σ, p)` for
  `fuse_ok h D Σ p`. No removal attempt.
- **Entries 4, 5 and 7.** Build inversion lemmas for `typed` through
  E-Case, E-Close, E-Let and P-Connect, then mechanize the static
  rejections (the flag example `sb_untypable`, `FlagPair`, the programs of
  `rejects.js`). State "a weakly fair run exists" with dependent choice as
  an explicit hypothesis of the lemma, no axiom. Entry 5 follows from it.
- **Entry 14b, no future variables.** Adopt in the Rocq.
- **Entry 12, per-end capture.** Adopt in the Rocq.

## Open

1. **Events folded into labels (N.2).** Three cases `solo i α`,
   `sync i j o σ`, `offer i σ`. Started on branch redesign-clean3 in the
   worktree .claude/worktrees/redesign-s4: N.1 (P-Term asks `tfree`,
   `prim` gone) is committed there (6986a1c), N.2 is uncommitted and
   built, without make test, make check or the map. The agent stopped when
   the session ended. Map: not yet. Rocq: finish N.2 on that branch.
   Status 2026-11-20: done in the Rocq (fc8a020, EvSolo, EvSync, EvOffer
   in lang/Process.v) and on the map (56e4eb4), merged into redesign.

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
   Overnight stage 4, 2026-11-20: stopped at the feasibility check of (a),
   no Rocq change. Verdict on (a): the plan fails as stated. The soup
   fixes the state `a` once for every index (`lf_sem := ∃ N a, ∀ n, a ∈
   S^{N,W}_n⟦Σ ⊢ T⟧`, soup/Soup.v), and a run computes the next state by
   the index-free update `own_next` from the event alone. The event of a
   plain `new c` names neither the point π nor the constraint C. If O-New
   picks `∃ S π C` at each level, the state after the creation needs the
   point of the new ends in K to equal π_n for every n, and the world to
   grow by one C for every n. Nothing forces π_n and C_n to agree across
   levels. Downward closure of E does not rescue it, because the choices
   form an infinite set (every field κ, every constraint C), so no
   pigeonhole argument finds one choice valid at every level. Repairs to
   decide on: (i) a finite menu of (π, C) per creation, determined by Θ,
   with downward closure and pigeonhole giving one choice for all levels
   (the client-server constraint `ι+k ≺ (κ+k)‾` for all k must then be one
   entry of the menu); (ii) the soup carries its own world and points,
   and O-New in the lock-free relation is stated at the world and point
   the soup offers, quantified universally over the offers that keep the
   world strict, which turns the thread's choice into the environment's
   and loses the creations that need a particular C; (iii) per-level
   worlds and points in the soup, which breaks the rank argument, because
   the rank of a pending thread is the point of its end in K at that
   position and the criterion compares it across positions. Note on (b)
   from the same reading: lockfree/Criterion.v asks one well-founded order
   on ranks for the whole run, so with growing worlds the order would be
   the union of the worlds along the run, which a loop that creates below
   its previous channel makes non-well-founded although every single
   world is well founded. A criterion that compares ranks only within one
   position would be needed. (c) needs nothing beyond strictness.

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
   Overnight stage 6, 2026-11-20: not done. A run is a function
   `nat → config`, so building one picks a step at every position. The
   semantics gives steps only as propositions (`istep`, with the received
   value, the fresh channel and the new thread number chosen inside), and
   a Prop existential does not yield a function without the axiom of
   dependent choice, which the rules forbid. The lemma needs a function
   that computes a step of a given thread when it has one: a redex finder
   for one thread, a partner search for synchronisations, fresh names,
   and a decision whether the thread is enabled, for the round robin.
   v2 has none of these, and I did not write them in this run.

5. **Padovani-style lock freedom as a corollary (low priority, queued
   2026-11-19).** From `lock_free p` and item 4: for every q reachable
   from p and every thread pending in q, some q' reachable from q has a
   step in which that thread takes part (Padovani 2014, Def. II.1, in our
   per-thread form). Map: one line in the theorems section once proven.
   Overnight stage 7, 2026-11-20: not reached. The corollary starts a
   maximal weakly fair run from the reachable q, which is entry 4.

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
   Done in the Rocq 2026-11-20 (61ad17b, overnight stage 1). Credits sit
   on `TSess S x a` and `TLolli … a` only, aging and capture recurse
   structurally, E-Send types its operand at `Tp ⊗ S₀@x^a`, asks
   `tage 1 Tp Tp'` and `tsub Tp' (payload_at m T x)`, and payloads carry
   no credit. No proof used the outer offset of an aggregate. Sub-Ex now
   compares the bodies by `tsub` instead of `teq`, so the lemma that V is
   monotone along subtyping is proved under every point instantiation
   (`Vrel_tsub_pinst`). The cost fundamental theorem, both fundamental
   theorems and every example build unchanged in shape. In the lock-free
   examples a box result is now the closure `(T ⊸ U)^∞`, and the credits
   of its argument sit on the ends of `T`.

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
   Overnight stage 5, 2026-11-20 (f756da5). Done: v2/examples/FlagPair.v.
   Two threads branch on one flag that a third party sends, the first on
   a at x and b at y, the second on ā and b̄. `fp_unrealizable` shows that
   no pair of worlds with a strict join has both threads in E for both
   flags. The first thread with inl asks x ≺ ȳ (`fp_gate`), the second
   with inr asks ȳ ≺ x, a cycle. One thread alone is not rejected, its
   arms ask x ≺ ȳ and y ≺ x̄. Closed under the global context.
   Stopped: the four programs of rejects.js. Each needs two proofs that
   v2 has no tools for. Not lock free needs an explicit infinite maximal
   weakly fair run with a thread pending at every position, and v2 builds
   no run, it only reasons about given ones (lockfree/Fair.v). Not typable
   needs inversion of `typed` through E-Sub, E-Open, E-Pack, E-Box and
   E-Force, and v2 has no inversion lemma for `typed`. The badges stay
   "to be mechanized".

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

   Overnight stage 8, 2026-11-20 (96d5f7e), the Rocq side of the map's
   notation. Done: `tfin ϑ` is ϑ(0) ∈ ℕ (types/Costs.v) and replaces
   `∃ tk, meets ϑ 0 tk` in p_term, fsem_of_cost, lf_p_term and
   lf_soundness_source. `cr_le Θ N` is cr(Θ) ≤ N (static/Contexts.v) in
   fsem_of_cost and thfuel_id. `meets ϑ r tk` carries the comment
   ϑ(r) ≤ tk. `soup_consistent` and `soup_gen_iff` (soup/State.v) read the
   soup as relation, fuel and consistency. Names and comments only, no
   Rocq notation, because a notation that starts with ϑ( or cr( clashes
   with application. Not done: one map Φ for Π and φ in FuelE and FV,
   with Φ↓ and spare Φ (FuelE and Vfuel occur in 20 files, and fuel/*.v
   and cost/*.v hold 302 lemmas that pass the two maps), and the step
   clause of Pbody over
   pstep (it changes the definition of P that stage 9 also changes, so
   it belongs to that work).
   Open question for the author, facts only. O-New picks the session
   type of a new channel by `∃ S` in relation/Relation.v (o_new) and F-New
   by its own `∃ S` in fuel/Fuel.v (f_new). The two obligations live in
   two step-indexed predicates that the soup combines only at the end,
   so a shared existential needs FuelE to take the relation's choice as
   a parameter, or one predicate for both. Then the soup could ask
   `Π = sty ∘ A` and drop Π. Nothing decided.

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
    Overnight stage 10, 2026-11-20, against redesign-clean3 after stages
    1, 2, 5 and 8. Scope: every Rocq name the map cites (601 references in
    data.js, checked by a script against the definitions in v2/) and the
    statements of the theorems section. The formulas of the other blocks
    were not compared symbol by symbol. No map edit, none of the
    differences is a statement the Rocq proves false. Differences that no
    entry queues:
    (1) Names that no longer exist. ty-ann cites `cr_df` (gone with entry
    6). age.credit cites `age_credit` (now `age_sess` and `age_arr`).
    P-Connect.strict cites `p_join_iff_connect` (gone with entry 13, the
    rule now rests on `strict_join_iff` and `ptyped_strict`).
    th.live-fundamental and th.live-fundamental-typed cite
    static/LiveFundamental.v, which does not exist (both theorems are in
    static/Fundamental.v). ctx.only cites `tenv_only` (the Rocq name is
    `lenv_only`). syn.let cites `t_act_let` (the steps are
    `t_act_let_unit` and `t_act_let_pair`).
    (2) Names in the wrong file. The blocks r-base, r-fun, r-data,
    r-boxes, r-ex, r-act, r-threads, r-new and t-subs cite the rules
    `d_*` and `d_conv` in static/Typing.v, they are in
    static/Conservativity.v. V-Arrow.lb cites `lb_le` in
    relation/Relation.v, it is in relation/Readiness.v. fu.idle and
    sty.skip cite `idle` in fuel/Fuel.v, it is in types/Types.v.
    (3) Premises the Rocq dropped. th.fundamental-proc, th.lf-fundamental,
    th.soundness and th.lf-soundness, with their notes and signatures,
    ask `strict W`. Since stage 2 the Rocq theorems ask none
    (`ptyped_strict`), so the map states a weaker theorem. Entry 13 names
    the Rocq change and marks its map side done, but the theorems section
    still shows the premise.
    (4) Rocq results without a map entry: `fp_unrealizable`
    (examples/FlagPair.v), `soup_gen_iff` (the soup as relation, fuel and
    consistency, soup/State.v), `strict_bare` (types/Worlds.v),
    `p_connect_join` (static/Typing.v).

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
    Order: check per-end capture, then generalize arrows. Author
    (2026-11-19): per-end capture is important.
    Rocq: after the repair run (entry 6) is merged. Map: after the design
    is confirmed.
    Design check 2026-11-20 (docs/redesign/check-per-end-capture.md, on
    paper). Per-end capture holds and removes the floor h. Capture becomes
    aging by a, FV-Arrow asks `φ′ ≥ φ − a`, Sub-Arr asks `a' ≤ a`. E-SpawnLam
    then differs from E-Abs plus E-Spawn only in the arrow points.
    Done in the Rocq 2026-11-21 (next run, stage 1). `TLolli` lost the
    floor h, and `tcap`, `lcap`, `thcap` with their lemmas are gone. E-Abs
    asks `thage a Θ Θh` and `lage a Δ Δh`. FV-Arrow (fuel/Fuel.v, `Vty`)
    asks the captured counters of the ends that are not idle at least a,
    and at a call accepts any counters `f′ ≥ f − a`. Sub-Arr asks
    `fle a' a`. `Vty_age` carries the call bound through aging by
    `fsub_age` (types/Costs.v), and `cost_e_abs` builds the body
    environment from `envf_age` and `envf_mono` over `cle_fminus`. The
    capture of a closure inside a closure is aging the inner closure, so
    Cap-Arr went with the rest. Plausibility. Every lock-free and
    deadlock-free example builds unchanged in shape, the box results of
    the lock-free examples are closures at credit ∞, which ages a box by
    `age_free` as before. The forwarder thunk `T_thk` at credit 2 still
    types. The four programs of rejects.js stay excluded, because
    `lf_soundness` still builds with no new axiom and these programs are
    not lock free. The S4.18 counterexample concerns the clause (fuse) of
    P, which this stage leaves alone, and `fuse_ok` still forbids new
    pairs of partners outside D. SemBranch, TreeTopo and FlagPair read
    no arrow credit and build unchanged. The loss
    example of this entry (A at N and B at 1 captured at a = 1) now keeps
    A at N − 1, which is `lage 1` on the two entries.

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
    Done in the Rocq 2026-11-20 (overnight stage 2, 69526fa). p_term
    asks `strict W`, p_connect asks disjoint families and
    `strict (W1|_S ⊔ W2|_S)` with `S = wshared W1 W2`, and
    `ptyped_strict` shows every derivation sits over a strict world. The
    earlier rule is the lemma `p_connect_join`, and p_join and
    p_join_iff_connect are gone. fundamental_proc,
    live_fundamental_proc, soundness, live_soundness, lf_fundamental and
    lf_soundness lost their `strict W` premise. The source theorems keep
    it, because P-Term asks it. A world without facts and families is
    strict (`strict_bare`), which the forwarder uses.

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
    Overnight stage 3, 2026-11-20: not done, by the rule "only if it
    shortens proofs". The flag is threaded beside the head sets through
    hbot (41 uses in 20 files), lenv_bot (56 in 17), sf_unionb (47 in 18)
    and fs_bot (12 in 10), and the semantic reading `sf_den` interprets it
    by the arbitrary set B. Folding ⊥ into the sets replaces each case
    split on the flag by a membership test of ⊥ and changes every one of
    these sites, with no proof that gets shorter in sight. `LNone` and
    `LBot` stay apart as they are.
    Open questions from the author, to discuss:
    (a) Named variables on the map instead of de Bruijn indices in Δ, as
        for points (the Rocq keeps indices). Author: cosmetic, map only,
        low priority.
    (b) Future variables: Γ holds φ ↦ u (the fact u ≺ φ) and F names φ as
        the unknown rest. Each φ has exactly one fact, so Γ ⊢ x ≺ φ iff
        Γ ⊢ x ≼ u. Candidate: F = (X, above u) and no future variables in
        Γ. To check against fl and the semantic den_{ρ,B}. Author
        (2026-11-19): wanted if it holds.
        Checked 2026-11-20 (docs/redesign/check-future-variables.md). It
        holds, `fl_to_var` and `fl_from_var` compiled in a scratch file.
        The relation's future needs the rest "above u" beside its points.

15. **Remove the clause (fuse) of P (author 2026-11-19, overnight stage
    9).** Not done in the overnight run of 2026-11-20, no Rocq change.
    A probe dropped the clause from `Pbody` (relation/Relation.v:505) and
    built. The first failure is inside Relation.v (`Pbody_mapX`, which
    maps the clauses under the fusion), and everything that reads P
    waits behind it. The clause is used in 14 files (counts of
    `fuse_ok` or `pfuse`): compat/ConnectLink.v 27, ConnectCtx.v 22,
    Rename.v 17, ConnectP.v 17, Relation.v 14, ConnectSteps.v,
    ConnectFuse.v, ConnectExt.v, ConnectExtMsg.v 7 each, Connect.v 6,
    PTerm.v 4, Conv.v 4, ConnectRen.v 2, LiveDF.v 1. `Prel_rename`
    (compat/Rename.v:915) is the projection `Prel_fuse` at D = ∅ and
    becomes an induction on the level, as `Erel_rename` is. The link case
    of P-Connect (compat/ConnectLink.v, 585 lines) reaches the fusion
    when `csub o1 o2` gives the other component a dual pair, so it needs
    a second theorem beside renaming, that P at Σ ∪ {c⁺, c⁻} with the two
    ends dual at dual points gives P at Σ with c restricted. That theorem
    changes the readiness of the interface (two interface ends become
    internal, so `above_offered` stops reading them) and turns interface
    actions on c into internal synchronizations, so its proof has the
    shape of P-Connect itself. compat/ConnectFuse.v (396 lines), which
    shows the composite closed under fusions, would go. The question of
    bound restricted channels (quotient or binder) was not reached. The
    first test, the counterexample of S4.18, was not run.

## Done in the Rocq

(entries move here once the repair agent has implemented and merged them)

## Open discussion (not scheduled)

- **Cross-references everywhere on the map (author 2026-11-19, another
  day).** Every symbol in every formula should be hoverable and lead to
  its definition, which needs a restructure of the generator (one
  definition site per symbol, references by key). Today only the parts
  wrapped by hand or by the automatic word list are hoverable.

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
  (2026-11-19): queue it as a discussion item. No Rocq work. Author later
  the same day: not wanted for now, also not as a display on the map.
- **Type-directed ticket split at spawn.** Today a spawn halves the
  tickets (child ⌈tk/2⌉, parent ⌊tk/2⌋), which forces the doubling form
  ϑ(r) = 2^s r + b and the side condition tok. If the child got exactly
  its need b_c, needs would just add up. That needs the split to be fixed
  outside the step index without the relation reading types. Discuss
  together with per-end link budgets. No Rocq work. Author (2026-11-19):
  probably good, worth designing.
  Design check 2026-11-20 (docs/redesign/check-ticket-split.md). Not as
  stated. The soup needs the split fixed for every index, and a split by
  the child's need either reads its type or needs a classical pigeonhole
  over the finitely many splits. With exact splits needs become offsets
  `r + b` and `tok` goes.
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
  Correction of an earlier claim: it already does at the process level.
  ready_p (relation/Readiness.v) reads points only of interface ends, and
  internal channels carry none, so P⟦∅ ⊢ T⟧ asks exactly deadlock
  freedom of every reachable stuck state, and the flag program is in it by
  a direct proof. What rejects it is the route through typing: P-Term asks
  each thread to be in E, and E orders every end the thread holds.
  sem_p_connect composes any two members of P, so a hand-proved component
  composes with typed ones, provided it is ready at its interface (offered
  ends below the partner points of the ends it does not offer). Both
  points are obvious, no mechanization wanted. Options discussed:
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
  (e) Author: embed the topological relation in ours by one generic proof.
      Inside a component nothing is to show, internal channels carry no
      points. At the external channels replay the topological argument
      once, generically: their tree-shaped interface should let us choose
      points for the interface ends so that ready_p holds. Then every
      process in their relation is in our P, and composes with typed code
      by sem_p_connect. Open: which points the tree induces, and whether
      their interface readiness implies above_offered.
