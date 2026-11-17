# Rewrite progress

The rewrite of docs/redesign/proposal.md lives in v2/ (logical name `GV`).
The old development in theories/ stays untouched.

## Stages

| Stage | Content | Status |
|---|---|---|
| S1 | language | done |
| S2 | points, worlds, types | in progress (examples open) |
| S3 | generic relation | open |
| S4 | generic compatibility | open |
| S5 | static fundamental theorems | open |
| S6 | fuel | open |
| S7 | cost judgment | open |
| S8 | soup and adequacy | open |
| S9 | lock-free composition and soundness | open |
| S10 | paper | open |

## Deviations

- Lexer (A.1). A subscript or superscript that is an identifier is set off
  by spaces, `V[κ]^W _ n⟦Θ ⊢ T⟧`, `Θ ; Γ ; Δ ⊢^F _ W t : T`,
  `ready _ W(Θ ∣ F, t)`. Rocq lexes `W_n` and `_n` as identifiers. LaTeX
  ignores the spaces, so the paper keeps the same string. Where the
  subscript follows a symbol, `⊢_W`, `⊨_W`, `⊫_W`, `⊪_W`, no space is
  needed.
- Lexer (A.1). The field x.κ is written `x·κ`. Rocq lexes `x.κ` as a
  qualified name.
- Lexer (A.1). The dual point x̄ and the dual end ō are written `x‾` and
  `o‾`. Rocq lexes `x̄` as one identifier.
- Lexer (A.1). The superscript of the soup keeps its braces,
  `S^{N,W} _ n⟦Σ ⊢ T⟧`, because LaTeX needs them for a two-letter
  superscript and Rocq lexes them.
- Lexer (A.1). `ready` is a keyword, so no Rocq name can be `ready`. The
  definitions stay `ready_t` and `ready_p` as A.2 says.

- S1, select. `select` carries the branch index i (a bool), as §2.8 writes
  `select_i`. The field κ_i where the end continues is a function of i and
  belongs to the point algebra of S2.
- S1, creation. `new_ℓ` is the nullary operator `ENew ℓ`, and the constant
  is `k_new ℓ` = λx. let ∗ = x in new_ℓ. Family labels and field labels are
  `nat`. The label of `new_κ o` carries the anchor o and the new name, and
  so does its event, because O-NewAt reads the anchor.
- S1, link. The link substitution `csub o1 o2` maps o1‾ to o2 and o1 to
  o2‾. End names no longer follow points, so a link of c⁺ and d⁺ is
  typable and its partner c⁻ must become d⁺. For the old polarity
  discipline the map agrees with the old `chsubst`.
- S1, one semantics. `istep` is the only definition of process steps. The
  plain semantics `pstep` is its erasure, and `pspec`, the multiset view
  that the relation of S3 inverts, is characterized by the theorem
  `pstep_iff`, not by a second definition.
- S1, runs. Runs, fairness and lock freedom use the steps of a closed
  configuration (`itstep`, every event but an external offer), as the old
  runs did. Run labels are `option event`, `None` for the stutter of a
  stuck end.
- S1, erasure for τ-divergence. `cerase` maps every end to one end, sign
  included, because `csub` can flip the sign of an end.
- S1, preservation. The runtime invariant preserved by closed steps is
  closedness of every thread (`itstep_closed`). The old Safety.v proves
  progress only. An external receive may bring an open value, so the
  invariant is stated for closed steps.
- S1, toolchain. The opam switch has Rocq 9.2, so v2 is built and tested
  with 9.2.

- S2, scopes. The tokens ⁺ and ‾ serve ends and points. The end notations
  live in `cend_scope` (key `cend`), the point notations in `point_scope`
  (key `pt`), each bound to its type. A list literal `[a; b]` clashes
  with the `;` of the typing notations inside a statement, so statements
  write `a :: b :: []`.
- S2, the merged judgment. The judgment of Q11 is `typed W N Θ Γ Δ F e T
  a c ϑ`, notation `Θ ; Γ ; Δ ⊢^F _{W,N} e : T^a ▷ c ; ϑ`. The paper
  string keeps the braces of the two-letter subscript, as the soup does.
  The DF judgment `Θ ; Γ ; Δ ⊢^F _ W t : T` of A.2 is `dftyped`, the same
  rules without cost premises, aging and capture.
- S2, floors. The floor h of an arrow ranges over ℕ ∪ {∞}, not ℕ. E-Abs
  restates a captured end at credit h, and §2.17's choice h = 0 then
  leaves the body unable to age the end by ∞. The DF instance takes
  h = ∞. A floor ∞ is met only by counters ∞.
- S2, credits of aggregates. A credit on a product, a sum or an
  existential is added to its parts. Aging, capture and subtyping push
  it inward, and the rules build aggregates at credit 0. E-Send checks
  the payload by aging it by one and subtyping it to the floor, as the
  old C-Send did, not by the literal a ≥ b + 1 of §2.17, which fails for
  a pair payload at N = ∞.
- S2, session instances. At N = ∞ a box body and a force see only
  session instances with the annotations of N = ∞ (`sinsts`). Without
  this, a box body typed at N = ∞ would have to type at instances with
  finite payload credits, where an end received at a finite credit
  cannot be aged by ∞.
- S2, subtyping. An existential may drop facts of its constraint under
  subtyping, so world extension preserves E-New, whose result names the
  laws of W. The DF judgment converts by subtyping of erased types.
- S2, E-Let. A rule types the redex (λx. e2) e1 as let x = e1 in e2,
  shaped like E-Let∗. Without it `let (a, a′) = new_ℓ in e` has no
  typing that captures more than one end, because E-Abs bounds all
  captured heads by one lower point.
- S2, points in session types. Point instantiation leaves session types
  alone, and E-Send and E-Recv ask the payload point-closed below its own
  binder (`pscoped m T`), as the old development scoped payloads. The
  first port instantiated inside payloads, and then instantiation did
  not commute with unfolding (a free point variable of a µ-body is
  captured on unrolling), so point substitution failed.
- S2, knownness. No premise asks a point known to W. Generated roots are
  known by construction and the budgets that read knownness are gone.
- S2, process typing. `ptyped N W Σ p T` carries the refill N, and
  `Σ ⊢_W p : T` is the instance N = ∞. P-Term asks the ends of Θ_B dual
  by the syntactic `dual` at dual points, with credit N. P-Connect and
  P-Join ask `w_fams W1 ## w_fams W2`. Renaming apart is the lemma
  `typed_gmap` applied before the join, and it needs a permutation of
  families (a right inverse of the root renaming), because E-Box
  quantifies over every session instance.
- S2, structural lemmas. `typed_pinst` and `typed_gmap` assume
  `world_wf W`. The future-variable domain of the target context of
  `typed_pinst` is a subset of the source's.
- S2, deferred. `seq_sound` for transformers with offset ∞ is stated in
  §2.17 but not used before S7, and S2 does not prove it.

## Log

- S1.0. Lexer test v2/test/Lexer.v of every judgment and token of
  Appendix A over dummy carriers. All parse, and `make test` checks that
  all 27 checks print as written (v2/test/Lexer.expected).
- S1.1. Syntax (v2/lang/Syntax.v). Ends `c⁺` and `c⁻` as two constructors
  of `cend`, values `Chan o`, saturated operators `Op k e` and `ENew ℓ`,
  the constants of GV as derived λ-values `k_send` to `k_new_at`, one
  renaming `emap` over end maps with `cmap` and the link substitution
  `csub` as instances. Notations `c⁺`, `c⁻`, `o‾` in v2/lang/Notations.v,
  checked by v2/test/LangNotations.v.
- S1.2. Thread steps (v2/lang/Semantics.v) with the T-Act rules as
  constructors `t_act_*` and one frame rule `t_act_ctx`. Labels of send and
  spawn carry the transfer set M, and `tstep_transfer` proves M = fends v.
- S1.3. Process steps (v2/lang/Process.v). One instrumented semantics
  `istep` with thread ids and events, constructors `p_act_*`. The plain
  semantics `pstep` is its erasure, `pstep_iff` gives the multiset view and
  `pstep_lift` replays a step on every lifting.
- S1.4. Safety (v2/lang/Safety.v). `act_offer_sig` proved once and
  `act_offer` as its corollary, `act_step`, `tstep_progress`,
  `istep_progress`, `proc_progress`, and `itstep_closed` (closed threads
  stay closed).
- S1.5. Harmony (v2/lang/Harmony.v). A reduction semantics `red` on soups
  with evaluation contexts, defined without labels, and
  `harmony : red p p' ↔ preduction p p'`.
- S1.6. Thread simulation tools (v2/lang/ThreadSim.v) and channel
  renamings (v2/lang/ChannelSwap.v) with `tstep_cmap` for every renaming of
  names, `pstep_pswap` and `safe_pswap_iff` for transpositions, and
  `oswap_csub`, the link substitution commuting with a transposition.
- S1.7. Runs and lock freedom over the new semantics (v2/lockfree/Fair.v,
  Reach.v, TauThread.v) with `wfair`, `lf_run`, `lock_free`,
  `lock_free_reach`, `lock_free_reach_of`, `no_tau_divergence` and
  `thread_acc`. v2/CheckAll.v lists 22 results, and `make check` reports
  all 22 closed under the global context. No `Admitted` and no axiom.
  v2/README.md says what v2 holds and how to build it. S1 done.
- S2.1 to S2.4. Points with generated roots, fields and duals
  (v2/types/Points.v), worlds with family laws, the join, the restriction
  and R7 as `strict_join_iff` (v2/types/Worlds.v), credits and
  transformers (v2/types/Costs.v), credited types (v2/types/Types.v), the
  merged judgment `typed`, its DF projection `dftyped` and process typing
  `ptyped` (v2/static/Typing.v).
- S2.5. Conservativity in both directions (v2/static/Conservativity.v),
  `typed_dftyped` and `dftyped_typed`.
- S2.6 and S2.7. World extension, term-variable renaming, channel
  renaming, renaming of families and generated roots, point substitution
  (v2/static/Weakening.v, Renaming.v, PointSubst.v).
- S2.8. The client and server cycle of §2.5 types with family laws
  (v2/examples/ClientServer.v, `cs_typed`). CheckAll lists 38 results,
  all closed.
