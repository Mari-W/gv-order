# Rewrite progress

The rewrite of docs/redesign/proposal.md lives in v2/ (logical name `GV`).
The old development in theories/ stays untouched.

## Stages

| Stage | Content | Status |
|---|---|---|
| S1 | language | done |
| S2 | points, worlds, types | open |
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
  renamings (v2/lang/ChannelSwap.v): `tstep_cmap` for every renaming of
  names, `pstep_pswap` and `safe_pswap_iff` for transpositions, and
  `oswap_csub`, the link substitution commuting with a transposition.
- S1.7. Runs and lock freedom over the new semantics (v2/lockfree/Fair.v,
  Reach.v, TauThread.v): `wfair`, `lf_run`, `lock_free`,
  `lock_free_reach`, `lock_free_reach_of`, `no_tau_divergence` and
  `thread_acc`. v2/CheckAll.v lists 22 results, and `make check` reports
  all 22 closed under the global context. No `Admitted` and no axiom.
  v2/README.md says what v2 holds and how to build it. S1 done.
