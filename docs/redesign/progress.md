# Rewrite progress

The rewrite of docs/redesign/proposal.md lives in v2/ (logical name `GV`).
The old development in theories/ stays untouched.

## Stages

| Stage | Content | Status |
|---|---|---|
| S1 | language | done |
| S2 | points, worlds, types | done |
| S3 | generic relation | done |
| S4 | generic compatibility | open |
| S5 | static fundamental theorems | open |
| S6 | fuel | done |
| S7 | cost judgment | stopped at S7.1, report on F-Send and F-Spawn (see S7.1) |
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
  Superseded by decision Q13: S4 adds a primitive let and E-Let types
  it, so no rule matches the redex shape.
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

- S3, annotations. R^κ reads no annotation of a type. V at S@x compares
  session types after erasing their annotations (`seqv S' S` is
  `sequiv (sty_df S') (sty_df S)`), and costs, transformers, floors and
  credits are never read. With the exact ≈ of S2 the box clause would
  have to depend on N. E-Box at N = ∞ types the body only at
  session instances with the annotations of N = ∞ (`sinsts None`), while
  E-Force at a finite N instantiates at any hcontractive instance, and
  `dftyped` converts between types equal up to `ty_df` (D-Conv). An
  annotation-blind relation serves both. The session types in the
  environments keep their annotations, so S6 reads each end's cost
  protocol off the environment of the live relation at the same index.
  V-Box quantifies over every hcontractive instance.
- S3, environments. The relation's environments Θ and Σ are `senv`, an
  end mapped to S@x with no credit. `tenv_erase` drops the credits of a
  typing environment, for S4 and S5.
- S3, cost tables. `ctable` carries two side conditions, κ(receive) ≥ 1
  and κ(β) = 0 → κ(send) ≥ 1. A receive reads V of its payload at the
  level of its continuation in a negative position, so that level must
  lie below n, and when β is free V at level n is defined together with
  E at level n (by fuel on the size of the type), so a free send would
  read V at level n at a payload of unbounded size. Both tables meet the
  conditions. The cost of a branch is κ(receive), of select and close
  κ(send).
- S3, payload level. A send reads its payload at the level of its
  continuation, n − κ(send): n in κ_DF, n − 1 in κ_L (§2.8 leaves the
  level open). Q-Send likewise.
- S3, spawn. O-Spawn reads the thunk at 1 ⊸ 1 at the parent's level n
  with the generic arrow clause, whose part at level n itself is read
  inside the fixpoint (`Varr` with the fixpoint at ∗). In κ_DF that part
  is empty, so the thunk is in V at level n as §2.8 writes
  (`Varr_spawn_iff`). In κ_L it is today's `Vspawn`.
- S3, Kripke. Every unfolding of E and P quantifies over W1 ⊒ W
  (decision Q9 a). The receive clause has no Kripke quantifier of its
  own, because the outer one covers it.
- S3, creation. O-New holds for every generated root g of family ℓ that
  is the root of no point of Θ (`gfresh`) and asks the new name fresh for
  Θ (`cfresh`), as the old O-New did. O-NewAt asks the anchor held. Both
  create the ends at S and `dual S`.
- S3, the step clause. E and P state one conjunct per label (`Esteps`,
  `Psteps`), because the inductive fixpoint must occur strictly
  positively and a `match` on the label hides it. `Eobl` and `Pobl` read
  the obligation off the label, and `Esteps_iff`, `Psteps_iff` relate
  the two forms. The obligations carry the paper's names, `o_send`,
  `q_recv` and so on.
- S3, process steps. P quantifies over the instrumented steps of every
  lifting of the soup (`istep`, with events), not over `pspec`. A τ step
  costs `ev_cost κ ev`, so Q-Admin and Q-Comm are one clause `q_tau`.
  The external send, receive, close, choice and link clauses port
  Q-Send (`send_split`), Q-Recv (`recv_ok`, `recv_env`, `recv_back`)
  and the rest of theories/relation/LogicalRelation.v to one entry per
  end. They are checked only by S4.
- S3, readiness. An end is offered when it is a subject of the label and
  Θ holds it. No shape test picks an entry, because each end has one.
- S3, futures. The relation's futures are sets of points. The static
  future of S2, with a future variable and the ⊥ flag, is interpreted by
  the semantic term judgment, which S4 defines with the bind lemma.
  S3 defines the semantic process judgments `Σ ⊨_W p : T` and
  `Σ ⊫_W p : T` (`sem_ptyped κ`).
- S3, syntax. The `;` of the typing notation of static/Typing.v breaks
  the record syntax and the tactic forms `pose proof (t); tac` and
  `exists a; tac` after a term at level 60 or above. Records live in
  relation/CostTable.v, which does not import static/Typing.v, and
  proofs write `pose proof t as H` and `(exists a); tac`. stdpp's `∉`
  sits at level 80, so `x ∉ X ∧ P` is written `(x ∉ X) ∧ P`.

- S6, one clock (Q10). Q10 (a) asks one clock if the bind lemma
  survives. It does, because `FuelE_bind` reads no cost of a β step. One clock
  fails one stage later, at E-Box in S7. The box
  `!(f = force f)`, forced, types by the merged judgment at cost 0, and
  its run is β steps forever. With β free and E a least fixpoint over
  free steps, as in κ_L, FuelE at level 1 has no derivation for it, so
  `cost_fundamental` is false. With β free and a greatest fixpoint, the
  term has fuel, but the semantic E-Box lemma has to read the self at
  the level it proves, with no step in between, and the induction on the
  index that proves it at two clocks has nothing to recur on. The live
  relation gets past the same point with the guard. One clock would put
  `guarded e` into `cost_fundamental` and change A.3. S6 takes the
  fallback Q10 (b), where every step costs one level, β, new, spawn and link
  included, as theories/lockfree/LFFuel.v does. Argued, no Rocq. The
  soup of S8 keeps two clocks (F25).
- S6, the refill (Q4). FuelE^N and the closure and box clauses of Vfuel
  hold at every refill N′ ≥ N (Kripke in N), as the old FuelE held in
  every extension of the budgets (`wbext`). Plain monotonicity in N has
  no proof. The receive clause takes incoming values at the receiver's
  refill, and a closure in Vfuel at N′ need not be in Vfuel at N, for
  instance one that refills an end and then acts N′ − 1 times on other
  ends while it holds that end. With the quantifier, `FuelE_mono` is
  monotone in N and in the counters, which is what the maximum at
  composition needs.
- S6, protocols (Q11). Π maps an end to its session type (`penv`) and
  nothing else. FuelE does not take the relation's `senv`, because it
  reads no point. S8 sets Π to the session types of the live environment
  A_t at the same index. No cost protocol is chosen and nothing is
  paired.
- S6, idle ends (Q5). An end is idle when its session type is Skip
  (`idle S` is `unfoldS S = SSkip`). No rule acts on Skip, and its dual is
  Skip. F-Wait (`f_act`) asks the acted end not idle, and F-Tick and the
  hand-over (`fspare`) skip idle ends. Counters evolve by the one update
  `refill`, `fhand`, `cnew`, whatever the protocols. S8 still needs
  `idle S ↔ idle S'` for S' ≃ dual S. The controller (#20) is not typed.
- S6, counters. Counters, the frame and N range over ℕ ∪ {∞}, like the
  floors of S2. At N = ∞ every fresh and refilled counter is ∞, and a
  tick keeps ∞.
- S6, threads. A thread returns at `RThread`, any value, holding no end
  (Π = φ = ∅). It replaces `CAny`. `FuelE_thread` turns FuelE at a
  primitive type into FuelE of a thread.
- S6, payloads. The send and receive clauses read the payload at the raw
  type T^b of the session type, with its bound point variables free,
  not at `payload_at m T x`. Vfuel reads no point (`Vfuel_pinst`), so the
  two agree.
- S6, boxes. The box clause of Vfuel quantifies over the session
  instances `sinsts N′ ss` of E-Box and reads no point instance.
- S6, renamings. FuelE is closed under end maps `cend → cend` injective on
  the held ends (`kinj`), because the link substitution `csub` maps ends,
  not channels.
- S6, deferred. `seq_sound` with offset ∞ is not used by the bind lemma.
  S7 proves it with the cost half of the judgment.

- S7, transformers. `seq_sound` asks `tok t1 t2`, the side condition the
  rules already carry, and covers offset ∞ (v2/cost/Transformers.v). A
  transformer with offset ∞ is met nowhere, so those cases hold
  vacuously.
- S7, fuel exactness. F-Send and F-Spawn read the transfer set M off the
  label and ask M ⊆ dom φ with the payload in `Vfuel` at `mres M Π`.
  No clause of `Vfuel` relates the ends a value mentions to its map Π,
  so `Vfuel` holds closures that no send and no spawn can hand on. This
  is the fuel form of `send_gap` (stage S4), which decision Q14 repaired
  for V and not for `Vfuel`. `fw_counterexample`
  (v2/cost/FuelGap.v) shows that `fsem_of_cost` of A.3 is false for the
  definitions of S6. See S7.1.

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
- S2.9. Cycle, FreshBetween, FreshMany, FactoryEx (two factories, B.1
  #51) and GrowRing (after the reordering of B.1) type with anchors and
  family laws (v2/examples/, `cy_typed`, `fb_typed`, `fm_typed`,
  `fx_typed`, `rg_typed`). GuardCex as written is rejected (argued): its
  box body blocks on a channel created at a fresh root while the
  caller's future is abstract, and it holds no end to anchor at.
  SegmentInterleave and ChoiceNegative are not ported. CheckAll lists 43
  results, all closed. S2 done.
- S3.1. `sfix` (v2/relation/Sfix.v), cost tables κ_DF and κ_L
  (v2/relation/CostTable.v), readiness `ready _ W(Θ ∣ F, t)` and
  `ready _ W(Σ, p)` (v2/relation/Readiness.v), and the definitions of
  `V[κ]^W _ n⟦Θ ⊢ T⟧`, `E[κ]^W _ n⟦Θ ⊢ T⟧^F`, `P[κ]^W _ n⟦Σ ⊢ T⟧`
  (v2/relation/Relation.v).
- S3.2. Transparent maps of one unfolding and the induction principles
  `Eind_ind'`, `Pind_ind'`, monotonicity of one unfolding in its readers,
  fuel independence of V (`Vbody_fuel`), and the characteristic
  equations `Vrel_*_iff`, `Erel_S_iff`, `Erel_S_ind`, `Prel_S_iff`,
  `Prel_S_ind`. The arrow reads `Vrel κ j → Erel κ j` at every j with
  j + κ(β) ≤ n (`Vrel_lolli_iff`).
- S3.3. Values, monotonicity in the world, downward closure and
  antitonicity in the future (v2/relation/Closure.v). `adequacy`,
  `live_adequacy` and the generic `adequacy_gen` (v2/relation/Adequacy.v),
  with two sanity checks, `Prel_done` and `Erel_beta_unit`.
- S3.4. Notation test v2/test/RelationNotations.v, README section,
  CheckAll lists 71 results, all closed. No `Admitted` and no axiom.
- S6.1. FuelE^N and Vfuel by credited types (v2/fuel/Fuel.v): the
  obligations `f_beta` to `f_link`, idle ends, the index-free update, the
  notations `e ∈ F^N _ n⟦σ ▷ c ; r⟧(Π, φ, tk)` and `v ∈ FV^N _ n⟦σ⟧(Π, φ)`
  through `sfix`, and the unfolding equations.
- S6.2. The clauses and the facts at counter 0, downward closure,
  `FuelE_mono` (refill, counters, frame, tickets, reserve) and
  `FuelE_rename` (v2/fuel/FuelMono.v).
- S6.3. `Vfuel_rename`, `FuelE_val`, `FuelE_beta`, `Vfuel_recount` along
  `tcap`, `Vfuel_age` along `tage`, values from parts, `Vfuel_pinst`,
  `FuelE_res_mono`, `FuelE_thread` (v2/fuel/FuelValues.v).
- S6.4. `FuelE_bind` with idle ends, `link_tickets_fall`
  (v2/fuel/FuelBind.v).
- S6.5. `Vfuel_teq`, `Vfuel_sub`, `FuelE_sub` (v2/fuel/FuelSub.v).
- S6.6. Notation test v2/test/FuelNotations.v, README section, CheckAll
  lists 105 results, all closed. No `Admitted` and no axiom. S6 done.
- S7.0. `seq_sound`, `meets_mono` and `meets_tid` (v2/cost/Transformers.v).
- S7.1. Stop. `fsem_of_cost` (old `ctyped_fsem`) fails for a thread that
  P-Term types at every refill N. The thread is
  fw o = let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w, with
  o : ?(∗ ⊸ ∗)^2.end. Its transformer is met at reserve 0 by every
  ticket count (`fw_ptyped`, `fw_tix_met`). F-Recv quantifies over every
  incoming value of `Vfuel`. The closure
  `dead_thunk o` = λ_. let ∗ = Ω in close o holds nothing and is in
  `Vfuel` at every level and refill, because its body only takes β
  steps (`Vfuel_dead`). After fw receives it and closes o, the spawn
  label moves {o}, and F-Spawn asks {o} ⊆ dom φ, which fails. So fw is
  not in `FuelT` at level 5 for any counters and tickets, and not in
  `fsem N` (`fw_not_fsem`). The same closure breaks the compatibility
  lemma of E-Send over groundings in `Vfuel` (`fuel_send_gap`). The pair
  ⟨dead_thunk q, d⟩ is in `Vfuel` at the payload type of d at every
  level, and its send is not in `FuelE` at level 1. Every repair needs
  the author, because each reads syntax in the fuel layer. (a) Q14 for
  `Vfuel`, so a closure asks dom Π = the ends it mentions and a box
  mentions no end. Every value of `Vfuel` is then exact, F-Recv and the
  arrow quantify only over exact values, and the compatibility lemmas of
  E-Abs, E-Box and E-SpawnLam need the typing lemma that the ends of a
  grounded term are those of Θ and of the grounding, as the old
  `cfacts` gave. The S6 lemmas on `Vfuel` keep v and Π or rename both,
  so they adapt with small changes. (b) F-Recv and the arrow read a
  transfer set at every incoming value, which amounts to (a). (c)
  F-Send and F-Spawn split Π by an existential with no M, which loses
  the index-free ownership that the soup of S8 pairs with O-Send and
  O-Spawn of the relation. Recommended (a), the clause Q14 already
  added to V. Not done. `csem`, the compatibility lemmas and
  `cost_fundamental`, which all depend on the choice. CheckAll lists
  108 results, all closed. No `Admitted` and no axiom.

