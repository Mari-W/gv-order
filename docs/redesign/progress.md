# Rewrite progress

The rewrite of docs/redesign/proposal.md lives in v2/ (logical name `GV`).
The old development in theories/ stays untouched.

## Stages

| Stage | Content | Status |
|---|---|---|
| S1 | language | done |
| S2 | points, worlds, types | done |
| S3 | generic relation | done |
| S4 | generic compatibility | in progress: (fuse) in P, Internalize as a projection (S4.19), P-Connect, P-Join, P-Term open |
| S5 | static fundamental theorems | term part done (S5.7): `fundamental`, `fundamental_typed`, `live_fundamental`, `live_fundamental_typed`; process theorems wait on S4 (targets in S5.5) |
| S6 | fuel | done |
| S7 | cost judgment | done |
| S8 | soup and adequacy | done (S8.34): `lfsoup_step`, `soup_no_tau_divergence`, `lf_adequacy`, `lf_thread_progress`, `idle_dual` |
| S9 | lock-free composition and soundness | in progress (S9.5): soup side done, `soup_connect`, `soup_term`, `lf_soup_connect`, `lf_soup_term_typed`, `lf_soundness_source`; process conjunct waits on S4 (targets in S9.5) |
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
  it, so no rule matches the redex shape. Done in S4.0.
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
- S4, static futures. `Θ ; Δ ⊨^F _ W t : T` takes the static future F
  of S2 and reads it through `sf_den ρ B F`: the future variable stands
  for an arbitrary set ρ φ and the ⊥ flag for an arbitrary set B, both
  universally quantified. The proposal's `pbot` (W8) is not used. A
  point that no world orders below anything does not survive the
  Kripke quantifier of E, whose later worlds need not be well formed.
  A term typed under the ⊥ flag performs no session action (every
  action asks `ub_below_s`, which asks the flag off), so it is ready
  under every future, and the universal reading is the one S5 can
  establish. The judgment at a set of points is `sem_typed_at`, the
  form the old semantic rules used. A body under a future hypothesis
  u ≺ φ (E-Abs, E-Box) is stated in that form over every future above
  u. With Γ = ∅, as in `fundamental` of A.3, both readings agree.
- S4, groundings. `Grel κ n W Θ Δ γ` splits Θ among the variables of Δ,
  one value of V per entry, as the old `grounding` did. It has no
  notation, because Appendix A gives none.
- S4, bind. `Erel_bind` asks no strictness of W and no bound on the
  heads of the frame. The future of the hole holds the heads of the
  frame's environment itself (`F ∪ senv_heads Θ2`), which S5 reaches
  from the static heads of E-App and its siblings. The ends a step of
  the hole acts on are held by the hole (`Erel_sends`), because every
  obligation reads the subject's entry, so a frame's ends are never
  touched and the old `Lsubjs_free` goes.
- S4, blindness. V, E and P agree at T and T' whenever
  `teq (ty_df T) (ty_df T')`, more than ty_df T = ty_df T'. The
  operator redexes need it, because V at S@x holds the end at an S'
  with S' ≈ S up to annotations only, and the obligations read the
  head of S' (`seqv_unfold_snd` and its siblings).

- S4, Q14. V at a λ asks `dom Θ = fends e` and V at a box `fends e = ∅`
  (decision Q14), as conjuncts of `Varr` and of the box clause of
  `Vbody`. The thunk of O-Spawn reads `Varr` too, so it asks the same,
  which O-Spawn's `dom Θ_M = M` already gave. The clause at a box is
  implied by the clause at its thunk, and is kept because Q14 states it.
- S4, `send_gap` is gone. Its positive form is `Erel_send`: a send of a
  pair in V at the payload and session types is in E, because the
  payload's environment is exactly its ends (`Vrel_exact`).
- S4, duality. O-Link compares the two ends by `sdual` up to erasure,
  and V gives each end's type only up to ≈. The link redex needs ≈ to be
  a congruence for `dual`. v2 had no such lemma, so types/Duality.v
  ports the flip algebra, `dual_unfoldS` and `sequiv_dual` from
  theories/types/Types.v and SessionEquiv.v.
- S4, the operator rules are stated at the set form `sem_typed_at`, with
  the facts of the typing rule read in W (`gen_e_*`, instances
  `sem_e_*`, `live_e_*`). The static facts Γ ⊢ x ≺ y and the static
  future reach this form only after S5 instantiates the hypotheses of Γ.
  E-New reads its constraint at the laws of the world of the judgment,
  so the redex is stated for every subset of the laws of a later world
  (`Erel_new_sub`).
- S4, Q16 environments. The renamed environment is `kren h Θ`, the
  map of the paper's `kmap h Θ`. stdpp's `kmap` asks h injective on all
  ends, and Q16 asks it only on the ends of Θ. `kren` agrees with `kmap`
  for an injective h (`kren_kmap`). Injectivity on the held ends is the
  fuel layer's `kinj h Θ`.
- S4, Q16 for terms. `Vrel_rename` and `Erel_rename` ask no duality
  condition of h. A term's obligations never compare an end with its
  partner, and the fresh names at a creation and at an incoming value
  keep the polarity by construction (`fresh_pull`). The condition is
  needed only for P, where the restricted channels and the partners of
  Q-Send and Q-Recv enter.
- S4, strict worlds (decision 4c077dc, after S4.15). The Kripke
  quantifier of `Pbody` ranges over strict worlds, ∀ W1, W ⊑ W1 →
  strict W1 → … . V and E keep theirs. `adequacy` and `live_adequacy`
  ask `strict W`, because P at a non-strict world is vacuous.
- S4, fusion (decision 4200d3d, after S4.18). The clause (fuse) of
  `Pbody` replaces (rename): every unfolding holds for
  `sdrop D (kren h Σ)` and `pfuse h D p` = (set_map (gch h) p.1 ∪ D,
  emapE h p.2) whenever `fuse_ok h D Σ p`: h commutes with duality, is
  injective on the held ends, makes two held ends partners only if they
  are or if their channel lies in D, D is apart from the renamed
  restricted channels, and the two ends of every channel of D are a dual
  pair at dual points of `kren h Σ` (`dpairs`). `pren_ok` asks no new
  partner pair at all. Cost tables carry `c_give_take : c_give ≤ c_take`.
- S4, Q16 for P (decision after S4.12). The clause (rename) is a
  quantifier of `Pbody`, inside the fixpoint. Every unfolding of P holds
  for `kren h Σ` and `pmap h p` for every h with `pren_ok h Σ p`: h
  commutes with duality and is injective on the held ends, the ends of Σ
  and both ends of every restricted channel. `pmap` renames the
  restricted channels by `gch h`. E carries no such quantifier. Its
  closure is the theorem `Erel_rename`, so the quantifier would be
  redundant there, and adding it would make every E lemma re-prove it.
  The decision text on redesign says the same ("V and E have the lemma
  as a theorem").

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
  definitions of S6. See S7.1. Repaired by decision Q15. The
  counterexample file is now v2/cost/Forwarder.v, which keeps the
  typing of the forwarder and checks that Q15 rejects `dead_thunk`
  (`dead_thunk_rejected`). `fuel_send_gap`, `fw_not_fsem` and
  `fw_counterexample` are deleted, because Q15 makes them false.
- S7, Q15. The closure clause of `Vty` asks `fends e = dom Π` and the
  box clause `fends e = ∅`, each as the second conjunct. The S6 lemmas
  change only in their destruct patterns, except `Vty_rename`, which
  shows the clause for the renamed body by `fends_emap` and `renk_dom`.
  `Vfuel_exact` states that every value of `Vfuel` is exact.
- S7, the facts of a derivation. `typed_tfacts` (v2/cost/Exact.v) gives
  `fends e = dom Θ`, an entry of Δ for every free variable, and an
  occurrence of every entry that is not unlimited. Weakening drops only
  unlimited entries, and a value at an unlimited type is a box, which
  holds no end. So a grounding of exact values gives the ends of the
  instance by `fends_subst_eq`.
- S7, refills (S7.6). FuelE, the closure and box clauses of `Vty`,
  `FuelE_mono` and `Vfuel_mono` quantify over refills in the order
  `rle`, finite refills by ≤ and ∞ above ∞ only, as the coordinator
  decided after S7.5. `FuelE_mono` changes its premise from `fle N N'`
  to `rle N N'`, and test/FuelNotations.expected changes with it.
- S7, the semantic judgment. `csem` has no hypothesis context Γ, no world
  and no future, because FuelE reads none of them. Its notation is
  `Θ ; Δ ⊨^N e : T^a ▷ c ; ϑ`, the merged form of A.2's
  `Θ ; Γ ⊨^N e : σ ▷ c ; t`, where Γ named the term context. Θ enters
  through a renaming g injective on its ends, with the session type of
  Θ exactly and a counter at or above its credit (`thfuel`). The frame
  of FuelE is the cost c.
- S7, the forwarder. `fw_fsem` gets the `fsem` of the S7.1 thread from
  `fsem_of_cost`. The paper counterexample of S7.5 is not in Rocq.
- S7, fsem_of_cost. The statement asks credits at most N on the ends of
  Θ and a ticket count that meets ϑ at reserve 0. P-Term gives credit N
  to every end. The session types of `fsem` are those of Θ (`te_sty`).

- S5, E-SpawnLam (stop). The semantic rule E-SpawnLam is false for the
  relation as defined, at every cost table. O-Spawn reads the thunk in V
  at an arrow 1 ⊸^u_l 1 for some u and l (`o_spawn`), and V at an arrow
  asks l ≼ heads Θ_M, a lower point of the heads of the ends the thunk
  takes along. D-SpawnLam (and E-SpawnLam of the merged judgment, Q8)
  asks no lower bound of a spawned λ. Counterexample in Rocq
  (v2/compat/SpawnGap.v). W has the constants 1, 2 and the one fact
  1 ≺ (2)‾ (`strict_gap`). The thread holds a⁺ : end@1 and b⁺ : end@2 and
  runs spawn (λ_. let ∗ = _ in let ∗ = close a⁺ in close b⁺), typed by
  D-SpawnLam (`gap_typed`). The heads (1)‾ and (2)‾ have no common lower
  point in W (`gap_no_lower`), so the spawn is in E at no positive level
  (`gap_not_E`), and `fundamental` of A.3 fails for it (`spawn_gap`,
  `spawn_gap_live`). The old development had no T-SpawnLam, only spawn
  of a value typed by T-Abs, which checks the lower bound. Repairs, each
  needing the author. (a) O-Spawn reads the thunk without the lower
  bound, Varr minus `lb_le`. The lower bound orders the heads of a
  closure against the ends of the term that holds it, and a spawned
  thunk leaves the parent, so the parent's readiness never reads it.
  `Varr_spawn_iff` changes, `Erel_spawn` keeps its text. (b) E-SpawnLam
  asks the lower-bound premise of E-Abs, which rejects a spawned thread
  that captures ends at unrelated points and may break `rg_typed` and
  `rg_ctyped`. Recommended (a). Until then the term theorems carry the
  semantic rule as a premise, `spawn_lam_rule κ_DF` and
  `spawn_lam_later κ_L` (v2/static/Fundamental.v, LiveRules.v), and are
  named `fundamental_of_spawn_lam` and `live_fundamental_of_spawn_lam`.
  The names `fundamental` and `live_fundamental` of A.3 wait for the
  repair, which then only has to prove the premise. Resolved in S5.7,
  after the decisions on O-Spawn (deviation "S5, O-Spawn without the
  lower point").
- S5, futures upwards. A value of a grounding holds its ends at or above
  the static heads of its type (`Vrel_heads`), while the bind lemma puts
  the heads of the frame's environment itself into the hole's future. E
  is closed upwards in its future (`Erel_cover`): a point at or above a
  point of F asks less of a blocked end. A new fact about E, in
  v2/compat/EFacts.v, proved like `Erel_weaken`.
- S5, D-Conv. Subtyping of erasures is not ≈ (an existential drops
  facts, an arrow is contravariant in its argument), so blindness alone
  does not give D-Conv. V is monotone along `tsub` (`Vrel_tsub`), and E
  reads its type only through V. `Erel_teq_1` asks the inclusion in every
  world, which E-Pack cannot give, because the facts of its constraint
  hold above W only. `Erel_ty_mono` (EFacts.v) asks it above W.
- S5, the hypotheses of Γ. The induction is on DF derivations. Γ is read
  through `hsat W1 σ ρ Γ`: every fact of an instantiated box constraint
  holds in W1, and every future variable φ stands for a set ρ φ above
  σ(u) when Γ has u ≺ φ. D-Box and D-Open close the m point variables of
  the box or the existential with the instance xs of the relation,
  `pclose xs m σ`. The merged judgment of Q11 enters by `typed_dftyped`,
  so `fundamental_typed` concludes at `tenv_df Θ`,
  `lenv_df Δ`, `ty_df T`. Δ and T could be read at their own annotations
  by blindness. Θ could not, because E is not shown blind in its
  environment.
- S5, D-Box. V at a box quantifies over every hereditarily contractive
  session instance, D-Box over the instances of N = ∞ only. The proof
  takes the erased instance `sty_df <$> ss` and moves back by blindness
  (`ty_df_sinst_map`). E-Box at κ_DF uses the positive cost of β
  (`gen_e_box`). The box rule with marks (`later_box`) needs no cost of
  β and holds at every table.
- S5, the guard. Port of theories/liveness/GuardRules.v as rules only
  (v2/static/Guard.v), with two simplifications. Marks propagate into λ
  bodies, where the old guard asked that a λ capture no marked variable
  (`nolater`). A body under a λ runs at a level at or below the level of
  the λ value, where a marked value is still in V below the level. The
  forceable marks under the λs of a box body and the rule (force f) e2
  for an acting e2 are gone. Their semantic proof needs the box body to
  be a λ, which V does not record, and no example of Appendix B needs
  them. The guard reads no syntax of the relation: `guarded t` is a
  premise of the theorem, beside the typing derivation.
- S5, marks in the relation. The judgment with marks `sem_later` reads a
  grounding `GrelL` that holds a marked variable as an unlimited value
  that mentions no end and is in V at every level below the current
  one. It is a definition over V and E, not a clause of either. At no
  marks it is `sem_typed_at` (`sem_later_noL`). The frame of an acting
  hole meets the value below the level (`Erel_bind_acts`, a new fact
  about E in v2/compat/BindActs.v), which asks every give and take to
  cost one or more, true of κ_L.
- S5, duplication. v2/compat/LiveRules.v repeats the rules of
  compat/TermRules.v and compat/Rules.v with marks. TermRules is the
  content of LiveRules at no marks, kept so that the DF theorem uses the
  S4 judgment `sem_typed_at` directly. A cleanup can derive the one from
  the other.

- S5, O-Spawn without the lower point and at the empty future
  (decisions after S5.5 and S5.6, on redesign under the O-Spawn entry).
  O-Spawn reads the thunk as `Vthunk` (v2/relation/Relation.v), a λ that
  holds exactly the ends it mentions and whose body is read at the
  empty future, with no lower and no upper point and no type arguments.
  `o_spawn` quantifies over ΘM and Θr only. `Varr` and V at an arrow are
  unchanged. `Varr_thunk` turns an arrow 1 ⊸^ub_lb 1 into a thunk, and
  `Vrel_thunk` (Closure.v) replaces `Varr_spawn_iff`, which no longer
  holds as an equivalence. `Vthunk_of_Vrel` (Redex.v) gives `Erel_spawn`
  its old text.
- S5, E blind in its environment (item 4 of the coordinator). Not done
  on redesign-s5: redesign-s4 has V, E and P along environments up to ≈
  (compat/Conv.v, S4.17). After the merge, `fundamental_typed` and
  `live_fundamental_typed` can conclude at Θ and Δ themselves through it.
- S4 merge needs (from S5). (1) `o_spawn` lost its upper and lower point:
  every destruct of the spawn case reads `(ΘM & Θr & A1 & …)` and every
  construction `exists ΘM, Θr`, and `Varr_mono` on the thunk becomes
  `Vthunk_mono`. On redesign-s4 this concerns compat/Conv.v:306 and
  compat/Rename.v:633 besides the files S5 changed (relation/Closure.v,
  compat/Blind.v, Bind.v, Swap.v, Redex.v). The thunk's body is read at
  the empty future, with no `ub_lt`, so the renaming and conversion
  proofs of the thunk lose their F and Hub arguments. (2) `Varr_spawn_iff`
  is gone, replaced by `Vrel_thunk`. (3) EFacts.v and BindActs.v unfold E
  by `Erel_S_ind` and `Erel_S_iff` and must be re-proved for the new
  definition of E, as Blind.v and Closure.v are. (4) P-Term must start a
  spawned thread at the empty future, which `fundamental` gives at
  F = (∅, None).
- S8, the protocol map. The soup chooses the protocol map Π of the fuel
  layer at each index next to the environment A of the relation, with
  the same ends, and does not read Π off A. O-New and F-New each pick
  the session type of a new channel by an existential of their own, so
  no soup can take the one from the other: after a creation E[live]
  holds at new_env c S x A for some S and FuelE at pnew c S′ Π for some
  S′, with no relation between S and S′. The soup pairs A up to
  annotations (`sdual`, as the relation does) and Π up to ≈ with
  annotations (S′ ≈ dual S), and adequacy reads idleness off Π only.
  P-Term can still start Π at `te_sty <$> Θ` (S7).
- S8, F-Link (fuel/Fuel.v). F-Link asks the two linked ends at dual
  protocols (`plink`), a clause on Π, no syntax. Without it the soup
  loses the pairing of Π at a link: after linking o1 and o2 the partners
  of o1 and o2 form one channel, and their protocols are dual only if
  those of o1 and o2 are. The relation's O-Link compares the two ends
  only up to annotations, and an annotation mismatch breaks the payload
  credit of a later message (the sender guarantees credit b, the
  receiver's FuelE quantifies over credit b′ > b). E-Link types the two
  ends at S and dual S exactly, so `link_redex` proves the clause; the
  S6 lemmas change only in their destruct patterns.
- S8, one clock. A soup step goes from index n + 1 to n, not n + 2 to n
  (F25). Each thread pays its own side of a synchronization at its own
  level: the sender κ(send) = 1, the receiver κ(recv) = 1, and FuelE
  loses one level at every step. The two clocks of the process relation
  P (a synchronization costs 2) do not reach the soup.
- S8, ownership. The index-free state is the configuration q, the
  ownership K (an end to its holder, its point and its counter, `hold`)
  and the tickets tk (`lfstate`, soup/State.v). Records live in
  soup/State.v because of the `;` clash of the typing notation (S3); the
  clauses of the soup are the generic record `soup_gen` there,
  instantiated in soup/Soup.v with E[live] and FuelE^N.
- S8, the refill of LF is finite, `N : nat`. The measure of adequacy
  reads counters as natural numbers, and at N = ∞ every counter is ∞.
- S8, the soup with an interface. `Soup` takes Σ (interface clause
  `sp_sig`, closure up to `dom Σ`), but `lfsoup_step` and adequacy are
  stated at Σ = ∅, for closed runs.
- S8, finite counters. The soup has the clause `sp_fin`: every counter in
  K is finite. It is index-free and preserved by the update (`kfin_*`).
  The measure of adequacy reads a counter as a natural number.
- S8, the process conjunct (Q12, F21). `soup_no_tau_divergence` holds
  (v2/soup/SoupTau.v), and adequacy reads the soup alone
  (`lf_adequacy_soup`). `lf_sem` keeps the live process conjunct of the
  proposal, because Q12 says the conjunct may go once the lemma exists,
  which is now the author's call. Dropping it changes only `lf_sem` and
  the statements of S9.
- S8, liftings. `lf_sem` fixes one lifting of p, lock freedom quantifies
  over runs from every lifting. `soup_relabel` moves a soup along a
  bijection of thread identifiers (v2/soup/Relabel.v), as the old
  `LFsoupAt_relabel` did.
- S8, the dependency. A pending thread depends on the owner in K of the
  partner of its end, never on a term that mentions the partner (as in
  the old adequacy). The criterion is `lf_run_criterion` unchanged, with
  `npend`, `admin_at` and `pend` of S1.
- S9, the exact cut. `soup_connect` takes the cut at Σ̄_C (`senv_dual`),
  the partners at exactly the dual session type, as `p_connect` types
  them, and not at `cut_dual` of compat/Connect.v (dual up to
  annotations). The soup pairs the protocols of a restricted channel up
  to ≈ with annotations (`sp_pdual`), and `sp_psig` puts an interface
  end into Π at the session type of its entry. A cut dual only up to
  annotations gives no such pairing, for the reason of "S8, F-Link".
  The clause is on environments. A semantic P-Connect with `cut_dual`
  composes with the soup only for cuts that are exact.
- S9, families. The proposal (§2.14) renames families apart at LF-Connect.
  The soup compares no points of two threads, so `soup_connect` needs
  no renaming and no disjointness of families. The world enters only
  through E[live], which is monotone in the world (`Erel_mono`,
  `wext_join_l`, `wext_join_r`). The refill is the larger of the two,
  by `FuelE_refill_mono`.
- S9, the soup half. `lf_soup W Σ p T` is the soup conjunct of `⊪`
  (`lf_sem_iff`). The composition lemmas are proved for it, and
  `lf_sem_term` and `lf_sem_connect` take the live process conjunct of
  the result as a premise until P-Term, P-Connect and P-Join of S4 are
  proved and the author decides on Q12 (deviation "S8, the process
  conjunct").
- S9, P-Term at a finite N. `lf_soup_term_typed` asks `meets ϑ 0 tk`
  for some tk, as `fsem_of_cost` does. `typed` at a finite N does not
  give it, because a transformer offset may be ∞. It also asks
  `guarded t` and `strict W` for `live_fundamental_typed`.
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

- S4.0. Decision Q13. The term former `ELet e1 e2` (let x = e1 in e2,
  binding 1 in e2) with the frame `FLet` and the head step `t_act_let`,
  `ELet v e --β--> e[v/x]`. The step carries the label β, so it costs
  κ(β) and the relation needs no new clause: O-Beta reads it. E-Let
  (`e_let`) and D-Let (`d_let`) type `ELet e1 e2` with the premises of
  the S2 rule, no lower point. `let_new` and `elet` of examples/Tools.v
  build the new former, so the examples keep their derivations.
  Safety (`act`, `act_offer_sig`, closedness), harmony (`HRedLet`),
  `act_emap`, the frame maps of ChannelSwap.v and TauThread.v, `relabel`
  and the notation test follow. Conservativity, renaming, weakening and
  point substitution needed no change beyond the rule's subject.
- S4.1. The bind lemma `Erel_bind` over every cost table
  (v2/compat/Bind.v) and blindness (v2/compat/Blind.v): `Vrel_teq`,
  `Erel_teq_ty`, `Prel_teq`, `Vrel_blind`, `Erel_blind`.
- S4.2. The semantic term judgment (v2/compat/SemTyped.v): `Grel`,
  `sem_typed_at`, `sf_den`, `sem_typed κ`, the notations `⊨` and `⊫`
  (test/CompatNotations.v), `Grel_split` for `lenv_split`, and the
  world, level and future lemmas.
- S4.3. Stop. O-Send asks `dom Θ_M = M` with M the ends the payload
  mentions (Q3), and after B5 and B6 no V clause relates the ends of a
  value to its environment (§2.7). So V holds values that no send can
  hand over. `send_gap` (v2/compat/SendGap.v) proves it in Rocq: the
  closure w' = λ_. let ∗ = Ω in close q⁺ mentions q⁺, owns nothing and
  is in `V^W _ n⟦∅ ⊢ ∗ ⊸ ∗⟧` at every n (its body only takes β steps),
  the pair ⟨w', d⁺⟩ is in V at the payload type of d⁺ at every n, and
  `send ⟨w', d⁺⟩` is not in E at level 1, because its label moves {q⁺}
  and the sender holds no q⁺. So the semantic E-Send rule is false over
  groundings in V. It is not an artefact of the rule's form. O-Recv,
  Q-Recv and the arrow quantify over every value of V, so the typable
  forwarder `let ⟨w, c⟩ = recv c in let ∗ = close c in close (send ⟨w, d⟩)`
  with c : ?(∗ ⊸ ∗).end, d : !(∗ ⊸ ∗).end, after receiving w' at Θin = ∅,
  reaches the same send at a positive level whenever n is large enough
  to pay for the receive, the close and the β steps before it (n ≥ 4 in
  κ_DF, n ≥ 3 in κ_L), so it is in neither E, and `fundamental` and `live_fundamental` of A.3 fail for it. The
  same holds for the closure λw. send ⟨w, d⟩ (E-Abs) and for a box that
  mentions an end in dead code (B.1 #32 argued it handled). The
  argument of §2.7 ("a closure that owns an end it does not mention
  cannot act on it, so the relation rejects it by itself") does not
  hold: V does not reject it, and every receiver must accept it.
  Repairs, each needing the author: (a) restore exactness in V,
  `dom Θ = fends v` at λ and box (B5, B6), a syntactic clause; (b) read
  a transfer set at every incoming value as well (O-Recv, Q-Recv and
  the arrow's argument, with E returning only exact values), which
  amounts to (a); (c) an existential split at O-Send and O-Spawn with
  no M, which loses the index-free ownership §2.7 wants for lock
  freedom. Not done: operator redexes, P-Term, Internalize, P-Connect,
  P-Join, renaming, `live ⊆ DF`. The composition lemmas do not depend
  on the repair as long as O-Send keeps an exact `Θ_M`, so they can
  start once the author decides. CheckAll lists 87 results, all
  closed. No `Admitted` and no axiom.
- S4.4. Decision Q14 in v2/relation/Relation.v, S3's closure and
  characteristic lemmas follow. types/Duality.v. v2/compat/Redex.v: the
  exact ends and the heads of values, the β redexes, the redex of every
  operator and of `new_ℓ`. v2/compat/Rules.v: the operator rules over
  every cost table and their DF and live instances.
- S4.5. live ⊆ DF (v2/compat/LiveDF.v). `live_sub_df : tshape T →
  ∅ ⊫_W p : T → ∅ ⊨_W p : T`, for a closed process at a first-order T
  (∗, S@x, ⊗, ⊕, ∃, no arrow and no box). V at such a T reads no E and
  is the same for both tables (`Vrel_shape`). A closed process takes τ
  steps only, each at least as costly in κ_DF as in κ_L except a link,
  which costs 0 in both and is read inside the level by induction on the
  size of the soup (`psize_link`). What this argument does not give.
  (1) A higher-order T or an open interface. V of κ_DF must then be read
  in a negative position (an arrow's argument, a received payload), and
  V of κ_DF is not included in V of κ_L: λ_. Ω is in V of κ_DF at
  ∗ ⊸ ∗ and not in V of κ_L. No counterexample to the inclusion itself
  is known; it needs an argument relating the two relations (a binary
  relation or parametricity), not an induction on levels. (2) An open
  interface also lets each level pick its own environment Θe of
  extruded ends in Q-Send, while the conclusion needs one environment at
  every level. Blindness of P in its environment up to ≈ would repair
  (2), not (1).
- S4.6. Renaming (v2/compat/Swap.v). V and E are invariant under a
  transposition of channel names, for every cost table (`Vrel_swap`,
  `Erel_swap`). P is not done: it needs the transposition on
  configurations with thread identifiers (only the erased `pstep_pswap`
  exists) and the transport of `send_split`, `recv_ok`, `recv_env` and
  `recv_back`.
- S4.7. Open: P-Term, Internalize, P-Connect with the external Q-Send
  and Q-Recv clauses, P-Join, and renaming of P. The plan: P-Join
  follows from P-Connect by R7 (`p_join_iff_connect`). P-Connect is
  induction on the level and, inside it, on the least fixpoints of the
  two components. Cross-cut communication is a Q-Send of one side
  against a Q-Recv of the other at cost κ(send) + κ(recv) ≥ 1. A link
  that involves a cut end renames the other component (renaming of P).
  Readiness of the composite is a chain of cut ends that strictly
  descends in W1 ⊔ W2 and so ends at an offered interface end by
  strictness. P-Term is P-Connect of the spawned threads. In size it
  matches theories/liveness/LiveConnect.v, LivePConnect.v, LivePTerm.v
  and composition/ReadyChain.v (about 3500 lines), and it is not
  started. CheckAll lists 125 results, all closed. No `Admitted` and no
  axiom.
- S7.2. Decision Q15 in v2/fuel/Fuel.v, the S6 lemmas adapted,
  `Vty_exact` and `Vfuel_exact` (v2/fuel/FuelMono.v).
- S7.3. v2/cost/FuelGap.v becomes v2/cost/Forwarder.v with
  `dead_thunk_rejected`, `fw_typed` and `fw_ptyped`.
- S7.4. `typed_tfacts`, `fends_subst_eq` and the renaming facts of
  free variables (v2/cost/Exact.v).
- S7.5. Stop. E-Force has no compatibility lemma under the decision
  "fuel is Kripke in the refill" together with the S2 deviation on
  session instances. FuelE^N and the box clause of `Vfuel` hold at every
  N′ ≥ N, and the order on ℕ ∪ {∞} puts ∞ above every finite N. A box in
  `Vfuel` at refill ∞ promises its body only at the instances
  `sinsts None ss`, the session types with the annotations of N = ∞
  (S2, session instances). A thread typed at a finite N forces a box at
  any hcontractive instance (E-Force with `sinsts N ss`). Fdef lets the
  refill of every step jump from N to ∞, so the thread must run at
  refill ∞, where a box it received or got from a grounding promises
  nothing at its finite instance. Counterexample on paper, not in Rocq.
  A thread typed at N = 2 receives a box !λx. let ⟨y, x′⟩ = recv x in
  e, at the instance s = ?(?S)^0.end of its session variable, forces it
  and runs the closure on an end at s. At refill ∞ the received box
  need only work at the instance ?(?S)^∞.end. There the received y
  carries credit ∞, every counter is ∞, and the body may act on x′
  while it holds y. At s the incoming y may arrive with counter 0, so
  the same action breaks F-Tick, and `fsem_of_cost` fails for the
  thread. Proposed repair, needing a decision. Order the refills by
  kind, N ≤ N′ within ℕ and ∞ only above ∞ (`rle`), in Fdef, in the
  closure and box clauses of `Vty`, and in `FuelE_mono` and
  `Vfuel_mono`. Composition takes the maximum of finite refills
  (Q4), and the DF instance N = ∞ stays its own, so S8 and S9 lose
  nothing. With `rle` the box at refill N″ has N″ = ∞ exactly when
  N = ∞, and E-Force gets its instance from `sinsts N ss`. The
  alternative, letting E-Box at N = ∞ type the body at every instance,
  undoes the S2 deviation. Not done. `csem`, the compatibility lemmas,
  `cost_fundamental` and `fsem_of_cost`. CheckAll lists 160 results,
  all closed. No `Admitted` and no axiom.
- S7.6. Refills ordered by kind (`rle`) in v2/fuel/, the S6 lemmas
  adapted.
- S7.7. `thfuel`, `gfuel`, `envf`, `csem` and their structural lemmas,
  `envf_exact` (v2/cost/CostSem.v).
- S7.8. `csem_bind0`, `csem_bind1`, `csem_bind2` (v2/cost/CostBind.v)
  and the redexes of the application and of every operator
  (v2/cost/CostRedex.v).
- S7.9 to S7.11. One lemma per typing rule, `cost_e_unit` to
  `cost_e_open`, `cost_e_let` on the primitive let of Q13, E-Box by
  induction on the level (v2/cost/CostRules.v).
- S7.12. `cost_fundamental`, `fsem_of_cost`, `fw_fsem`
  (v2/cost/CostFund.v), notation test v2/test/CostNotations.v, README
  section. CheckAll lists 173 results, all closed. No `Admitted` and no
  axiom. S7 done.
- S4.8. Renaming of P (v2/compat/PSwap.v). The transposition a ↔ b on
  configurations with thread identifiers (`qswap`) and on events
  (`evswap`). `istep_qswap`: a step of a configuration is the renamed
  step of the renamed configuration, every rule P-Act-* included, the
  link through `eswap_csub`. `erase_qswap` relates it to `pswap`. The
  external clauses move along it (`send_split_swap`, `recv_ok_swap`,
  `recv_env_swap`, `recv_back_swap`, `chans_of_swap`), and so does
  readiness (`ready_p_swap`). `Prel_swap`: P is invariant, for every
  cost table.
- S4.9. Not done: P-Term, Internalize, P-Connect, P-Join. Found while
  planning them: the transpositions of S4.6 and S4.8 are not the
  renaming P-Connect needs. A link P-Act-Link renames every thread by
  `csub o1 o2`, which sends ō1 to o2 and o1 to ō2, so a link of c⁺ with
  d⁺ turns the partner's c⁻ into d⁺ (S1 deviation "link"). When o1 is a
  cut end, the other component is renamed by a map that flips the
  polarity of a channel, and P-Connect needs P of that renamed
  component. Two obstacles block a renaming lemma for such maps. (1) A
  map that flips the polarity of c sends the new pair ⟨c⁺, c⁻⟩ of a
  creation to ⟨c'⁻, c'⁺⟩, so it commutes with T-Act-New only after the
  fresh name is chosen anew per step. The renaming lemma has to range
  over all bijections of ends that commute with the partner map (not
  only transpositions), with a fresh-name argument at every creation.
  At the process level the global freshness of P-Act-New gives the
  fresh name. At the term level O-New asks freshness only for Θ, and a
  term may mention a fresh name in code it never runs. (2) The relation
  asks no correspondence between the ends a term mentions and the ends
  it holds, except at values (Q14). The other component may mention, in
  code it never runs, an end the link substitution then identifies with
  one it holds. Such a renaming is not injective on the term, and a
  proof needs either an invariant that every thread mentions only ends
  it holds or restricts (typed processes keep it, the relation does
  not: after a send a term may still mention a sent end), or a
  simulation argument for code a term never runs. Before this proof
  goes further, the author should decide which of these to use: a
  syntactic premise on P-Connect (each component mentions only its own
  channels, as typing gives), or a renaming lemma over dual-commuting
  bijections with fresh names chosen per creation. The rest of the plan
  of S4.7 stands. CheckAll lists 162 results, all closed.
- S4.10. Decision Q16 (21989f4 on redesign), worked out before
  proving. Q16 asks invariance under every end bijection that commutes
  with duality. That lemma is plausible, but it is not the renaming
  P-Connect needs, and it is not provable by moving each obligation
  along one bijection. The step that P-Connect needs, and its proof, is
  the following.
  (1) The link renaming of the other component is no bijection on the
  ends it mentions. `csub o1 o2` sends o1‾ and o2 to o2 (`csub_fuses`,
  v2/compat/PSwap.v). The holder of o1‾ may mention o2 in code it never
  runs, so after the link two ends of its term are one. No bijection
  restricted to the mentioned ends gives this term.
  (2) Re-choosing the fresh name does not save the bijection form. Let
  g flip the channel c (g c⁺ = c⁻). The renamed term may create c while
  it mentions c⁺ in code it never runs (O-New asks freshness only for
  Θ). The renamed continuation then holds the new c⁺ at the place of the
  old mention. The original continuation, for any name c'' it creates,
  has the mention g⁻¹(c⁺) apart from the new ends, so the renamed
  continuation is the image of an original continuation only under a
  map that sends two ends to c⁺.
  (3) The sound form is an argument about held ends. Let h be a map of
  ends that commutes with duality (h ō = (h o)‾) and is injective on the
  ends of Θ, arbitrary elsewhere. Claim: e ∈ E⟦Θ ⊢ T⟧^F implies
  emap h e ∈ E⟦kmap h Θ ⊢ T⟧^F, and the same for V and P (for P,
  injective on the ends of Σ). Why the mentions that h merges do not
  matter: emap h keeps the shape of a term, so every step of emap h e
  sits at the place of a step of e, and every action of e is on a held
  end, because each obligation reads the subject's entry in Θ. A
  mention that e does not hold is never acted on, sent or spawned on any
  path, and E quantifies over every received value and every created
  name, so this holds for every future. The renamed term therefore acts
  only on images of held ends, where h is injective. Steps with a free
  choice move by extending h: a creation of c by emap h e is matched by
  e creating a name c'' fresh for Θ and for the ends e mentions, with h
  extended by c''± ↦ c± (polarity kept). A received value w with Θin is
  matched by w' = emap k w with k a right inverse of the extended h that
  keeps duality and avoids the ends of Θ (k sends the partner of a held
  end to that held end's partner). The arrow's argument is handled in
  the same way. A P-Act-Link of o1, o2 is matched by the link of
  the preimages, with h replaced by h2 ∘ csub = csub' ∘ h, which is
  defined on the image of csub because h is injective on the two held
  linked channels. The bijections of Q16 are a special case, so (3) is
  stronger than Q16 and gives the renaming of the other component at a
  link directly: csub restricted to the holder's held ends is injective.
  It also needs Internalize, because after a link the other component
  may hold both ends of a channel.
  (4) Nothing found contradicts Q16 or (3). (3) is not proved yet. It
  replaces the involution argument of compat/Swap.v and PSwap.v by a
  forward simulation that extends h at every choice. By size it is the
  largest single lemma of S4. I stopped here so the author can confirm
  that (3) is acceptable as the form of Q16: maps that commute with
  duality and are injective on held ends, not bijections of all ends.
- S4.11. Decision Q16 for V and E, in the held-ends form of S4.10
  (v2/compat/Rename.v). `Vrel_rename` and `Erel_rename`: for every map
  h of ends injective on the ends of Θ and every cost table,
  v ∈ V⟦Θ ⊢ T⟧ gives emap h v ∈ V⟦kren h Θ ⊢ T⟧, and the same for E at
  every future. The proof is the forward simulation of S4.10 (3). A
  step of emap h e comes from the redex of e (`act_emap`), and thread
  steps are deterministic for a fixed label (`tstep_det`), so the two
  continuations agree up to an extension of h (`tstep_emap_back`). A
  creation and an incoming value (O-Recv, the argument of a λ) pick
  fresh channels and extend h to send them back (`fresh_pull`,
  `pull_value`). Readiness moves along h because every session step of
  a term in E is on a held end (`Erel_sends`, `ready_rename`). The
  transposition lemmas `Vrel_swap` and `Erel_swap` are now instances
  (`Vrel_swap_rename`), and compat/Swap.v keeps only the transposition
  on environments. No `Admitted` and no axiom.
- S4.12. Stop at Q16 for P. The renaming of P is not proved, and the
  route of S4.10 does not reach it. Nothing found makes the lemma
  false. What breaks is the proof by a forward simulation, which needs
  the renamed configuration to be the image of the original under one
  map of ends after every step.
  (1) For P the held ends are the ends of Σ and both ends of every
  restricted channel. h has to be injective on all of them, because a
  τ step meets two threads by the names of their ends. It also has to
  create no new pair of partners in Σ (o, p in Σ with h p = (h o)‾ only
  when p = o‾). Otherwise the renamed process has internal steps whose
  original is a Q-Send followed by a Q-Recv, which is Internalize, not
  renaming. The link of P-Connect between two cut ends creates such a
  pair (p2 holds o1‾ and o2‾, and csub sends o1‾ to o2), so that case
  needs Internalize after the renaming, as S4.10 said.
  (2) P-Act-Link fixes the link partner o2 from the term, and o2 need
  not be held. The original links a restricted end with an end it
  neither holds nor restricts, and h may send that end onto the
  restricted channel. Example, in v2 terms. C = {c}, Σ = ∅, threads
  ∗, link ⟨c⁺, z⁺⟩ and (λx. ∗) ⟨c⁻, z⁺⟩, with h sending z± to c± and
  fixing every other end. h commutes with duality and is injective on
  c⁺ and c⁻. The original link turns the third thread into
  (λx. ∗) ⟨z⁺, z⁺⟩. The renamed link is the self link of c⁺, which
  flips c, and turns it into (λx. ∗) ⟨c⁺, c⁻⟩. Both processes are in P
  at every level (argued, not in Rocq), but no map of ends takes the
  first term to the second. The term-level
  proof never meets this, because O-Link reads both ends from Θ.
  (3) A condition on h alone repairs (2) only for one step. If h maps
  no end outside the restricted channels onto a restricted channel
  (reflection), the h2 of S4.10 exists at every link. Reflection is not
  preserved by Q-Recv. The renamed process may receive both ends of a
  channel d that h already uses as the image of an end the original
  mentions in dead code, and after the receive d is restricted while
  that end is not.
  Two ways on, each needing the author. (a) Make E and P closed under
  held-ends renamings by definition, as FuelE is (F15, `Fdef`
  quantifies over every g with `kinj`). The renaming lemma is then a
  projection, and P-Connect has to establish the clause for the
  composite, by the induction hypothesis on renamed components. (b) A
  simulation up to dead code, a relation between terms that agree up to
  h on every end the term will act on. It is semantic and I see no
  finite form of it. I recommend (a). Not started: P-Term, Internalize,
  P-Connect, P-Join, all of which wait on this. CheckAll lists 169
  results, all closed. No `Admitted` and no axiom.
- S4.13. The clause (rename) in `Pbody` (v2/relation/Relation.v),
  with `gch`, `dcomm`, `kren`, `pmap`, `pheld`, `pren_ok` moved there
  from compat/Rename.v. The clauses at one renaming are `Pclauses`, and
  `Pbody_id` and `Prel_S_clauses` read them at the identity. Closure,
  adequacy, blindness and `live_sub_df` follow with small changes.
  `Prel_rename` is the projection: h with `pren_ok h Σ p` gives
  pmap h p ∈ P⟦kren h Σ ⊢ T⟧, because a renaming of a renaming is the
  composite (`pmap_pmap`, `pren_ok_compose`). `Prel_swap` is now an
  instance of it, and the induction of compat/PSwap.v is gone. Adequacy
  is unchanged, because it reads the clauses at the identity. CheckAll
  lists 170 results, all closed.
- S4.14. Checked against P-Connect, not proved. The clause (rename)
  breaks no decided point and not adequacy (adequacy reads the identity).
  `pren_ok_csub` (v2/compat/Rename.v): when one component links o1 with
  o2 and the other holds o1‾ but neither o1 nor o2 (as an interface end
  or a restricted end), `csub o1 o2` commutes with duality and is
  injective on the held ends of the other, also when it holds o2‾. So
  the link case of P-Connect gets P of the renamed component from
  `Prel_rename`. The plan for the rest, for a successor.
  (1) Internalize. If Σ holds o at (S, x) and o‾ at (S', x‾) with
  `sdual S S'` and ech o ∉ p.1, then p ∈ P⟦Σ ⊢ T⟧ gives
  (p.1 ∪ {ech o}, p.2) ∈ P⟦delete o (delete o‾ Σ) ⊢ T⟧. An internal
  message on the new channel costs `c_give κ + c_take κ` (`ev_cost` of
  `EvMsg`), and the original pays the same by Q-Send on o and then
  Q-Recv on o‾ with Θ2 the ends that leave (Σv ∪ Θe). Close and choice
  likewise, a link on it by Q-Link. Readiness: an end of the channel
  waits on its partner, which lies below by `sdual` at dual points.
  The clause (rename) of the result comes from the clause of p at the
  same h, because a held-ends renaming of the result is one of p.
  (2) P-Connect, two worlds. p1 ∈ P^{W1}⟦Σ1 ∪ ΣC ⊢ T⟧,
  p2 ∈ P^{W2}⟦Σ2 ∪ Σ̄C ⊢ 1⟧, ΣC and Σ̄C dual entry by entry, all domains
  and restricted sets disjoint, strict (W1 ⊔ W2) give
  (p1.1 ∪ p2.1 ∪ chans ΣC, p1.2 ⊎ p2.2) ∈ P^{W1 ⊔ W2}⟦Σ1 ∪ Σ2 ⊢ T⟧.
  Induction on the level, inside it on both least fixpoints. Steps: one
  side alone (its Q-clauses for its interface, τ otherwise), a message
  across the cut (Q-Send of one, Q-Recv of the other, cost
  κ(send) + κ(recv) ≥ 1, so the level drops), a link with a cut end
  (q_link of the linking side, `Prel_rename` with `pren_ok_csub` on the
  other, then Internalize when the other held o2‾). Readiness of the
  composite: a stuck cut end points to its partner's offer below it,
  a chain that strictly descends in W1 ⊔ W2 and ends at an interface
  offer by strictness. The clause (rename) for the composite: a
  held-ends renaming h of the composite restricts to one of each
  component (cut channels are restricted, so both ends are held), and
  pmap h of the composite is the composite of pmap h p1 and pmap h p2,
  so the case is the same statement for the renamed components
  (`Prel_rename`), which the induction covers if the lemma is stated
  for all p1 and p2.
  (3) P-Join by `p_join_iff_connect`. (4) P-Term: a thread in
  E⟦Θ_B ∪ Σ ⊢ T⟧ with Θ_B the paired dual ends of C0 gives
  (C0, {t}) ∈ P, by P-Connect of the parent and each spawned thread,
  with `Erel_rename` for its clause (rename).
  Not started in Rocq. In size this is theories/liveness/LiveInternalize.v,
  LiveConnect.v, LivePConnect.v, LivePTerm.v and composition/ReadyChain.v,
  about 4700 lines.
- S4.15. Stop. Internalize and P-Connect are false for the relation
  as defined, for every cost table. P quantifies over every W1 ⊒ W
  (`Pbody`), and ⊑ does not keep strictness. Q-Recv reads the incoming
  value in V at W1, so a later world W1 with a cycle can deliver ends at
  points that only a cyclic order accepts. A component is ready in such
  a W1 by a chain through the cycle. The composite after the message is
  deadlocked. Counterexample on paper, not in Rocq.
  W has constant points x, z, r with the facts z ≺ x and r ≺ x‾, and is
  strict. p1 holds r⁺ : ?(∃α [x ≺ α‾]. end@α).end at r and the cut end
  a⁺ : ?1.end at x, and runs
  let ⟨y, r'⟩ = recv r⁺ in let ∗ = close r' in
  let ⟨u, a'⟩ = recv a⁺ in let ∗ = close a' in close y.
  p2 holds a⁻ : !1.end at x‾ and d⁺ : end at z, and runs
  let ∗ = close d⁺ in close (send ⟨∗, a⁻⟩).
  Both are in P at W at every level (argued). p1 waits on r⁺ below
  x‾ (r ≺ x‾), then on a⁺ below the partner point of the received end,
  which the constraint gives in every later world. p2 waits on d⁺ below
  x (z ≺ x). The cut is dual at dual points and W ⊔ W = W is strict, so
  P-Connect gives the composite (a, p1 | p2) in P at W with interface
  r⁺, d⁺. Take W' = W plus the fact x ≺ z, and receive Chan d⁻ on r⁺
  with α := z‾. The value is in V at W' (x ≺ (z‾)‾ = z holds in W'),
  and `recv_ok` holds, because the composite holds d⁺ at z. The
  composite then restricts d, closes r' and is stuck: p1 waits on a⁺,
  p2 on d⁺, and p1 closes d⁻ only after a. Its interface is empty and it
  is not terminated, so it is not ready, and it is not in P at level 4
  or above. The same example refutes Internalize: p1 | p2 with
  interface r⁺, a⁺, a⁻, d⁺ is in P (after the message it is ready in W'
  because W' ⊢ x ≺ z ≺ x), and internalizing a gives the composite.
  Cause. The old live relation, which decision Q9 (a) names ("as the
  live relation does"), quantified over `wext_r`, whose extensions are
  strict (theories/relation/Worlds.v, `wext`). S3 dropped strictness
  from ⊑. Proposed repair: the Kripke quantifier of `Pbody` ranges over
  strict worlds, ∀ W1, W ⊑ W1 → strict W1 → ∀ h, pren_ok h Σ p → …
  V and E keep theirs. Then every chain of P-Connect and Internalize
  descends in a strict world and stops. Tried in a copy of v2: about
  45 changed lines in relation/Relation.v (`Pbody`, its maps,
  `Pbody_id`, `Prel_S_clauses`), relation/Closure.v (`Prel_down`,
  `Prel_S_step`), relation/Adequacy.v, compat/Blind.v, compat/LiveDF.v,
  compat/Rename.v. It builds, CheckAll keeps 190 of 190 closed, and
  `adequacy` and `live_adequacy` gain the premise `strict W`
  (test/RelationNotations.expected changes). P at a non-strict world
  becomes vacuous, so adequacy needs it. `soundness` of A.3 already
  assumes strict W. Not applied, because it changes the relation and A.3.
  Not started: Internalize, P-Connect, P-Join, P-Term. CheckAll lists
  190 results, all closed. No `Admitted` and no axiom.
- S4.16. The repair of S4.15 (decision 4c077dc). `Pbody` asks
  `strict W1`, and `Pbody_id`, `Prel_S_clauses` and `Prel_S_step` with
  it. `adequacy`, `live_adequacy` and the lemmas behind them ask
  `strict W`. relation/Adequacy.v exports types/Worlds.v again after
  lockfree/TauThread.v, so that `strict` is the world's and not stdpp's.
  test/RelationNotations.expected follows. CheckAll lists 190 results,
  all closed.
- S4.17. compat/Conv.v. Environments up to ≈ (`senv_eqv`: the same
  ends at the same points, session types ≈ after erasure). V, E and P
  transport along them for every cost table (`Vrel_conv`, `Erel_conv`,
  `Prel_conv`). Composition needs it at a link of a cut end o1 with an
  interface end o2: the holder of o1‾ then holds o2 at the type of o1‾,
  and the interface keeps o2 at its own type, which Q-Link gives only
  up to ≈. CheckAll lists 193 results, all closed.
- S4.18. Stop. The clause (rename) of `Pbody` (S4.13) makes P-Connect
  false, even with an empty cut, and P-Term with it. `pren_ok h Σ p`
  asks h injective on the held ends only, so h may map two unrelated
  interface ends to the two ends of one channel. The renamed process
  then has a τ message on that free channel, and Q-Admin and Q-Comm
  (`q_tau`) keep the interface, so the continuation must be in P at the
  old, unadvanced types. S4.12 (1) named the condition ("create no new
  pair of partners in Σ"), and S4.13 left it out.
  Counterexample on paper, not in Rocq. t1 = close (send ⟨∗, d⁺⟩) with
  Σ1 = d⁺ : !1.end, t2 = let ⟨u, y⟩ = recv e⁺ in close y with
  Σ2 = e⁺ : ?1.end. Each single thread is in P at every level. P-Connect
  with ΣC = ∅ gives p = (∅, {t1, t2}) ∈ P⟦d⁺, e⁺ ⊢ 1⟧. Take h with
  d± ↦ c±, e⁺ ↦ c⁻, e⁻ ↦ c⁺, the identity elsewhere. It commutes with
  duality and is injective on {d⁺, e⁺}, so (rename) asks P of
  (∅, {t1[c⁺], t2[c⁻]}) at c⁺ : !1.end, c⁻ : ?1.end. That process takes
  a τ message on c, and `q_tau` asks the continuation in P at the same
  interface. The continuation closes c⁺ externally while the interface
  still says !1.end, so Q-Close fails and it is not in P at level 1.
  Hence p is not in P at level c_give + c_take + 1. A spawn reaches the
  same pair of threads, so P-Term fails as well, and with it
  `fundamental_proc`.
  Two repairs. (A) Ask h injective on every end of a held channel
  (which forbids new partner pairs). `Prel_rename` stays a projection,
  but the link case of P-Connect needs P of the other component after
  `csub o1 o2` when it holds o1‾ and o2‾, a renaming that does create a
  pair and so has to be internalized at once. That fusion lemma is then
  neither a projection nor reachable by the forward simulation (S4.12
  (2)). (B) Replace (rename) by a clause (fuse): every unfolding of P
  holds for sdrop D (kren h Σ) and (set_map (gch h) p.1 ∪ D, emapE h p.2)
  for every h that commutes with duality, is injective on the held
  ends, and creates new partner pairs only on the channels D, which h
  makes dual pairs at dual points of the interface, disjoint from the
  renamed restricted channels. D = ∅ is (A)'s renaming, h = id
  internalizes pairs of Σ. Internalize, the link case of P-Connect and
  `Prel_rename` are then projections, and a composite of fusions is a
  fusion. P-Connect and P-Term must establish (fuse) for their
  composites. A fusion of a composite is a composite of the fused
  components over a larger cut, so a lemma stated for every cut covers
  it, as (rename) was covered for renamed components. I recommend (B).
  Not started: Internalize, P-Connect, P-Join, P-Term. CheckAll lists
  193 results, all closed. No `Admitted` and no axiom.
- S4.19. The clause (fuse) (decision 4200d3d) in v2/relation/Relation.v:
  `sdrop`, `pfuse`, `dpairs`, `fuse_ok`, `pren_ok` with the condition
  "no new partner pair", `fuse_ok_id`, `pren_fuse_ok`,
  `fuse_ok_empty` (an empty interface admits D = ∅ only). The field
  `c_give_take` of `ctable`. v2/compat/Rename.v: the held ends of a
  fusion are the images of the held ends (`pheld_fuse`,
  `pheld_fuse_inv`), a composite of fusions is a fusion
  (`fuse_ok_compose`, `fuse_sdrop_compose`, `pfuse_compose`, through
  `kren_sdrop`), `Prel_fuse` as a projection, `Prel_rename` (D = ∅) and
  `Prel_internalize` (h = id: `dpairs D Σ → D ## p.1 → p ∈ P⟦Σ⟧ →
  (p.1 ∪ D, p.2) ∈ P⟦sdrop D Σ⟧`) as instances. `pren_ok_csub` asks in
  addition that the other component does not hold o2‾; when it does,
  the link case is a fusion with D = {ech o2}. Closure, Adequacy,
  Blind, LiveDF, PSwap and Conv follow (`fuse_ok_conv`). CheckAll lists
  196 results, all closed.
- S5.1. Two facts about E (v2/compat/EFacts.v), `Erel_cover` and
  `Erel_ty_mono`. The structural rules over every cost table
  (v2/compat/TermRules.v): groundings at heads, ends and entries,
  `Vrel_tsub`, `gen_e_unit` to `gen_e_pack`, E-Box at a positive cost
  of β. Stop at E-SpawnLam, with the counterexample in Rocq
  (v2/compat/SpawnGap.v, deviation "S5, E-SpawnLam").
- S5.2. `dftyped_sem` and `fundamental_of_spawn_lam`
  (v2/static/Fundamental.v): one induction on DF derivations through
  `hsat` and `pclose`, every rule but D-SpawnLam by a `gen_e_*` rule,
  D-SpawnLam by the premise `spawn_lam_rule κ_DF`.
  `fundamental_typed_of_spawn_lam` for the merged judgment.
- S5.3. The guard `glive` and `guarded` (v2/static/Guard.v),
  `Erel_bind_acts` (v2/compat/BindActs.v), the groundings with marks and
  every rule with marks (v2/compat/LiveRules.v).
- S5.4. `dftyped_later` and `live_fundamental_of_spawn_lam`
  (v2/static/LiveFundamental.v) at every table where give costs one or
  more, κ_L among them. The guard against Appendix B
  (v2/examples/GuardEx.v): `div_not_guarded` (#14), `pn_fix_not_guarded`
  (#13), `cx_not_guarded` (#15, the box of GuardCex), the spawn loop
  (`spawn_loop_not_guarded`, #12 and #40 in shape), and the accepted
  `loop_guarded` and `stage_guarded` (the stage of B.1 #4).
- S5.5. Targets for the process level, not proved, because they need
  P-Term and P-Connect of S4 and the repair of E-SpawnLam.
  `fundamental_proc : strict W → Σ ⊢_W p : T → Σ ⊨_W p : T` by induction
  on `ptyped`: P-Term from `fundamental` and `sem_p_term`, P-Connect and
  P-Join from `sem_p_connect` (P-Join through `p_join_iff_connect`).
  `soundness : strict W → ∅ ⊢_W p : T → deadlock_free p` is `adequacy`
  after `fundamental_proc`. `live_fundamental_proc` asks every thread of
  p guarded, and `live_soundness : strict W → ∅ ⊢_W p : T → guarded p →
  deadlock_free p ∧ no_tau_divergence p` is `live_adequacy` after it.
  `soundness_source : strict W → prim T → ∅ ; ∅ ; [] ⊢^(∅, None) _ W t : T
  → deadlock_free (∅, {[+ t +]})` is P-Term at C0 = ∅ and Σ = ∅, with
  no creation constraint. A.3 writes `soundness_source` without
  strictness of W, which `fundamental` needs: the laws of the families
  of W must be acyclic, so the statement keeps `strict W`. CheckAll
  lists 203 results, all closed. No `Admitted` and no axiom.
- S5.6. O-Spawn without the lower point, as decided (deviation "S5,
  O-Spawn without the lower point"). `spawn_gap` and v2/compat/SpawnGap.v
  are deleted, because the decision makes them false: under the new
  O-Spawn the thread of S5.1 is in E, with upper point (2)‾⁺, above both
  blocking points 1 and 2 (argued, not in Rocq). Stop: E-SpawnLam is
  still false. The thunk clause reads the body at every future F above
  its upper point u (`ub_lt W' ub F`), as V at an arrow does, while
  D-SpawnLam types the body at the empty future only. A body may create
  a channel at a fresh root g and block on it, and O-New picks g after F
  and u are fixed, so no u puts g below F. Counterexample on paper, not
  in Rocq: spawn (λ_. let ⟨c, c′⟩ = new_ℓ in let ∗ = spawn (λ_. close c)
  in close c′), typed by D-SpawnLam at Θ = ∅. For any u take F = {u⁺}
  and g a root other than the root of u. The body reaches close c′,
  blocked at g‾, and g‾ ≺ u⁺ fails, so the body is not ready at F and
  not in E at a positive level, and neither is the spawn.
  Proposed repair, needing a decision: the thunk clause reads the body
  at the empty future only, Vthunk without ub and with F = ∅. The
  spawned thread starts with no context, so nothing it could wait for
  lies in a future. `Erel_spawn` still holds, because V at an arrow
  gives the body at F = ∅ for every upper point. E-SpawnLam then follows
  from the body at the empty future (`spawn_lam_rule` and
  `spawn_lam_later` become provable), and P-Term of S4 must spawn
  threads at the empty future, which it does if it reads `fundamental`
  at F = ∅. Not done: `spawn_lam_rule`, `spawn_lam_later`, the
  unconditional `fundamental` and `live_fundamental`, and E blind in its
  environment. CheckAll lists 199 results, all closed. No `Admitted` and
  no axiom.
- S5.7. The thunk of O-Spawn at the empty future, as decided after
  S5.6. `Vthunk` without the upper point, `Vrel_thunk` for
  `Varr_spawn_iff`. `Erel_spawn_thunk` and `gen_e_spawn_lam`
  (v2/compat/TermRules.v), `later_spawn_lam` (LiveRules.v), so
  `spawn_lam_rule κ` and `spawn_lam_later κ` hold at every table
  (`spawn_lam_valid`, `spawn_lam_later_valid`). The theorems of A.3
  without premises: `fundamental`, `fundamental_typed`
  (v2/static/Fundamental.v), `live_fundamental`, `live_fundamental_typed`
  (v2/static/LiveFundamental.v). E blind in its environment is left to
  compat/Conv.v of S4 (deviation "S5, E blind in its environment").
  CheckAll lists 201 results, all closed. No `Admitted` and no axiom.
- S4.20 (in progress). v2/compat/Connect.v, P-Connect. Done:
  the environments of a cut (`pfree`, `cut_dual`, the side conditions
  `conn`, symmetric by `conn_sym`), the composite `pconn`, liftings of a
  composite (`pconn_lift`, `soup_split`), τ steps and session steps of
  one component inside the composite (`tau_lift`, `sess_lift`,
  `link_tau`), the offers of the composite (`offered_1_c`,
  `offered_c_1`), an offer on a cut end meets an offer on its partner
  (`dual_offers`), a chain of cut ends stops in a strict world
  (`finite_lt_acc`, needing no decision of ≺), readiness of one
  component at a primitive type (`comp_ready`), and of the composite
  (`chain`, `pc_ready`), P-Stop of the composite (`pc_stop`).
  Deviations found. (1) P-Connect asks the type T of p1 primitive
  (`prim T`, as `ptyped_prim` gives). Otherwise p1 may stop with a value
  holding an end while p2 waits, and the composite is not ready.
  (2) `conn` asks Σ1, Σ2 and ΣC partner-free (`pfree`). A component
  that holds both ends of a free channel in its interface can hand one
  end across the cut, and the τ messages of the composite on that free
  channel then keep the interface at the old types (`q_tau`), so the
  composite is not in P. S5 has to show that typed interfaces are
  partner-free, or P-Term has to ask it. (3) `conn` asks the restricted
  channels of each side apart from its own interface channels as well.
  Plan for the rest. The step clause of the composite, one lemma per
  kind of event, over the clauses of the two components (component
  steps through `q_tau`; a message, close or choice across the cut as
  Q-Send, Q-Close, Q-Select of one side and Q-Recv, Q-Close, Q-Branch
  of the other at cost κ(give) + κ(take), both read off the components'
  clauses at the current level; a link renames or fuses the other side
  by `Prel_fuse`; external steps re-split the interface by channels).
  Since then (same entry): `Prel_S_ind_fuse` and `Pbody_fuse` (the
  induction over steps of cost 0 with its predicate closed under
  fusion, `Φfuse`), `csub_dcomm_all`, `ren_held_id` and `Prel_ren_id`
  (a renaming that fixes the held ends keeps P), `istep_local` (a step
  of the composite taken by one side alone is a step of that side),
  and the section `core` of the step clause. Its context: the clauses
  of the two components at a strict W1 (fixpoint readers X1, X2 with
  `X1P`, `X2P`), the lemma at every lower level (`L : ConnL κ j W1 T`),
  P of every fusion of each component (`HP1`, `HP2`), and the
  continuations at the same level (`G1` for a continuation of p1 in X1
  against any p2 in P, `G2` for a continuation of p2 in X2 against any
  fusion of p1). Proved in `core`: `tau_l1`, `tau_l2` (τ steps of one
  side, a link of a restricted channel renaming the other side by a map
  that fixes its held ends), `conn_delete` and `tau_close` (a close
  across the cut), `conn_update` and `tau_choice12` (a choice across the
  cut, p1 selecting). The section `core` now lives in
  v2/compat/ConnectSteps.v, so that Connect.v does not recompile.
  Open in `core`: a choice across the cut with p2 selecting (the mirror
  of `tau_choice12`, `conn_update` at edual o), a message across the cut (Q-Send of
  one side, Q-Recv of the other with Θ2 = Σv ∪ Θe, the new cut re-split
  by the ends of Σ1 ∪ Σ2), a choice across the cut, the links of a cut
  end (`csub` on the other side: renaming when o2 is an interface end,
  fusion with D = {ech o2} when o2 is a cut end, `Prel_conv` for the
  interface type of o2), the links whose removed channel is restricted
  on the other side (`csub o1 o2 ∘ csub o2 o1 = csub o1 o2`), the
  contradictions (a side acting externally on an end it does not hold,
  through `Psteps_sends`), the six external clauses of each side, and
  the assembly of `Pclauses`. Then the splitting of a fusion of the
  composite into fusions of the components over a larger cut, and the
  wrapper. Note: Connect.v compiles in about 3 minutes; set_solver
  under the big section context is slow, so clear the context first.
  Then the induction: strong induction on the level, inside it
  `Prel_S_ind` on p1 for every p2 and on p2 for every fusion of p1, and
  the clause (fuse) of the composite by splitting a fusion of the
  composite into fusions of the components over a larger cut.
- S8.1. `lf_run_criterion` and `thread_progress` ported to the runs of
  S1 (v2/lockfree/Criterion.v, ThreadProgress.v), without
  `lf_criterion`, `fuel_bound`, `rank_bound` and `waits` (quirk A3).
- S8.2. `idle_dual` (v2/soup/Idle.v): S′ ≈ dual S gives
  idle S ↔ idle S′, the duality lemma S6 owed.
- S8.3. F-Link asks `plink` (deviation "S8, F-Link").
- S8.4 to S8.19. Soup states, `Soup`, `⊪`, the update `lf_next`
  (v2/soup/State.v, Soup.v), map facts (OwnFacts.v, SyncMaps.v,
  LinkMaps.v), dual session types along a step (Sessions.v), the step
  case by case (SoupStep.v: β, new, new_κ, spawn; SoupSync.v: message,
  close, choice; SoupLink.v: link), and `lfsoup_step`, `lfsoup_run`,
  `lfsoup_isteps` (SoupRun.v). No `Admitted`.
- S8.20, S8.21. `Erel_tacc`: a thread in E[live] at a positive level,
  with its spawned children, admits no infinite run of administrative
  steps, because O-Spawn reads the child inside the parent's least
  fixpoint. The multiset extension of that order is well founded
  (`mstep_acc`), and a τ step of a soup is one of its steps
  (`padmin_mstep`). `soup_no_tau_divergence` (v2/soup/SoupTau.v).
- S8.22. `sp_fin` (deviation "S8, finite counters").
- S8.23 to S8.31. The facts of one soup (soup/LFLocal.v), steps of a run
  without the soup and the ends an event touches (LFRunFacts.v,
  LFEvents.v), and the run-level lemmas of soup/LFAdequacy.v: local
  progress by well-founded induction on the point of the waited end
  (`lf_local_progress`), the rank (`lf_rank`, `lf_stab`), persistence of
  an enabled thread (`lf_pers`), the measure (`lf_fuel`): a link spends a
  ticket, a step of the holder on another end ticks the partner's
  counter, which F-Tick keeps at 1 or more because the partner is not
  idle (F-Wait of the waiter, `partner_busy`, `idle_dual`), a hand-over
  passes it with one unit less, and every other step keeps it while the
  holder's step is administrative.
- S8.32. `relabel_map`, `soup_relabel` (deviation "S8, liftings").
- S8.33. `lf_adequacy_soup`, `lf_adequacy : lfworld W → ∅ ⊪_W p : T →
  lock_free p`, `lf_thread_progress` (v2/soup/LFAdequacy.v).
- S8.34. Notation test v2/test/SoupNotations.v, README section, CheckAll
  entries. S8 done.
- S9.1. The soup clause `sp_psig` (v2/soup/State.v): an end of the
  interface, Σ !! o = Some (S, x), has Π !! o = Some S, the session type
  of its entry exactly. The S8 step lemmas are at Σ = ∅, where the
  clause is vacuous (`soup_keep` and the constructor after it in
  SoupStep.v). `soup_relabel` holds at every Σ.
- S9.2. Soup composition (v2/soup/SoupCompose.v). `soup_par`: soups
  over Σa and Σb with disjoint thread ids, dom Σa ## dom Σb, C1 ## C2,
  C1 ## chans Σb and C2 ## chans Σa give a soup of (C1 ∪ C2, M1 ∪ M2)
  over Σa ∪ Σb at W1 ⊔ W2 and refill max N1 N2, with K, A, Π the unions
  and tk, U split by `tsel (dom M1)`. `soup_nu`: a soup over Σ ∪ Σ_R,
  where Σ_R holds both ends of each of its channels at dual session
  types and points, C ## chans Σ_R and chans Σ ## chans Σ_R, gives a
  soup of (C ∪ chans Σ_R, M) over Σ. `soup_connect` is `soup_nu` after
  `soup_par` under exactly the side conditions of `p_connect` (the
  map disjointness of Σ1, Σ_C and of Σ2, Σ̄_C follows from the channel
  conditions). P-Join has the same soup. `soup_term`: one thread 0
  holding every end of Θ = Σ at credit N ∪ Θ_B, with counter N
  (`kterm`), in E[live] at `tenv_erase Θ` and in FuelE at
  `te_sty <$> Θ`, gives a soup of (C0, {0 ↦ t}) over Σ. No `Admitted`.
- S9.3. The soup half of `⊪` (v2/soup/LFCompose.v). `lf_soup`,
  `lf_sem_iff`, `soup_lift` (the soup at every lifting, at every Σ),
  `lf_soup_connect` (the second component's thread ids shifted past
  those of the first, `tshift`), `lf_soup_term`, `typed_live` (a guarded
  thread typed at a finite N is in E[live] at its environment, through
  `live_fundamental_typed`, `Erel_conv` and `Erel_blind`),
  `lf_soup_term_typed`, and `lf_sem_term`, `lf_sem_connect` with the
  live process conjunct as a premise. CheckAll lists 248 results, all
  closed.
- S9.4. `lf_soundness_source : lfworld W → guarded t → prim T →
  ∅ ; ∅ ; [] ⊢^(∅, None) _{W,N} t : T^a ▷ c ; ϑ (N finite) →
  meets ϑ 0 tk → lock_free (∅, {[+ t +]})`, from `lf_soup_term_typed`
  and `lf_adequacy_soup`, with no process conjunct. CheckAll lists 249
  results, all closed.
- S9.5. Targets, not proved. Each is the soup lemma of S9.2 and S9.3
  plus the P lemma named.
  `lf_p_term : strict W → guarded t → [the premises of p_term at Some N]
  → meets ϑ 0 tk → Σ ⊪_W (C0, {[+ t +]}) : T` is `lf_sem_term` after
  the live P-Term `∀ n, (C0, {[+ t +]}) ∈ P[live]^W _ n⟦Σ ⊢ T⟧` from
  the same premises (S4 P-Term at κ_L, the thread through
  `typed_live`).
  `lf_p_connect : (Σ1 ∪ Σ_C) ⊪_{W1} (C1, E1) : T →
  (Σ2 ∪ Σ̄_C) ⊪_{W2} (C2, E2) : 1 → [the side conditions of p_connect]
  → (Σ1 ∪ Σ2) ⊪_{W1 ⊔ W2} (C1 ∪ C2 ∪ chans Σ_C, E1 ⊎ E2) : T` is
  `lf_sem_connect` after the live P-Connect of S4.20 at W1 ⊔ W2. Its
  inputs: both components moved to W1 ⊔ W2 by `Prel_mono`
  (`wext_join_l`, `wext_join_r`); `conn Σ1 Σ_C C1 Σ2 Σ̄_C C2`, of which
  `cut_dual Σ_C Σ̄_C` follows from `senv_dual_lookup` (sdual S (dual S)
  by reflexivity) and the channel conditions are those of p_connect,
  but `pfree Σ1` and `pfree Σ2` are not given by p_connect (S4.20,
  deviation 2: S5 shows typed interfaces partner-free, or the rule asks
  it); `prim T` from `sp_prim` of the first soup.
  `lf_p_join`: the same with the live P-Join. Its soup half is
  `lf_soup_connect` unchanged.
  `Σ ⊩^N_W p : T` (`lfptyped`) is not defined. The proposal says the
  lock-free rules add fsem^N to P-Term. With the merged judgment of S7,
  `fsem_of_cost` gives fsem^N from `meets ϑ 0 tk`, so either premise
  serves, and a guarded thread is needed for `live_fundamental_typed`.
  The author chooses the form.
  `lf_fundamental : strict W → Σ ⊩^N_W p : T → Σ ⊪_W p : T`, with every
  thread guarded, by induction: P-Term by `lf_p_term`, P-Connect by
  `lf_p_connect` with strict W1 and strict W2 from `strict_join_iff`,
  P-Join by `lf_p_join`.
  `lf_soundness : lfworld W → ∅ ⊩^N_W p : T → lock_free p` is
  `lf_adequacy` after `lf_fundamental`.
  If Q12 drops the process conjunct from `⊪`, no P lemma is needed: the
  same induction runs on `lf_soup` with `lf_soup_term_typed` and
  `lf_soup_connect`, and `lf_adequacy_soup` closes `lf_soundness`, as in
  `lf_soundness_source`.

- S4.21. A choice across the cut with p2 selecting (`tau_choice21`,
  compat/ConnectSteps.v). A message across the cut in both directions
  (`tau_msg12`, `tau_msg21`, compat/ConnectCross.v). The receiver takes
  Θ2 = Σv ∪ Θe, the ends the sender moves. Afterwards the sender holds
  E1, the receiver E2, and the cut is re-split by the interface Σ1 ∪ Σ2
  (`fin`, `fout`, compat/ConnectSplit.v). `conn_filter` gives the side
  conditions of P-Connect for that split from conditions on E1, E2 and
  Σ alone, and the classes of an end under a cut (`cls_1`, `cls_C`,
  `cls_2`, `cls_D`, `cls_c1`, `cls_c2`) discharge them. The environment
  lemmas of a message (`msg_recv_ok`, `msg_conn`, `msg_iface`,
  `msg_chans`, compat/ConnectMsg.v) read environments and channel sets
  only, so p2 sending uses them through `conn_sym`. A message whose
  give and take cost more than the level lands at level 0, where P
  holds. No deviation.
- S4.22. Links whose kept end is restricted on the side of the actor
  (`tau_link_own1`, `tau_link_own2`, compat/ConnectLink.v). The actor
  takes the link of o2 (the label is unordered), and the composite is
  that result renamed by csub o1 o2, because csub o1 o2 after
  csub o2 o1 is csub o1 o2 (`csub_csub`, compat/ConnectRen.v). This
  covers the removed channel being a cut channel or restricted in the
  other component. A renaming of the composite that fixes the interface
  keeps `conn` (`conn_rename`), and `ren_comp1`, `ren_comp2` turn a step
  of one side into the step clause of the renamed composite (G1 or G2
  at cost 0, the lemma at the lower level otherwise). `pren_ok_csub_r`:
  csub o1 o2 is a renaming whenever o2 and o2‾ are not held, whatever
  happens to o1. No deviation.
- S4.23. Links of p1 on two ends it does not restrict (`tau_link_ext1`,
  compat/ConnectLink.v): Q-Link of p1. The removed end o1 is then a cut
  end. If the kept end o2 is an interface end of p1, the holder of o1‾
  in p2 now holds o2, at the type of o1‾, which `Prel_conv` brings to
  the interface type of o2 (`sdual_trans_l`), and o2 moves from Σ1 to
  Σ2 (`conn_link_iface`). If o2 is a cut end, p2 holds both ends of the
  channel of o2 afterwards, a fusion with D = {ech o2}
  (`fuse_ok_csub_cut`, `kren_csub_eq`, `conn_del`, compat/ConnectRen.v).
  The order of the two ends in the label is free (`pair_eq`). Note for
  successors: `tauto` and `set_solver` under the section context of
  `links` are slow when the goal mixes many unions; split the goal and
  `clear` first (one `set_solver` took 28 s and failed before the
  split). No deviation.
- S4.24. The mirror `tau_link_ext2` (a link of p2 on two ends it does
  not restrict). When p2 links its cut end o1 with its interface end
  o2, G2 needs the fusion of p1 to land exactly on Σ1' ∪ ΣC', so Σ1'
  keeps o2 at the type of o1‾ (`conn_retype1`), and `Prel_conv` brings
  the composite back to Σ1 ∪ Σ2 at the end. No deviation.
- S4.25. Every τ step of the composite (`tau_all`, compat/ConnectTau.v).
  β, new, spawn and steps whose threads all lie in one component are
  steps of that component (`tau_l1`, `tau_l2`). A message, close or
  choice across the components is one of `tau_msg12`, `tau_msg21`,
  `tau_close` (both orders, through edual), `tau_choice12`,
  `tau_choice21`. A close of two threads of one component on a channel
  it does not restrict contradicts its Q-Close clauses, because both
  ends would lie in its partner-free interface (`close_same1`,
  `close_same2`). A link is local, or `tau_link_own1/2`, or
  `tau_link_ext1/2`. So the τ clause of P-Step holds for the composite
  over the clauses of the two components. Open in order: the six
  external clauses of each side (Q-Send and Q-Recv of the composite
  re-split the cut like the message case), the assembly of `Pclauses`
  with `pc_stop` and `pc_ready`, the splitting of a fusion of the
  composite into fusions of the components over a larger cut, and the
  wrapper (strong induction on the level, `Prel_S_ind_fuse` on each
  side), then P-Join and P-Term. No deviation.
- S4.26. External steps of the composite, first part
  (compat/ConnectExt.v). An external step of the composite is a step of
  the component of its thread on one of its own interface ends
  (`ext_split`; the subject is no cut end because the composite
  restricts the cut). Close, select, branch and link change the
  interface of that component only, so `ext_comp1` and `ext_comp2` (G1
  or G2 with the identity fusion at cost 0, the lemma at the lower level
  otherwise) give Q-Close, Q-Select, Q-Branch and Q-Link of the
  composite (`ext_close`, `ext_select`, `ext_branch`, `ext_link`), with
  `conn_del_iface1/2` and `conn_retype1/2`. Open in order: Q-Send and
  Q-Recv of the composite (a send can move cut ends, whose partners
  then join the interface; a receive can bring ends whose partners lie
  in the other component, which become cut ends; both re-split the cut
  as in S4.21), the assembly of `Pclauses` for the composite from
  `pc_stop`, `pc_ready`, `tau_all` and the six external clauses, the
  splitting of a fusion of the composite into fusions of the components
  over a larger cut, the wrapper, then P-Join and P-Term. No deviation.
- S4.27. Q-Send and Q-Recv of the composite (`ext_send`, `ext_recv`,
  compat/ConnectExtMsg.v) over the environment lemmas of
  compat/ConnectSendEnv.v. A send of p1 on its interface end moves Σv1
  and Θe1. In the composite the moved cut ends of Σv1 are restricted,
  so they leave with Θe = fout Σ Σv1 ∪ Θe1, and their partners in p2
  join the interface with Σe = Σe1 ∪ ΣDm (`snd_vr`, `snd_del`,
  `snd_split`, `snd_payload`, `snd_moved`). The cut after the send is
  re-split by the composite's new interface (`snd_conn`, `snd_iface`,
  `snd_chans`). A receive of p1 is a receive of p1 at the same Θ2
  (`rcv_ok1`), and an end of Θ2 whose partner lies in Σ2 becomes a cut
  end (`rcv_conn`, `rcv_iface`, `rcv_chans`). p2 acting uses the same
  lemmas through `conn_sym`. `ext_comp1'`, `ext_comp2'` give the step
  clause of a component step over a re-split cut. No deviation.
- S4.28. The clauses of P for the composite (`pc_clauses`,
  compat/ConnectExtMsg.v) from `pc_stop`, `pc_ready`, `tau_all` and the
  six external clauses. No deviation.
