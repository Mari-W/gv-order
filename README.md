# SPO-LR-DF: deadlock freedom by strict partial orders and a logical relation

This repository holds a Rocq development of a step-indexed logical relation
for GV♯, indexed by worlds of points and their order, and the deadlock freedom
it gives. A static type system with points, frames and constrained boxes
(□∀ιs. C) is sound for it. Every typed closed program is deadlock free.

## Building

The development needs Rocq 9.1 or 9.2 with `rocq-stdlib` and `rocq-stdpp`
(1.13). With the opam switch active, run

```
eval $(opam env)
make -j$(nproc)
```

A clean build takes about 12 minutes. If `Makefile.conf` is missing, run
`rocq makefile -f _CoqProject -o Makefile` first. The logical root is `LRGV`,
so `theories/lang/Syntax.v` is the module `LRGV.lang.Syntax`. The development
has no axioms and no admitted proofs.

## Map of theories/

`lang/`, the calculus.

- `Syntax.v`: terms with de Bruijn variables and channel names, the constants select₁, select₂ and branch included.
- `Semantics.v`: the labelled term semantics and the process LTS, with the choice labels c◁i, c▷i and P-Act-Choice.
- `Safety.v`: deadlock freedom and the other process properties, and progress.
- `ThreadSim.v`: threads related one to one and runs of β steps, shared by the simulations of pgv/ and pn/.
- `ChannelSwap.v`: transpositions of channel names commute with the LTS.
- `Harmony.v`: a reduction semantics for soups agrees with the LTS (`harmony`).

`types/`, the types.

- `Types.v`: types with boxes over points and session variables and existential points, context-free session types (Skip, ;, !P, ?P, ⊕, &, Close, μ), their head normal form `unfoldS` (unr), points, constraints, duality, environments, creation constraints over n variables (`creation_ok`), and the constants as constrained type-indexed schemes (`konst_sig`, `konst_ty`, SHARP-EDGES 147).
- `SessionEquiv.v`: bisimilarity ≈ on heads, the laws of ; and μ, and duality ⊥.
- `LinearEnv.v`: linear variable environments, splitting and weakening.

`relation/`, the logical relation.

- `Worlds.v`: worlds, their facts ≡ and ≺, extension and strictness.
- `Creation.v`: creation constraints. The closed form of T + C (`interp`), the world of new (`wext_cc`), transfer of `cc_ok` (`cc_ok_transfer`) and the model lemma (`cc_model`).
- `Readiness.v`: readiness of terms (with a frame) and of processes.
- `FutureConj.v`: readiness splits into the empty future and the singleton futures (`ready_t_conj`). The same split of E is open (SHARP-EDGES 146).
- `LogicalRelation.v`: V, E and P with O-Select, O-Branch, Q-Select and Q-Branch, V-Box over session instances and V-Ex, semantic typing, and `adequacy`.

`invariance/`, properties of the relation (spec §10).

- `PointRenaming.v`: renaming points maps the relation to itself.
- `EquivInvariance.v`: the relation is invariant under ≈ (semantic E-Conv).
- `Monotonicity.v`: monotonicity in the world and frame weakening.
- `PointConversion.v`: aliased points are interchangeable in types and entries.
- `ChannelRenaming.v`: renaming channels maps the relation to itself.
- `JunkRenaming.v`: renaming a channel a process does not own.

`composition/`, the process rules (spec §11).

- `ReadyChain.v`: readiness of a composite from readiness of its parts.
- `Internalize.v`: a process that holds both ends of a link fuses them (`Prel_internalize`).
- `ConnectCut.v`: P-Connect, the cut and the external steps of one component.
- `ConnectSteps.v`: P-Connect, links, internal steps and synchronizations across the cut.
- `PConnect.v`: P-Connect assembled (`Prel_connect`).
- `PTerm.v`: P-Term (`Prel_term`) and P-Connect with an empty cut (`Prel_indep`).
- `PConnectN.v`: P-Connect for n components (`Prel_connect_n`).

`rules/`, the term rules (spec §11).

- `Bind.v`: evaluation contexts (`Erel_bind`).
- `TermRules.v`: one compositionality lemma per typing rule.
- `BoxRules.v`: the rules that need the box, E-App, E-Force, E-Exp and E-Contract.
- `ExRules.v`: E-Pack and E-Open for existential points (`sem_typed_pack`, `sem_typed_open`).
- `SemanticRules.v`: the infinitary judgment of these rules and its fundamental theorem.

`static/`, the static system (spec §9).

- `FactTheory.v`: frames, box hypotheses and the judgments Γ ⊢ x ≡ y and Γ ⊢ a ≺ b, with program order as the rule `fl_po`.
- `PointSubst.v`: substitution of points and the transport of facts along it.
- `Typing.v`: the typing judgments `typed` and `ptyped`.
- `Source.v`: the source judgment `styped` without a world, the fact theory of the hypotheses alone (`heqs`, `hfl`, `hlt`) and the embedding (`styped_typed`, `typed_styped`, `styped_iff`).
- `Fundamental.v`: `fundamental`, `fundamental_proc`, `soundness` and `soundness_source`.

`examples/`, the examples of spec §13.

- `ExampleTools.v`: strict worlds from ranks, derived rules and tactics.
- `Sync.v`, `Cycle.v`, `Delegation.v`, `Scheduler.v`: first-order examples.
- `Factory.v`: the factory at one top-level point and under □∀ι, both under a top-level constraint.
- `FactoryEx.v`: the factory with an existential result, introduced by E-Pack. The client holds two handles at once and uses them in order, in the empty world (`fx_deadlock_free`).
- `RequestReply.v`, `Relay.v`, `TailCall.v`, `ReceivedChain.v`, `Forwarder.v`: recursive boxes with infinite constraints.
- `Ordered.v`: a box whose constraint orders its two arguments.
- `FreshBetween.v`: a box over ι ≺ κ that creates a channel between them with E-NewFresh (`fb_between_underivable`, `fb_deadlock_free_empty`).
- `FreshMany.v`: the fresh channel acts three times between ι and κ, under the infinite constraint {ι ≺ δ} ∪ {δ+k ≺ κ} (`fm_deadlock_free`).
- `FreshTools.v` and `SyncFresh.v`, `CycleFresh.v`, `SchedulerFresh.v`, `RequestReplyFresh.v`, `TailCallFresh.v`, `RelayFresh.v`: the closed examples retyped with fresh points in smaller worlds, as copies `*_main_ex` that bind each fresh channel by the encoded let of new (`*_deadlock_free_fresh`).
- `LitTools.v`: the shared tools of the examples taken from the literature. Program order over a gap, the gate tactics, the chain of points ι[0]ⁿ `slotv` with the orders `dlt` and `ult` and their creation-constraint wrappers, and `tv_case`.
- `MilnerSched.v`: Milner's cyclic scheduler of Dardha and Gay, Example 1 in full with k = 3 agents and their collectors, every channel at a point of one root (`ms_deadlock_free`).
- `KobForwarder.v`: Kobayashi's recursive forwarder server, Example 2, as a recursive box whose fresh reply channel sits at ι[0] for the point ι of the channel it answers on (`fw_deadlock_free_kob`).
- `FactServer.v`: the factorial server of Kobayashi and of Padovani, the same shape with the branch on the received value (`fc_deadlock_free`).
- `Stream.v`: Padovani's `stream`, a producer that sends a fresh continuation each round, with a consumer (`st_deadlock_free`).
- `Congruence.v`: a box whose derivation needs both congruences of ≡, one alias between base points read at a payload point x[i] and at the successor (`cg_deadlock_free`).
- `Rejected.v`: programs the static system rejects (`rr_call_underivable`, `sched_rev_underivable`, `ms_rev_underivable`, `badlink_underivable`, `ord_no_constraint`).
- `SendTreeType.v`: the type of sendTree with the coarse ceiling over walks through x+1 and x[i], a smoke test (SHARP-EDGES 73, 142).

`examples/cfst/`, the examples of context-free session types (SHARP-EDGES 74, 75, 142 and 144). Since K11 a choice moves its channel from x to x[i] and owes x ≺ x[i], and ceilings range over the walks from a point. Every example states a whole-program `styped` derivation, creates its channels with the existential new under a creation constraint, and proves deadlock freedom with `soundness_source`.

- `CfstTools.v`: hereditary contractiveness by depth, congruences of ≈, case and E-Open for Θ = ∅, facts of constraints with outer points, the ceiling C₀, the lockstep creation constraints and `cc_ok_out` for constraints with outer points.
- `TreeCopy.v`: recvTree as `drain` and sendTree after recvTree as `copy`, both with polymorphic recursion and existential points, run on a fixed tree (`tree_deadlock_free`).
- `Stream.v`: the two streams of Mordido and Pérez in a cycle (`st_deadlock_free`).
- `CfstDeadlock.v`: their classic deadlock is not deadlock free and so has no `styped` derivation (`dl_untypable`, `dl_untypable_source`). Its repair types (`dlfix_deadlock_free`).
- `CfstScheduler.v`: Milner's cyclic scheduler with three schedulers and three workers, each channel created under a rank constraint against the earlier ones (`sch_deadlock_free`).
- `TreeSum.v`: treeSum of Thiemann and Vasconcelos (Listing 2) with the reply after both subtrees, serving the client transform on a fixed tree (`ts_deadlock_free`).
- `ArithServer.v`: their arithmetic expression server (Listing 3) with binary choices and its fixed client (`as_deadlock_free`).
- `BranchOrder.v`: a branch that orders two channels against the other branch, typable with the payload points x[0] and x[1] of K11 and not under K5 (`bo_deadlock_free`, SHARP-EDGES 76, 144).
- `SkipDrop.v`: a program of Mordido and Pérez that drops both ends of a channel at Skip ends in a restricted name that no thread mentions, so it is not deadlock free under `terminated` (`sd_not_deadlock_free`, SHARP-EDGES 151).
- `SegmentInterleave.v`: a channel created after treeSum returns and ordered against the returned channel in both directions, under a local creation constraint (`si_deadlock_free`, SHARP-EDGES 152).
- `SegmentDeleg.v`: a channel created at the payload point of the channel treeSum returns and sent on it (`sd_deadlock_free`, SHARP-EDGES 152).

The context-free work runs on the core of branch `exists` since 2026-11-04 (docs/extensions/context-free.md, section "Ported to the exists core", SHARP-EDGES 141 to 145). theories/pgv and theories/pn are in the build again.

`mp/`, Mordido and Pérez in fragment v1 with repairs R1 to R6 (SHARP-EDGES 77, docs/extensions/adequacy/mordido-perez.md 12 and 13).

- `MPTypes.v`, `MPTyping.v`: their types and typing on our terms, the judgment yields the translated term.
- `MPWorld.v`: anchors for valuations, channel points named by their type in head form, the box constraint over every valuation.
- `MPTranslate.v`: the translation lemma and deadlock freedom of every closed program (`mp_translate`, `mp_deadlock_free`).
- `MPExamples.v`: the two streams typed in the source judgment and translated (`st_mp_deadlock_free`).

Version 2 in `mp/` supersedes fragment v1, with context-free session types, session type variables and functions over unbounded segments (SHARP-EDGES 78, docs/extensions/adequacy/mordido-perez.md 12 and 13).

- `MP2Types.v`, `MP2Typing.v`: their types and typing with Skip, ;, type variables and segment functions, the judgment yields the translated term.
- `MP2World.v`: denotations of raw session types, observational equivalence of points, the ceiling above junk, the box constraints of abstractions and segments.
- `MP2Translate.v`: the translation lemma and deadlock freedom of every closed program (`mp2_translate`, `mp2_deadlock_free`).
- `MP2Examples.v`: receiveTree with the tree channel, the two streams, the repaired classic deadlock and T2, each translated (`rt_mp2_deadlock_free`, `st_mp2_deadlock_free`, `df_mp2_deadlock_free`, `t2_mp2_deadlock_free`), and the rank of the tree channel after receiveTree, which depends on the size of the tree (`rt_rank_data`, SHARP-EDGES 79).
- `MP2Semantics.v`: their reduction (Fig. 15) with repairs R4 and R5, and their deadlock freedom (Definition 1) for a source program.
- `MP2Simulation.v`: a simulation between source configurations and translated processes, so every typed closed program is deadlock free in their semantics (`mp2_deadlock_free_source`, SHARP-EDGES 80, docs/extensions/adequacy/mordido-perez.md 14), with the four examples (`rt_deadlock_free_src` and the others).
- `MPRounds.v`: program 8, two loops that type at their first round and deadlock in their semantics (`p8_not_deadlock_free`, `p8_not_mtyped`), and unequal increments with matching rates through version 2 (`rr_mp2_deadlock_free`, SHARP-EDGES 81).

Version 3 in `mp/` extends version 2 with n-ary choices and with channels created after a segment call (SHARP-EDGES 82 and 83, docs/extensions/adequacy/mordido-perez.md 15).

- `MP3Types.v`, `MP3World.v`, `MP3Typing.v`: priorities at a depth for inner nodes of a choice, the levels below ⊥ and above ⊤, the low chain and the high chain.
- `MP3Translate.v`: the translation lemma and deadlock freedom (`mp3_translate`, `mp3_deadlock_free`).
- `MP3Examples.v`: the examples of version 2, a choice with three labels (`ch3_mp3_deadlock_free`), matching rates (`rr_mp3_deadlock_free`), and a channel created after receiveTree below the floor or above the ceiling (`rtA_mp3_deadlock_free`, `rtB_mp3_deadlock_free`).
- `MP3Simulation.v`: deadlock freedom in their semantics (`mp3_deadlock_free_source`) with every example (`ch3_deadlock_free_src3` and the others).

theories/mp stays at its world `Wmp` on the merged core. Translated new is `let_new_pair` typed by `t_new_at`, and segment constraints state x ≺ x[i] along every walk (SHARP-EDGES 145).

`counterexamples/`

- `DropCounter.v`: why the fresh point of E-Abs and E-Exp is a frame variable.

`pgv/`, adequacy for repaired Priority GV (docs/extensions/adequacy/pgv-adequacy.md).

- `PGVTypes.v`: PGV's priorities, types, duality, pr(·) and the monotone fragment `pgv_mono`.
- `PGVTyping.v`: the schemas and Fig. 2 on our terms with repairs R1 and R2 (`pgv_typed`, `pgv_frag`).
- `PGVWorld.v`: the protocol-point world `Wpgv`, its strictness and the translation of types.
- `PGVTranslate.v`: PGV derivations become `typed` derivations (`pgv_translate`, `pgv_deadlock_free`).
- `PGVSimulation.v`: the simulation of a program by its translation, and deadlock freedom of the program itself (`rel`, `fwd`, `final`, `pgv_deadlock_free_source`).
- `PGVExamples.v`: Example 2.1 of the paper, a delegation, a link, and the two counterexamples rejected.
- `PGVFalling.v`: two closed programs with falling sessions typed in repaired PGV (`fall2_typed`, `fallxy_typed`). `fallxy` shows that no translation that reads points off session types covers falling sessions (pgv-adequacy.md §8).

`pn/`, adequacy for Padovani and Novara, FORTE 2015 (docs/extensions/adequacy/padovani-novara.md §7).

- `PNTypes.v`: levels, channel, arrow, recursive and wrapped types, the level |t| and the shift ⇑ⁿ.
- `PNTyping.v`: Table 2 with T-App-Poly on our terms, repaired fix, as a judgment that also yields the translated term (`pn_typed`).
- `PNWorld.v`: anchors and ranks into ℤ with a top element, the constraint `Crel` and its acyclicity (`Crel_acyclic`), and the translation of types.
- `PNTranslate.v`: derivations become `typed` derivations at every anchor and offset (`pn_translate`), a closed program becomes a term of the source judgment (`pn_translate_source`, `pn_deadlock_free`).
- `PNExamples.v`: parallel Fibonacci and the signal pipe, both deadlock free, and three fixes whose body is no λ (`div_typed`, `divsend_typed`, `fixfork_typed`), two of them from pdf p. 14 of the chapter.
- `PNSemantics.v`: the reduction semantics of the chapter on the source syntax and Definition 1 (`src_pstep`, `pn_deadlock_free_src`), §8.
- `PNSimulation.v`: the simulation of the source by its translation and the theorem in the source semantics (`trel`, `fwd`, `pn_deadlock_free_source`).

## Main results

- `soundness` (static/Fundamental.v): a typed closed process at a strict world is deadlock free.
- `soundness_source` (static/Fundamental.v): a closed term of the source judgment under a top-level constraint C₀ over n point variables is deadlock free when C₀ is a creation constraint against the empty context (`creation_ok n nofact nofact (λ _, False) C₀`, the premise of new at n variables). `c0_creation_ok` shows it is the acyclicity of C₀ (`c0_acyclic`, SHARP-EDGES 148). Its premise is `styped ∅ [(C₀, ids n)] [] (∅, None) t T` and names no world. The proof types the term in `wnil` and starts the run in `wc0 n C₀`, the facts of C₀ at fresh constants (docs/extensions/existentials.md parts 6 and 7, sharp edges 110, 122).
- `styped` (static/Source.v): the judgment Δ ⊢^F_Γ t : T of static-system.md for a self-contained single-threaded source program, with Γ the hypotheses Ψ and the frame hypotheses Φ. Its type is `fhyps → hyps → lenv → sframe → expr → ty → Prop`, with no world and no channel environment. It mirrors every rule of `typed` for a form without channel constants and adds none. A world is a don't-care there, because a well-formed world relates two points only by program order or between two points of its support, every support name is a constant, and a source derivation names none (sharp edges 122). Program order is the rule `fl_po` of the fact theory (sharp edges 121). `styped_typed` sends a source derivation into `typed` at every world, `typed_styped` sends a derivation in a world of empty support back, and `styped_iff` is the equivalence (sharp edges 123). The whole-program typing lemma of every example states `styped`, and so does `pn_translate_source`. `typed` and `ptyped` keep their world for the process layer, and the PGV translation keeps `Wpgv`.
- `fundamental`, `fundamental_proc` (static/Fundamental.v): typed terms and processes are semantically typed.
- `adequacy` (relation/LogicalRelation.v): a semantically typed closed process is deadlock free.
- `Prel_term`, `Prel_indep` (composition/PTerm.v), `Prel_connect` (composition/PConnect.v), `Prel_connect_n` (composition/PConnectN.v), `Prel_internalize` (composition/Internalize.v).
- `Erel_bind` (rules/Bind.v).
- `pgv_deadlock_free` (pgv/PGVTranslate.v): the translation of a closed program of type 1 in the monotone fragment of repaired PGV is deadlock free, and by `pgv_deadlock_free_source` (pgv/PGVSimulation.v) so is the program itself. The examples of pgv/PGVExamples.v apply the latter.
- `pn_deadlock_free` (pn/PNTranslate.v): the translation of a closed program of type unit in fragment v1 of repaired Padovani and Novara is deadlock free. `fibo_deadlock_free` and `pipe_deadlock_free` (pn/PNExamples.v) apply it.
- `pn_deadlock_free_source` (pn/PNSimulation.v): such a program is deadlock free in the semantics of the chapter (Definition 1), with every fix λf.e at any type (padovani-novara.md §9). `fibo_deadlock_free_src`, `pipe_deadlock_free_src`, `div_deadlock_free_src`, `divsend_deadlock_free_src` and `fixfork_deadlock_free_src` apply it.
- The examples: `sync_deadlock_free`, `cycle_deadlock_free`, `deleg_deadlock_free`, `sched_deadlock_free`, `fac_deadlock_free`, `fa_deadlock_free`, `rr_deadlock_free`, `rel_deadlock_free`, `tc_deadlock_free`, `ch_deadlock_free`, `fw_deadlock_free`, `fb_deadlock_free`, one per file in examples/. Also `tree_deadlock_free`, `st_deadlock_free`, `dlfix_deadlock_free`, `sch_deadlock_free`, `ts_deadlock_free`, `as_deadlock_free`, `bo_deadlock_free`, `si_deadlock_free`, `sd_deadlock_free`, `dl_untypable` and `sd_not_deadlock_free` in examples/cfst/.
- The examples from the literature, each typed as its paper writes it and each stated in the world-free `styped`: `ms_deadlock_free` (Milner's cyclic scheduler of Dardha and Gay, Example 1 in full), `fw_deadlock_free_kob` (Kobayashi's recursive forwarder server, Example 2), `fc_deadlock_free` (the factorial server of Kobayashi and of Padovani), `st_deadlock_free` (Padovani's `stream`). `cg_deadlock_free` is the first derivation that uses the congruences of ≡ (docs/extensions/literature-examples.md, sharp edges 130 to 136).
- E-NewFresh (`t_newfresh_open`, static/Typing.v) creates a channel at a fresh point ι with a constraint C that relates points of ι (ι+k, ι[i], …) to known points, when u ≺ v holds for every u ≺ p and q ≺ v of C with q at or after p in program order. `t_newfresh_lh_open` is the form L ≺ ι ≺ H. World extension is unchanged (docs/extensions/fresh-points.md, sharp edges 90 to 96). E-NewFresh is a lemma on the encoded term let p = new ∗ in let (x, y) = p in t (`let_new`), not a rule (sharp edges 103).
- Existential points ∃^ℓ ιs. C. T (`TEx`, types/Types.v) with E-Pack, E-Open and V-Ex, where the lower bound ℓ is absent (`LNone`, holds nothing), a point, or ⊥, the unknown point (SHARP-EDGES 149), and the signature new : ∗ ⊸ ∃^⊥ ι. C. S@ι ⊗ S̄@ι. C is any set of facts between points of ι and outer points, by ≺ and ≡, that is acyclic and conservative over the context (`cc_ok`, sharp edges 105 and 106). relation/Creation.v proves it sound (`interp`, `wext_cc`, `cc_ok_transfer`), and `cc_model` proves it for concrete constraints. `t_new_at` (static/Fundamental.v) gives new at a known point on the encoded let, and `t_new_open` (static/Typing.v) new under any creation constraint. Every example types in the empty world. Factory and the PN translation start under a top-level constraint C₀ (`soundness_source`). The PGV translation keeps its world `Wpgv`, because its payloads hold global points (sharp edges 107, 108, 110 to 112). W stays as a parameter of `typed` for configurations, and source programs type in the world-free `styped` (static/Source.v, sharp edges 122). A frame carries a flag for a held ∃^⊥, under which no call with an upper point passes the gate (docs/extensions/existentials.md, sharp edges 97 to 100 and 103).
- Session choice is a derived form. `sel1_typed`, `sel2_typed` and `branch_typed` (examples/ChoiceEnc.v) type selection as sending inj_i of a fresh channel whose arm lies at x[i], and branching as a receive and a case. `choice_deadlock_free` is T1 ∥ T2 ∥ T3 of mordido-perez.md §9.5, whose two branches need opposite orders against d, and `loop_deadlock_free` a recursive choice server. No rule of the core changes (docs/extensions/choice-encoding.md, sharp edges 137).
- Primitive choice translates into that encoding. `choice_translate` (examples/ChoiceTranslate.v) proves that replacing select and branch by the encoded terms preserves `styped` on a fragment, and `translated_deadlock_free` (examples/ChoiceTranslateEx.v) applies it to T1 ∥ T2 ∥ T3. The negative control with both arms at one payload point is underivable by inversion (`t2_underivable`, `negative_new_at`, examples/ChoiceNegative.v). A message whose payload is an existential is a derived form (`send_ex`, `recv_ex`, `ex_deadlock_free`, examples/ExPayload.v, docs/extensions/existential-payloads.md). The three are summarized in docs/extensions/SMALL-THEOREMS-REPORT.md.
- A payload of a channel or nothing. `some_deadlock_free`, `some_swapped_deadlock_free` and `none_deadlock_free` (examples/OptionPayload.v) send inj₁ of a channel at ι[0] or inj₂ ∗ on !((S⁰@self[0]) ⊕ ∗).Close. The heads of a sum include both arms, so `none` owes ι ≺ ι[0] and the creation constraint of `some` (sharp edges 140).
- The box type □(∀ιs. C. T) is one type former (`TBox`, types/Types.v), so ∀ occurs only directly under □. Part 2 of docs/extensions/existentials.md had split it into □ and ∀ with E-Gen and E-Inst. No program used the two rules, and the split was undone (sharp edges 109). The rules beyond `orders-lr` are E-Pack and E-Open.

## Other documents

- `docs/ORDERS-SPEC.md` is the design specification. Section numbers in the code refer to it.
- `docs/SHARP-EDGES.md` is the decision log. Comments of the form "sharp edges N" point to entry N.
- `docs/TOUR.md` is a guided tour of the system with examples, rules, the logical relation and the main statements.
- `docs/extensions/` holds the extensions and the adequacy studies, `docs/history/` the design reviews.
- `paper/` holds the draft of the paper on this system.
