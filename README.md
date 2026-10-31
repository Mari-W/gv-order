# Deadlock freedom for GV♯ with an order-based logical relation

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
- `ChannelSwap.v`: transpositions of channel names commute with the LTS.
- `Harmony.v`: a reduction semantics for soups agrees with the LTS (`harmony`).

`types/`, the types.

- `Types.v`: types with boxes over points and session variables and existential points, context-free session types (Skip, ;, !P, ?P, ⊕, &, Close, μ), their head normal form `unfoldS` (unr), points, constraints, duality, environments.
- `SessionEquiv.v`: bisimilarity ≈ on heads, the laws of ; and μ, and duality ⊥.
- `LinearEnv.v`: linear variable environments, splitting and weakening.

`relation/`, the logical relation.

- `Worlds.v`: worlds, their facts ≡ and ≺, extension and strictness.
- `Readiness.v`: readiness of terms (with a frame) and of processes.
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
- `BoxRules.v`: the rules that need the box, E-App, E-Force, E-Exp and E-Contract, and E-Pack and E-Open for existential points.
- `SemanticRules.v`: the infinitary judgment of these rules and its fundamental theorem.

`static/`, the static system (spec §9).

- `FactTheory.v`: frames, box hypotheses and the judgments Γ ⊢ x ≡ y and Γ ⊢ a ≺ b.
- `PointSubst.v`: substitution of points and the transport of facts along it.
- `Typing.v`: the typing judgments `typed` and `ptyped`.
- `Fundamental.v`: `fundamental`, `fundamental_proc` and `soundness`.

`examples/`, the examples of spec §13.

- `ExampleTools.v`: strict worlds from ranks, derived rules and tactics.
- `Sync.v`, `Cycle.v`, `Delegation.v`, `Scheduler.v`: first-order examples.
- `Factory.v`: the factory at one point and under □∀ι.
- `RequestReply.v`, `Relay.v`, `TailCall.v`, `ReceivedChain.v`, `Forwarder.v`: recursive boxes with infinite constraints.
- `Ordered.v`: a box whose constraint orders its two arguments.
- `Rejected.v`: programs the static system rejects (`rr_call_underivable`).
- `SendTreeType.v`: the type of sendTree with the coarse ceiling over walks, a smoke test (SHARP-EDGES 73, 76).

`examples/cfst/`, the examples of context-free session types (SHARP-EDGES 74, 75 and 76). Since K10 a choice moves its channel to a branch root x◁i, and ceilings range over the walks from a point.

- `CfstTools.v`: hereditary contractiveness by depth, congruences of ≈, case and E-Open for Θ = ∅, facts of constraints with outer points, the lockstep world.
- `TreeCopy.v`: recvTree as `drain` and sendTree after recvTree as `copy`, both with polymorphic recursion and existential points, run on a fixed tree (`tree_deadlock_free`).
- `Stream.v`: the two streams of Mordido and Pérez in a cycle (`st_deadlock_free`).
- `CfstDeadlock.v`: their classic deadlock is not deadlock free and so has no typing at any strict world (`dl_untypable`). Its repair types (`dlfix_deadlock_free`).
- `CfstScheduler.v`: Milner's cyclic scheduler with three schedulers and three workers (`sch_deadlock_free`).
- `TreeSum.v`: treeSum of Thiemann and Vasconcelos (Listing 2) with the reply after both subtrees, serving the client transform on a fixed tree (`ts_deadlock_free`).
- `ArithServer.v`: their arithmetic expression server (Listing 3) with binary choices and its fixed client (`as_deadlock_free`).
- `BranchOrder.v`: a branch that orders two channels against the other branch, typable with branch roots and not under K5 (`bo_deadlock_free`, SHARP-EDGES 76).

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

`counterexamples/`

- `DropCounter.v`: why the fresh point of E-Abs and E-Exp is a frame variable.

On branch `cfst` (context-free session types, SHARP-EDGES 72 and 73) `pgv/` and `pn/` stay in the tree but are not part of the build.

`pgv/`, adequacy for repaired Priority GV (docs/extensions/adequacy/pgv-adequacy.md).

- `PGVTypes.v`: PGV's priorities, types, duality, pr(·) and the monotone fragment `pgv_mono`.
- `PGVTyping.v`: the schemas and Fig. 2 on our terms with repairs R1 and R2 (`pgv_typed`, `pgv_frag`).
- `PGVWorld.v`: the protocol-point world `Wpgv`, its strictness and the translation of types.
- `PGVTranslate.v`: PGV derivations become `typed` derivations (`pgv_translate`, `pgv_deadlock_free`).
- `PGVExamples.v`: Example 2.1 of the paper, a delegation, a link, and the two counterexamples rejected.

`pn/`, adequacy for Padovani and Novara, FORTE 2015 (docs/extensions/adequacy/padovani-novara.md §7).

- `PNTypes.v`: levels, channel, arrow, recursive and wrapped types, the level |t| and the shift ⇑ⁿ.
- `PNTyping.v`: Table 2 with T-App-Poly on our terms, repaired fix, as a judgment that also yields the translated term (`pn_typed`).
- `PNWorld.v`: the level world `Wpn` of anchors and ranks into ℤ with a top element, its strictness and the translation of types.
- `PNTranslate.v`: derivations become `typed` derivations at every anchor and offset (`pn_translate`, `pn_deadlock_free`).
- `PNExamples.v`: parallel Fibonacci and the signal pipe, both deadlock free.
- `PNSemantics.v`: the reduction semantics of the chapter on the source syntax and Definition 1 (`src_pstep`, `pn_deadlock_free_src`), §8.
- `PNSimulation.v`: the simulation of the source by its translation and the theorem in the source semantics (`trel`, `fwd`, `pn_deadlock_free_source`).

## Main results

- `soundness` (static/Fundamental.v): a typed closed process at a strict world is deadlock free.
- `fundamental`, `fundamental_proc` (static/Fundamental.v): typed terms and processes are semantically typed.
- `adequacy` (relation/LogicalRelation.v): a semantically typed closed process is deadlock free.
- `Prel_term`, `Prel_indep` (composition/PTerm.v), `Prel_connect` (composition/PConnect.v), `Prel_connect_n` (composition/PConnectN.v), `Prel_internalize` (composition/Internalize.v).
- `Erel_bind` (rules/Bind.v).
- `pgv_deadlock_free` (pgv/PGVTranslate.v): a closed program of type 1 in the monotone fragment of repaired PGV is deadlock free.
- `pn_deadlock_free` (pn/PNTranslate.v): the translation of a closed program of type unit in fragment v1 of repaired Padovani and Novara is deadlock free. `fibo_deadlock_free` and `pipe_deadlock_free` (pn/PNExamples.v) apply it.
- `pn_deadlock_free_source` (pn/PNSimulation.v): such a program whose fixes are all fix λf.λx.e is deadlock free in the semantics of the chapter (Definition 1). `fibo_deadlock_free_src` and `pipe_deadlock_free_src` apply it.
- The examples: `sync_deadlock_free`, `cycle_deadlock_free`, `deleg_deadlock_free`, `sched_deadlock_free`, `fac_deadlock_free`, `fa_deadlock_free`, `rr_deadlock_free`, `rel_deadlock_free`, `tc_deadlock_free`, `ch_deadlock_free`, `fw_deadlock_free`, one per file in examples/. On branch `cfst` also `tree_deadlock_free`, `st_deadlock_free`, `dlfix_deadlock_free`, `sch_deadlock_free`, `ts_deadlock_free`, `as_deadlock_free`, `bo_deadlock_free` and `dl_untypable` in examples/cfst/.

## Other documents

- `ORDERS-SPEC.md` is the design specification. Section numbers in the code refer to it.
- `SHARP-EDGES.md` is the decision log. Comments of the form "sharp edges N" point to entry N.
- `gvsharp-orders.lagda` is the literate description of the system.
- `docs/` holds the notes on decidability and the design reviews.
- `paper/` holds the paper of the system before the order-based port.
