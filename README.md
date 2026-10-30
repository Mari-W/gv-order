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

- `Syntax.v`: terms with de Bruijn variables and channel names.
- `Semantics.v`: the labelled term semantics and the process LTS.
- `Safety.v`: deadlock freedom and the other process properties, and progress.
- `ChannelSwap.v`: transpositions of channel names commute with the LTS.
- `Harmony.v`: a reduction semantics for soups agrees with the LTS (`harmony`).

`types/`, the types.

- `Types.v`: types, session types, points, constraints, duality, environments.
- `SessionEquiv.v`: coinductive session equivalence ≈ and duality ⊥.
- `LinearEnv.v`: linear variable environments, splitting and weakening.

`relation/`, the logical relation.

- `Worlds.v`: worlds, their facts ≡ and ≺, extension and strictness.
- `Readiness.v`: readiness of terms (with a frame) and of processes.
- `LogicalRelation.v`: V, E and P, semantic typing, and `adequacy`.

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

`counterexamples/`

- `DropCounter.v`: why the fresh point of E-Abs and E-Exp is a frame variable.

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

## Main results

- `soundness` (static/Fundamental.v): a typed closed process at a strict world is deadlock free.
- `fundamental`, `fundamental_proc` (static/Fundamental.v): typed terms and processes are semantically typed.
- `adequacy` (relation/LogicalRelation.v): a semantically typed closed process is deadlock free.
- `Prel_term`, `Prel_indep` (composition/PTerm.v), `Prel_connect` (composition/PConnect.v), `Prel_connect_n` (composition/PConnectN.v), `Prel_internalize` (composition/Internalize.v).
- `Erel_bind` (rules/Bind.v).
- `pgv_deadlock_free` (pgv/PGVTranslate.v): a closed program of type 1 in the monotone fragment of repaired PGV is deadlock free.
- `pn_deadlock_free` (pn/PNTranslate.v): the translation of a closed program of type unit in fragment v1 of repaired Padovani and Novara is deadlock free. `fibo_deadlock_free` and `pipe_deadlock_free` (pn/PNExamples.v) apply it.
- The examples: `sync_deadlock_free`, `cycle_deadlock_free`, `deleg_deadlock_free`, `sched_deadlock_free`, `fac_deadlock_free`, `fa_deadlock_free`, `rr_deadlock_free`, `rel_deadlock_free`, `tc_deadlock_free`, `ch_deadlock_free`, `fw_deadlock_free`, one per file in examples/.

## Other documents

- `ORDERS-SPEC.md` is the design specification. Section numbers in the code refer to it.
- `SHARP-EDGES.md` is the decision log. Comments of the form "sharp edges N" point to entry N.
- `gvsharp-orders.lagda` is the literate description of the system.
- `docs/` holds the notes on decidability and the design reviews.
- `paper/` holds the paper of the system before the order-based port.
