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
- `ThreadSim.v`: threads related one to one and runs of β steps, shared by the simulations of pgv/ and pn/.
- `ChannelSwap.v`: transpositions of channel names commute with the LTS.
- `Harmony.v`: a reduction semantics for soups agrees with the LTS (`harmony`).

`types/`, the types.

- `Types.v`: types, session types, points, constraints, duality, environments.
- `SessionEquiv.v`: coinductive session equivalence ≈ and duality ⊥.
- `LinearEnv.v`: linear variable environments, splitting and weakening.

`relation/`, the logical relation.

- `Worlds.v`: worlds, their facts ≡ and ≺, extension and strictness.
- `Creation.v`: creation constraints. The closed form of T + C (`interp`), the world of new (`wext_cc`), transfer of `cc_ok` (`cc_ok_transfer`) and the model lemma (`cc_model`).
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
- `LitTools.v`: the shared tools of the examples taken from the literature. Program order over a gap, the gate tactics, the chain of carried roots `slotv` with the ascending order `ult` and its creation-constraint wrapper `cc_ok_ult`, and `tv_case`.
- `MilnerSched.v`: Milner's cyclic scheduler of Dardha and Gay, Example 1 in full with k = 3 agents and their collectors, every channel at a point of one root (`ms_deadlock_free`).
- `KobForwarder.v`: Kobayashi's recursive forwarder server, Example 2, as a recursive box whose fresh reply channel sits at the first carried root of the channel it answers on (`fw_deadlock_free_kob`).
- `FactServer.v`: the factorial server of Kobayashi and of Padovani, the same shape with the branch on the received value (`fc_deadlock_free`).
- `Stream.v`: Padovani's `stream`, a producer that sends a fresh continuation each round, with a consumer (`st_deadlock_free`).
- `Congruence.v`: a box whose derivation needs both congruences of ≡, one alias between base points read at a carried root and at the successor (`cg_deadlock_free`).
- `Rejected.v`: programs the static system rejects (`rr_call_underivable`, `sched_rev_underivable`, `ms_rev_underivable`, `badlink_underivable`, `ord_no_constraint`).

`counterexamples/`

- `DropCounter.v`: why the fresh point of E-Abs and E-Exp is a frame variable.

`pgv/`, adequacy for repaired Priority GV (docs/extensions/adequacy/pgv-adequacy.md).

- `PGVTypes.v`: PGV's priorities, types, duality, pr(·) and the monotone fragment `pgv_mono`.
- `PGVTyping.v`: the schemas and Fig. 2 on our terms with repairs R1 and R2 (`pgv_typed`, `pgv_frag`).
- `PGVWorld.v`: the protocol-point world `Wpgv`, its strictness and the translation of types.
- `PGVTranslate.v`: PGV derivations become `typed` derivations (`pgv_translate`, `pgv_deadlock_free`).
- `PGVSimulation.v`: the simulation of a program by its translation, and deadlock freedom of the program itself (`rel`, `fwd`, `final`, `pgv_deadlock_free_source`).
- `PGVExamples.v`: Example 2.1 of the paper, a delegation, a link, and the two counterexamples rejected.

`pn/`, adequacy for Padovani and Novara, FORTE 2015 (docs/extensions/adequacy/padovani-novara.md §7).

- `PNTypes.v`: levels, channel, arrow, recursive and wrapped types, the level |t| and the shift ⇑ⁿ.
- `PNTyping.v`: Table 2 with T-App-Poly on our terms, repaired fix, as a judgment that also yields the translated term (`pn_typed`).
- `PNWorld.v`: anchors and ranks into ℤ with a top element, the constraint `Crel` and its acyclicity (`Crel_acyclic`), and the translation of types.
- `PNTranslate.v`: derivations become `typed` derivations at every anchor and offset (`pn_translate`), a closed program becomes a term of the source judgment (`pn_translate_source`, `pn_deadlock_free`).
- `PNExamples.v`: parallel Fibonacci and the signal pipe, both deadlock free.
- `PNSemantics.v`: the reduction semantics of the chapter on the source syntax and Definition 1 (`src_pstep`, `pn_deadlock_free_src`), §8.
- `PNSimulation.v`: the simulation of the source by its translation and the theorem in the source semantics (`trel`, `fwd`, `pn_deadlock_free_source`).

## Main results

- `soundness` (static/Fundamental.v): a typed closed process at a strict world is deadlock free.
- `soundness_source` (static/Fundamental.v): a closed term of the source judgment under a top-level constraint C₀ over n point variables is deadlock free when C₀ is acyclic (`c0_acyclic`). Its premise is `styped ∅ [(C₀, ids n)] [] (∅, None) t T` and names no world. The proof types the term in `wnil` and starts the run in `wc0 n C₀`, the facts of C₀ at fresh constants (docs/extensions/existentials.md parts 6 and 7, sharp edges 110, 122).
- `styped` (static/Source.v): the judgment Δ ⊢^F_Γ t : T of static-system.md for a self-contained single-threaded source program, with Γ the hypotheses Ψ and the frame hypotheses Φ. Its type is `fhyps → hyps → lenv → sframe → expr → ty → Prop`, with no world and no channel environment. It mirrors every rule of `typed` for a form without channel constants and adds none. A world is a don't-care there, because a well-formed world relates two points only by program order or between two points of its support, every support name is a constant, and a source derivation names none (sharp edges 122). Program order is the rule `fl_po` of the fact theory (sharp edges 121). `styped_typed` sends a source derivation into `typed` at every world, `typed_styped` sends a derivation in a world of empty support back, and `styped_iff` is the equivalence (sharp edges 123). The whole-program typing lemma of every example states `styped`, and so does `pn_translate_source`. `typed` and `ptyped` keep their world for the process layer, and the PGV translation keeps `Wpgv`.
- `fundamental`, `fundamental_proc` (static/Fundamental.v): typed terms and processes are semantically typed.
- `adequacy` (relation/LogicalRelation.v): a semantically typed closed process is deadlock free.
- `Prel_term`, `Prel_indep` (composition/PTerm.v), `Prel_connect` (composition/PConnect.v), `Prel_connect_n` (composition/PConnectN.v), `Prel_internalize` (composition/Internalize.v).
- `Erel_bind` (rules/Bind.v).
- `pgv_deadlock_free` (pgv/PGVTranslate.v): the translation of a closed program of type 1 in the monotone fragment of repaired PGV is deadlock free, and by `pgv_deadlock_free_source` (pgv/PGVSimulation.v) so is the program itself. The examples of pgv/PGVExamples.v apply the latter.
- `pn_deadlock_free` (pn/PNTranslate.v): the translation of a closed program of type unit in fragment v1 of repaired Padovani and Novara is deadlock free. `fibo_deadlock_free` and `pipe_deadlock_free` (pn/PNExamples.v) apply it.
- `pn_deadlock_free_source` (pn/PNSimulation.v): such a program whose fixes are all fix λf.λx.e is deadlock free in the semantics of the chapter (Definition 1). `fibo_deadlock_free_src` and `pipe_deadlock_free_src` apply it.
- The examples: `sync_deadlock_free`, `cycle_deadlock_free`, `deleg_deadlock_free`, `sched_deadlock_free`, `fac_deadlock_free`, `fa_deadlock_free`, `rr_deadlock_free`, `rel_deadlock_free`, `tc_deadlock_free`, `ch_deadlock_free`, `fw_deadlock_free`, `fb_deadlock_free`, one per file in examples/.
- The examples from the literature, each typed as its paper writes it and each stated in the world-free `styped`: `ms_deadlock_free` (Milner's cyclic scheduler of Dardha and Gay, Example 1 in full), `fw_deadlock_free_kob` (Kobayashi's recursive forwarder server, Example 2), `fc_deadlock_free` (the factorial server of Kobayashi and of Padovani), `st_deadlock_free` (Padovani's `stream`). `cg_deadlock_free` is the first derivation that uses the congruences of ≡ (docs/extensions/literature-examples.md, sharp edges 130 to 136).
- E-NewFresh (`t_newfresh_open`, static/Typing.v) creates a channel at a fresh point ι with a constraint C that relates points of ι (ι+k, ι.i, …) to known points, when u ≺ v holds for every u ≺ p and q ≺ v of C with q at or after p in program order. `t_newfresh_lh_open` is the form L ≺ ι ≺ H. World extension is unchanged (docs/extensions/fresh-points.md, sharp edges 90 to 96). E-NewFresh is a lemma on the encoded term let p = new ∗ in let (x, y) = p in t (`let_new`), not a rule (sharp edges 103).
- Existential points ∃^ℓ ιs. C. T (`TEx`, types/Types.v) with E-Pack, E-Open and V-Ex, where the lower bound ℓ is ⊤, ⊥ or a point, and the signature new : ∗ ⊸^⊥_⊤ ∃^⊥ ι. C. S@ι ⊗ S̄@ι. C is any set of facts between points of ι and outer points, by ≺ and ≡, that is acyclic and conservative over the context (`cc_ok`, sharp edges 105 and 106). relation/Creation.v proves it sound (`interp`, `wext_cc`, `cc_ok_transfer`), and `cc_model` proves it for concrete constraints. `t_new_at` (static/Fundamental.v) gives new at a known point on the encoded let, and `t_new_open` (static/Typing.v) new under any creation constraint. Every example types in the empty world. Factory and the PN translation start under a top-level constraint C₀ (`soundness_source`). The PGV translation keeps its world `Wpgv`, because its payloads hold global points (sharp edges 107, 108, 110 to 112). W stays as a parameter of `typed` for configurations, and source programs type in the world-free `styped` (static/Source.v, sharp edges 122). A frame carries a flag for a held ∃^⊥, under which no call with an upper point passes the gate (docs/extensions/existentials.md, sharp edges 97 to 100 and 103).
- The box type □(∀ιs. C. T) is one type former (`TBox`, types/Types.v), so ∀ occurs only directly under □. Part 2 of docs/extensions/existentials.md had split it into □ and ∀ with E-Gen and E-Inst. No program used the two rules, and the split was undone (sharp edges 109). The rules beyond `orders-lr` are E-Pack and E-Open.

## Other documents

- `ORDERS-SPEC.md` is the design specification. Section numbers in the code refer to it.
- `SHARP-EDGES.md` is the decision log. Comments of the form "sharp edges N" point to entry N.
- `gvsharp-orders.lagda` is the literate description of the system.
- `docs/` holds the notes on decidability and the design reviews.
- `paper/` holds the paper of the system before the order-based port.
