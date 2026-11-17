# v2, the rewrite of docs/redesign/proposal.md

v2 is a new Rocq library with the logical name `GV`. It rebuilds the
mechanization from the ground up after docs/redesign/proposal.md, stage by
stage (§6 of the proposal). The old development in theories/ stays as it is
and v2 imports nothing from it. docs/redesign/progress.md records the state
of every stage, the log and every deviation from the proposal.

## Build

```
eval $(opam env)
cd v2
make -j4        # the library, about 70 seconds
make test       # the notations print as written (test/*.expected)
make check      # every result in CheckAll.v is closed under the global context
```

Tested with Rocq 9.2 and stdpp 1.13. If Makefile.conf is missing, `make` regenerates
it from _CoqProject. If `make` stops with Error 139, run `ulimit -s 1000000`
and run `make` again. The root build of theories/ ignores v2.

## Stage S1, the language

| File | Content |
|---|---|
| test/Lexer.v | every judgment and token of Appendix A, parsed and printed over dummy carriers |
| lang/Syntax.v | ends `c⁺` `c⁻`, terms with saturated operators `Op k e` and `ENew ℓ`, the constants of GV as λ-values, substitution, the one renaming `emap` with `cmap` and the link substitution `csub` |
| lang/Notations.v | `c⁺`, `c⁻`, `o‾` (test/LangNotations.v checks them) |
| lang/Semantics.v | thread steps, the T-Act rules `t_act_*` and the frame rule `t_act_ctx`, labels with transfer sets |
| lang/Process.v | the one instrumented semantics `istep` (thread ids, events, rules `p_act_*`), its erasure `pstep`, the multiset view `pspec` |
| lang/Safety.v | `act`, `act_offer_sig` once, progress for terms and configurations, closedness preserved |
| lang/Harmony.v | a label-free reduction semantics and `harmony` |
| lang/ThreadSim.v | tools for simulations, with β runs, contexts and threads related one to one |
| lang/ChannelSwap.v | renamings of channel names and transpositions in thread and process steps |
| lockfree/Fair.v | runs, weak fairness, `lock_free`, `lock_free_reach`, waiting |
| lockfree/Reach.v | `lock_free_reach_of`, a fair scheduler |
| lockfree/TauThread.v | `no_tau_divergence` and its thread-wise form `thread_acc` |
| CheckAll.v | `Print Assumptions` of the main results of the stage |

## Stage S2, points, worlds and the typing judgment

| File | Content |
|---|---|
| types/Points.v | roots (constants, generated roots `NGen ℓ g`, variables), points with the shift `x⁺`, the field `x·κ` and the dual `x‾`, instantiation, renaming of generated roots, facts, box constraints |
| types/Worlds.v | worlds `(A, ≺_A, L, Λ)`, the order `W ⊢ x ≺ y`, `world_wf`, `strict`, `lfworld`, `⊑`, the join `⊔`, `wrestrict`, R7 `strict_join_iff`, renaming families apart |
| types/Costs.v | credits and costs in ℕ ∪ {∞}, ticket transformers with offsets in ℕ ∪ {∞} |
| types/Types.v | context-free session types and types with credits, costs, transformers and floors, duality, unfolding, ≈, the annotations of N = ∞ (`ty_df`) |
| types/Erasure.v | `ty_df` commutes with the type operations and preserves ≈ |
| static/Contexts.v | Θ, Γ, Δ, futures, the fact theory `slt`, aging, capture, subtyping |
| static/Typing.v | the merged judgment `typed` (rules `e_*`), its DF projection `dftyped` (rules `d_*`), process typing `ptyped` (`p_term`, `p_connect`, `p_join`) |
| static/Conservativity.v | `typed_dftyped`, `dftyped_typed`, `conservative` |
| static/Weakening.v | world extension, term-variable renaming and weakening |
| static/Renaming.v | channel renaming, renaming of families and generated roots |
| static/PointSubst.v | point substitution `typed_pinst` |
| examples/ | the S2 examples, typed in `dftyped` and lifted to N = ∞ |
| test/TypeNotations.v | the S2 notations, ends and points side by side |

## Stage S3, the generic relation R^κ

One step-indexed relation, parametric in a cost table κ, gives the
deadlock-freedom relation (`κ_DF`) and the live relation (`κ_L`, also
written `live`). A step of cost c at level n carries its obligation at
level n − c, and a step of cost 0 is read inside the least fixpoint of
the level.

| File | Content |
|---|---|
| relation/Sfix.v | `sfix`, the one course-of-values fixpoint on the step index |
| relation/CostTable.v | cost tables `ctable`, `κ_DF`, `κ_L`, the cost of a thread label (`tcost`) and of an event (`ev_cost`), levels |
| relation/Readiness.v | readiness `ready _ W(Θ ∣ F, t)` and `ready _ W(Σ, p)`, one entry per end |
| relation/Relation.v | `v ∈ V[κ]^W _ n⟦Θ ⊢ T⟧`, `e ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^F`, `p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧` (`V^W`, `E^W`, `P^W` for κ_DF), the obligations `o_*` and `q_*` named after the paper's clauses, induction principles and the characteristic equations |
| relation/Closure.v | values, monotonicity in the world, downward closure, antitonicity in the future |
| relation/Adequacy.v | `Σ ⊨_W p : T`, `Σ ⊫_W p : T`, `adequacy`, `live_adequacy` |
| test/RelationNotations.v | the S3 notations |

The environments of the relation are `senv`, an end mapped to a
session type at a point, with no credit (`tenv_erase` drops the credits
of a typing environment). The session types keep their annotations, so
the fuel layer of stage S6 reads each end's cost protocol off the
environment of the live relation at the same index.
