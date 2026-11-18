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
| static/Typing.v | the merged judgment `typed` (rules `e_*`), its DF projection `dftyped` (rules `d_*`), process typing `ptyped` (`p_term` with `pfree Σ`, `p_connect`, `p_join`), `ptyped_pfree`, `ptyped_chans` |
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

## Stage S6, fuel

One step-indexed predicate per thread, `e ∈ F^N _ n⟦σ ▷ c ; r⟧(Π, φ, tk)`,
and its value part `v ∈ FV^N _ n⟦σ⟧(Π, φ)` by the credited type σ. Π
maps the held ends to their session types (the session-type part of the
relation's environment), φ to their counters, tk counts link tickets.
N is the one refill, and deadlock freedom is the instance N = ∞. Fuel
reads no point, no world and no relation. Every step costs one level.

| File | Content |
|---|---|
| fuel/Fuel.v | maps of ends, idle ends, the index-free update (`refill`, `fhand`, `cnew`), the obligations `f_*` named after F-Beta to F-Link, `Vty` by the type, `FuelE` and `Vfuel` through `sfix`, the notations, the unfolding equations |
| fuel/FuelMono.v | the clauses at index n + 1 (F-Wait, F-Tick, the hand-over, counter 0), downward closure, `FuelE_mono` in the refill, the counters, the frame, the tickets and the reserve, `FuelE_rename` |
| fuel/FuelValues.v | `Vfuel_rename`, `FuelE_val` (F2), `FuelE_beta` (F3), `Vfuel_recount` along the capture Θ^h and `Vfuel_age` along aging Γ − c (F5), values from their parts and `Vfuel_pinst` (F6), `FuelE_res_mono`, `FuelE_thread` |
| fuel/FuelBind.v | `FuelE_bind` (F1) and `link_tickets_fall` |
| fuel/FuelSub.v | `Vfuel_teq`, `Vfuel_sub`, `FuelE_sub` along the subtyping of the merged judgment |
| test/FuelNotations.v | the S6 notations |
## Stage S4, generic compatibility

| File | Content |
|---|---|
| types/Duality.v | duality commutes with unfolding (`dual_unfoldS`), ≈ is a congruence for `dual` (`sequiv_dual`), ported |
| compat/Bind.v | `Erel_sends`, readiness under a frame, the bind lemma `Erel_bind` for every cost table |
| compat/Blind.v | heads of session types up to ≈ (`seqv_unfold_*`), V, E and P agree at types whose erasures are ≈ (`Vrel_teq`, `Erel_teq_ty`, `Prel_teq`), the blindness lemma `Vrel_blind`, `Erel_blind` |
| compat/SemTyped.v | groundings `Grel`, the judgment at a set of points `sem_typed_at`, static futures `sf_den`, `Θ ; Δ ⊨^F _ W t : T` and `Θ ; Δ ⊫^F _ W t : T` (`sem_typed κ`) |
| compat/Redex.v | exact ends and heads of values (`Vrel_exact`, `Vrel_heads`), the β redexes and the redex of every operator (`Erel_send` … `Erel_force`, `Erel_new`) |
| compat/Rules.v | the operator rules over every cost table (`gen_e_*`) and their instances `sem_e_*`, `live_e_*` |
| compat/LiveDF.v | `live_sub_df`: ∅ ⊫_W p : T ⟹ ∅ ⊨_W p : T at a first-order T |
| compat/Swap.v | the transposition of channel names on environments (`sswap`) and readiness |
| compat/Rename.v | decision Q16: V and E under every map of ends injective on the held ends (`Vrel_rename`, `Erel_rename`), P by projection of its clause (fuse) (`Prel_fuse`), a composite of fusions is a fusion (`fuse_ok_compose`), renaming (`Prel_rename`, D = ∅) and Internalize (`Prel_internalize`, h = id) as instances, the transpositions as instances (`Vrel_swap`, `Erel_swap`), the link substitution as a renaming of the other component (`pren_ok_csub`) |
| compat/PSwap.v | the transposition on configurations with thread ids and on events (`istep_qswap`), the external clauses along it, P is invariant (`Prel_swap`, an instance of `Prel_rename`) |
| compat/Conv.v | environments up to ≈ (`senv_eqv`): V, E and P transport along them (`Vrel_conv`, `Erel_conv`, `Prel_conv`) |
| compat/Connect.v | P-Connect: environments of a cut (`cut_dual`, `conn`; `pfree` lives in static/Typing.v), the composite `pconn`, liftings, offers of the composite, the chain of cut ends (`finite_lt_acc`), readiness (`pc_ready`) and P-Stop (`pc_stop`) of the composite, `Prel_S_ind_fuse` |
| compat/ConnectSteps.v | P-Connect: the step clause of the composite, one lemma per kind of step (`tau_l1`, `tau_l2`, `tau_close`, `tau_choice12`) |
| compat/ConnectP.v | P-Connect and P-Join (`conn_all`, `sem_p_connect`, `sem_p_join`) |
| compat/RenameInd.v | one unfolding of E under a renaming, for any reader closed under renaming (`Ebody_rename`), and the induction over the steps of cost 0 with its predicate closed under renaming (`Erel_S_ind_ren`) |
| compat/PTerm.v | P-Term: the environments of a single thread (`sth`), its steps (`istep_single`), the split at a spawn (`spawn_split`), a fusion (`sth_fuse`), the environments after Q-Send, Q-Recv and a link of a restricted channel (`snd_sth`, `rcv_sth`, `lk_res`), the clauses (`core`), the spawned thread composed by P-Connect (`spawn_case`), `sem_p_term` |
| test/CompatNotations.v | the S4 notations |

## Stage S7, cost half of the merged judgment

`Θ ; Δ ⊨^N e : T^a ▷ c ; ϑ` (`csem`) holds when every grounded instance
of e is in FuelE at every refill above N, in the order `rle` (finite
refills by ≤, ∞ only above ∞). Θ is grounded by a renaming of its ends
(`thfuel`), Δ by values of `Vfuel` (`gfuel`). `cost_fundamental` proves
it for every derivation of the merged judgment, and `fsem_of_cost` turns
a closed thread into `fsem`. Decision Q15 makes every value of `Vfuel`
exact (`Vfuel_exact`).

| File | Content |
|---|---|
| cost/Transformers.v | `seq_sound` with offset ∞ |
| cost/Exact.v | `typed_tfacts`, the ends and free variables of a typed term, `fends_subst_eq` |
| cost/Forwarder.v | the forwarder of S7.1, `dead_thunk_rejected` under Q15, `fw_typed` |
| cost/CostSem.v | `thfuel`, `gfuel`, `envf`, `csem` and their structural lemmas, `envf_exact` |
| cost/CostBind.v | `csem_bind0`, `csem_bind1`, `csem_bind2` on top of `FuelE_bind` |
| cost/CostRedex.v | FuelE of the application of a closure and of every operator |
| cost/CostRules.v | one lemma `cost_e_*` per typing rule |
| cost/CostFund.v | `cost_fundamental`, `fsem_of_cost`, `fw_fsem` |
| test/CostNotations.v | the S7 notation |

## Stage S5, static fundamental theorems

One induction on DF derivations instantiates the point variables of Γ
by σ and its future variables by ρ, in any world where the instantiated
hypotheses hold (`hsat`), and reads the ⊥ flag as any set B. Each case
is a `gen_e_*` rule. The live theorem runs the same induction with the
guard's marks: a marked variable is the self of a box, held by the
grounding only below the current level (`GrelL`, `sem_later`). O-Spawn
reads the thunk at the empty future with no lower or upper point
(`Vthunk`), which D-SpawnLam meets (`gen_e_spawn_lam`).

| File | Content |
|---|---|
| compat/EFacts.v | E is closed upwards in its future (`Erel_cover`) and monotone in its type above a world (`Erel_ty_mono`) |
| compat/TermRules.v | groundings at heads, ends and entries (`Grel_heads`, `Grel_fends`, `Grel_pick`), V along subtyping (`Vrel_tsub`), the structural rules `gen_e_unit` … `gen_e_pack`, E-Box at a positive cost of β, E-SpawnLam (`gen_e_spawn_lam`) |
| compat/BindActs.v | the bind lemma for a hole that acts before it returns (`Erel_bind_acts`) |
| compat/LiveRules.v | groundings with marks `GrelL`, `sem_later`, every rule with marks, the box that marks its self (`later_box`), frames that clear the marks (`later_bind_acts`) |
| static/Guard.v | `acts`, the guard `glive` and `guarded`, renaming of marks |
| static/Fundamental.v | `hsat`, instances under binders (`pclose`), `dftyped_sem`, `spawn_lam_valid`, `fundamental`, `fundamental_typed` |
| static/LiveFundamental.v | `dftyped_later`, `spawn_lam_later_valid`, `live_fundamental`, `live_fundamental_typed` |
| examples/GuardEx.v | the guard against Appendix B #12 to #15 and #40, and the C2 stage of B.1 #4 |
| static/FundamentalProc.v | the side conditions of P-Connect from the typing premises (`ptyped_conn`), one induction on `ptyped` for every cost table (`proc_gen`), `fundamental_proc`, `live_fundamental_proc` (every thread guarded, `pguarded`), `soundness`, `live_soundness`, `soundness_source` |

## Stage S8, the soup and adequacy

A soup state fixes the threads, the ownership K (holder, point and
counter of every held end) and the tickets outside the index. At each
index every thread is in E[live] at its part of an environment A and in
FuelE^N at its part of a protocol map Π, with the two ends of every
internal channel paired. The update `lf_next` reads only the event.
`lfsoup_step` goes from index n + 1 to n. The τ steps of a soup admit no
infinite run (`soup_no_tau_divergence`), so `⊪` is the soup alone
(Q12, decided 2026-11-18). `lf_adequacy` instantiates
`lf_run_criterion` with ownership as the dependency, the point in K as
the rank and the tickets and the partner's counter as the measure.

| File | Content |
|---|---|
| lockfree/Criterion.v | `lf_run_criterion`, ported to the runs of S1 |
| lockfree/ThreadProgress.v | `thread_progress` |
| soup/Idle.v | `idle_dual`: S′ ≈ dual S gives idle S ↔ idle S′ |
| soup/State.v | `hold`, `lfstate`, the parts `kth`, `ctrs`, `kres`, the clauses `soup_gen` |
| soup/Soup.v | `Soup`, `a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧`, `lf_sem`, `Σ ⊪_W p : T`, the update `own_next`, `tk_next`, `lf_next`, `lf_run_state` |
| soup/OwnFacts.v, SyncMaps.v, LinkMaps.v | lookups of the parts of a state and of every update, finite counters |
| soup/Sessions.v | dual session types and protocols along a step and at a link |
| soup/SoupStep.v, SoupSync.v, SoupLink.v | the soup along each kind of step |
| soup/SoupRun.v | `lfsoup_step`, `lfsoup_run`, `lfsoup_isteps` |
| soup/SoupTau.v | `Erel_tacc`, the multiset extension, `soup_no_tau_divergence` |
| soup/LFLocal.v | the facts of one soup: held ends, readiness, partners, ranks, restricted links, fitting redexes |
| soup/LFRunFacts.v, LFEvents.v | steps of a run, the ends an event touches, tickets |
| soup/Relabel.v | the soup at every lifting (`relabel_map`, `soup_relabel`) |
| soup/LFAdequacy.v | local progress, rank, persistence, `lf_fuel`, `lf_adequacy_soup`, `lf_adequacy`, `lf_thread_progress` |
| test/SoupNotations.v | the S8 and S9 notations |

## Stage S9, lock-free composition and soundness

`Σ ⊪_W p : T` is the soup alone. A thread typed at a finite N gives a
soup through `fsem_of_cost` and `live_fundamental_typed`. Two soups over
the cut of P-Connect give a soup of the composite at W1 ⊔ W2 and the
larger refill: their union, then the restriction of the cut channels.
The judgment `Σ ⊩^N _ W p : T` has the rules of `⊢_W` with static
premises only. P-Term types the thread at Some N and asks `guarded t`
and `meets ϑ 0 tk`. `lf_fundamental` and `lf_soundness` follow by
induction on it.

| File | Content |
|---|---|
| soup/SoupCompose.v | `soup_par`, `soup_nu`, `soup_connect`, `soup_term` |
| soup/LFCompose.v | `soup_lift`, `lf_soup_connect`, `lf_p_connect`, `lf_p_join`, `lf_soup_term`, `typed_live`, `lf_p_term`, `lf_soundness_source` |
| soup/LFTyped.v | `lfptyped`, `Σ ⊩^N _ W p : T` with `p_term`, `p_connect`, `p_join`, `lf_fundamental`, `lf_soundness` |
| examples/LFClose.v | `lfworld_bare`, two threads closing one channel typed by P-Connect, `cl_lock_free` |
| examples/LFTools.v | `lfworld_measure`, `lfworld_lex3`, `lf_main`, boxes of one arrow at a finite N (`lbox`, `lbox_typed`, `lbox_force`), the rules over Θ = ∅ in derivation order |
| examples/LFCycle.v | cycle at N = 2, `cy_lock_free` |
| examples/LFFreshBetween.v | between at N = 2, `fb_lock_free` |
| examples/LFFreshMany.v | many at N = 4, `fm_lock_free` |
| examples/LFClientServer.v | the client and server loops at N = 3, `cs_lock_free` |
| examples/LFFactoryEx.v | the factory at N = 2, `fx_lock_free` |
| examples/LFGrowRing.v | the growing ring at N = 4 with payload credit 2 (`Schl`), `W_rg_wf`, `rg_lock_free` |
