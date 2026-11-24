# Switching main to the redesign, 2026-11-24

Approved by the author on 2026-11-24. Main carries the redesign from now on.
The old main stays reachable as branch old-main.

Before the switch main had 107 commits not in redesign. `git log --cherry-mark`
finds 91 of them patch-identical on redesign. The redesign line carried the
old development further (branch lock-freedom), so it already holds every Rocq
commit of main, 6 of them rebased with a changed patch. The 9 commits of
branch no-eq-paper are the only work of main that redesign lacked. Redesign
added no file that main changed after the paper commits, except
docs/extensions/no-equality.md.

| Group | Commits on main | On redesign before the switch | Verdict for v2 |
|---|---|---|---|
| End points, Rocq core (polarity on points, partner heads, dual worlds, readiness, invariance, Internalize, composition, term rules, fact theory, Typing, Fundamental) | a72798e to f3ae55b, 3ba2150 | patch-identical, theories/ | superseded. v2 names the two ends c⁺ and c⁻ (lang/Syntax.v), has the dual point x‾ (types/Points.v) and one readiness entry per end (relation/Readiness.v) |
| End points, examples and tools (ExampleTools, LitTools, cfst, lit, choice, semantic, the bit program, DropCounter, gen-checkall) | f141319 to ceb968a except the two below | patch-identical, theories/ | old development. v2 has its own example set. The examples v2 lacks are an open item below |
| End points, PGV, PN and MP translations, algorithmic checker | 8bd6eca, ed31bc2, b058143, f04cf05 | patch-identical, theories/ | v2 lacks them. Open item. The proposal keeps the translations out until S5 (§6, Appendix B #57), and the algorithmic system has its own plan (algorithmic-plan.md) |
| End points, paper and docs (static system, worlds, appendix, priorities, ORDERS-SPEC, README, extensions index, sharp edge 154) | 3809643 to dace89e | patch-identical, ORDERS-SPEC later amended on redesign | old development. Redesign's text is newer, kept |
| P-Join | 5767250 | patch-identical | superseded. P-Connect with an empty cut composes two components side by side (v2/compat/Connect.v, `sem_p_connect` in v2/compat/ConnectP.v) |
| No equality, Rocq and docs (no alias in Forwarder, Congruence, FirstAction, link at dual points, new_place, KTNewAt, facts and worlds without ≡, sharp edge 159) | a0c0e3b to efe2b73 | patch-identical, later replaced by the constant world (sharp edge 172) | superseded. v2 worlds `(A, ≺_A, L, Λ)` carry no ≡ (types/Worlds.v) |
| No equality, paper (x⁺ᵏ, new@x, link at dual points, worlds (N, ≺), the forwarder with an existential payload, fields σ.κ, binder ξ) | 7540e4b to 0a7091e (9 commits) | absent. Redesign's paper/ equals main's at 7540e4b~1 | taken from main. paper/ is main's text, a pure extension of redesign's. The paragraph on the paper in docs/extensions/no-equality.md is main's. The paper still describes the old system. Its rewrite for v2 is planned on branch redesign-paper |
| Liveness, live relation (costs, τ layer, unfolding, adequacy, conversion, constants, term rules, bind lemma) | c40f9c2 to 4e4dee4 | patch-identical, then link cost 0, constant world and syntactic points on the lock-freedom line | superseded by the one relation R^κ at κ_L (v2/relation/CostTable.v, Relation.v), `live_adequacy` (relation/Adequacy.v) and `live_soundness` (static/FundamentalProc.v) |
| Liveness, guard (Guard, GuardMarks, LiveGuard, LiveGuardRules, LiveGuardFund) and counterexamples (LiveKob, GuardCex) | 489836d to 21b13e2 | patch-identical | superseded. v2 dropped the guard (F3 of fable-findings.md). A force costs one unit in κ_L, so `live_soundness` gives `no_free_divergence` (lockfree/TauThread.v) where the old guarded theorem gave `no_tau_divergence`. The counterexamples are entries #12, #14 and #15 of proposal Appendix B. v2/examples/GuardEx.v records their verdicts without the guard (`div_box_typed`, `pn_fix_typed`, `cx_box_typed`, `spawn_loop_rejected`) |
| Liveness, composition (LiveRenaming, LiveJunk, LiveFuse, LiveEconv, LiveInternalize, LiveConnect, LivePConnect, LivePTerm, LiveGuardProc, liveness §11, sharp edge 170) | b1926fe to 653e623 | present, 6 commits rebased (b1926fe, 4259124, cdb59d0, df080d7, 47ec123, 653e623), then carried further | superseded by the generic compatibility lemmas at every cost table (v2/compat, `sem_p_connect`, `sem_p_term`) and `live_soundness` |

Files where main and redesign differ outside v2 and docs/redesign.
Redesign's text is newer in every one but paper/ and the one paragraph of
no-equality.md. Main's versions of CheckAll.v, _CoqProject, .gitignore,
scripts/gen-checkall.py, docs/ORDERS-SPEC.md, docs/SHARP-EDGES.md,
docs/extensions/liveness.md and theories/ predate the lock-freedom line and
stay reachable on old-main. Redesign's lock-freedom docs
(docs/extensions/lock-freedom-*.md) and theories/lockfree stay.

## Open items

1. PGV, PN and MP translations into v2. Main and redesign hold them in
   theories/pgv, theories/pn and theories/mp, out of the old build since the
   syntactic points (sharp edge 173).
2. Old examples v2 lacks. The bit program (examples/EndPoints.v), the
   forwarder with an existential payload (Forwarder.v), Congruence, the cfst
   examples (FirstAction, TreeCopy, TreeSum, CfstScheduler), DataBranch,
   ReceivedChain, Milner's scheduler and the literature examples
   (examples/lit). Each is a typing check in v2 or a rejection to add to
   Appendix B.
3. The algorithmic checker of theories/algorithmic. Its v2 successor is the
   bidirectional system of algorithmic-plan.md.

## Ported

paper/ and the paper paragraph of docs/extensions/no-equality.md. No v2 file
changed.
