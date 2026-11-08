# Lock freedom: progress

Branch `lock-freedom`, off `liveness` at 3d9aef9. Plan: lock-freedom-plan.md.
Updated after every stage and every agent result.

| Stage | Status | Rocq files / theorems | make | Admitted | Open problems |
|---|---|---|---|---|---|
| 0  Paper proof (criterion, fuel and rank from the fragment) | done (0a, 0b) | none | n/a | n/a | decisions 1 to 4 of the plan await the author |
| 1  Fair semantics, lock_free, local_progress, lf_criterion | done (f99a2bd) | theories/lockfree/Instr.v (istep_erase, preduction_lift, pred_star_lift), Fair.v (wfair, lock_free, lock_free_reach), TauThread.v (thread_acc), LocalProgress.v (local_progress_ready), Criterion.v (lf_criterion) | passes | 0, no axioms | see log: LPrel alone does not give local progress; linearity facts must come from typing; links still channel steps |
| 2a Link τ costs 0 (relation, guard, liveness proofs, TauThread) | done on the liveness side (31c95da), lockfree widening folded into 2b-core | LiveRelation.v (PALink, LElink, Q-Link), Guard.v (KLink out), LiveGuard.v, LiveBind.v, Internalize, LiveConnect.v (lsteps_link), P-Term | passes | 0, no axioms | thread_acc needs the premise "every link redex has a restricted end" |
| 2b-core Constant world in the core (base and live relation, typing without KTNewEx, examples retyped) | done (de6e13c..6540027) | Typing.v (created), Fundamental.v (created_world, soundness_created), base and live relation (O-New at a known point, Q-Admin and process τ keep W), TauThread.v (links_restricted) | passes, 255 closed | 0, no axioms | SegmentInterleave not retyped (needs a stronger TreeSum box type, author); paper cites t_new_open and si_deadlock_free |
| 2b Rank and fuel in the relation (well-founded W, fuel constant N, per-thread invariant) | running on branch lf-fuel | | | | per-thread invariant needed (stage 1 finding 1) |
| 3a Fragment checks R1, R2′, R4′, wf_world, lfptyped (branch lf-rules) | done (4d74f15, merge into lock-freedom after 2a) | theories/lockfree/Fragment.v: lfptyped, lfsource, fw_lfptyped, tc_lfptyped, sch_lfsource, kob/c1/c3 rejections, tsum_r1_fails | passes, 267 closed | 0, no axioms | Rank on W catches chains only under the constant world; R4′ needs a typing annotation |
| 3  Fundamental theorem, lf_soundness, thread_progress, examples | not started | | | | |
| 3c Coverage of the literature (plan §12) | done (cc300ce on lf-rules) | Fragment.v (lf_r2r, starve_not_lfptyped, rc_lfptyped, abp_lfsource, rg_lfsource, wgen_rank_wf), examples/ABP.v, examples/GrowRing.v | passes | 0, no axioms | none. The ring gap is closed | | | | author's acceptance criterion |
| 4  Paper section | not started | | | | |

## Log

- 2026-11-08. Branch created. Plan moved here from the liveness worktree.
  Stages 0 and 1 started in parallel. Stage 1 changes no existing definition.
- 2026-11-08. The first stage 0 agent was cut off by a content filter partway
  through and delivered nothing. Stage 0 is restarted in three smaller parts:
  0a (fuel, rank and the criterion proof), 0b (rules R1 to R4 and the oracle),
  0c (example verdicts). 0a is running.

- 2026-11-08. Stage 0a done: paper proof of lf_criterion, measure (rank,
  fuel, admin depth). Four corrections to the plan (plan §6.1), among them a
  link loop that refreshes fuel, closed by the decision that links cost 0.
  Open: the proof argues classically (plan §6.3). Third uniformity option
  recorded, the constant world (plan §6.4).

- 2026-11-08. Revision approved by the author (relayed): fuel ticks only
  while the partner end is offered (plan §7). The static fragment keeps R2.
  The controller program must type by a direct semantic proof.

- 2026-11-08. Stage 1 done. lf_criterion is closed under the global context,
  constructive (fairness with deadlines, no axiom). Findings:
  (1) `∀ n, LPrel n W ∅ T p` alone does not give local progress. The closed
  process ({a, c}, {recv a, ping c, pong c}) satisfies the relation at every n
  because it never becomes stable, yet recv a waits forever. The false
  statement sits in theories/lockfree/open/LocalProgressLR.v, outside the
  build. Stage 2 must therefore keep a per-thread invariant (each thread's
  gate at its own Θ, one holder per entry, partner entries at dual points),
  as the fundamental theorem's derivation has it, and not rely on the closed
  P relation alone.
  (2) fuel_bound carries two linearity clauses (unique holder, enabled
  pending threads stay enabled) that typing has to supply.
  (3) Links are still channel steps in padmin, admin_at and tR. With link
  cost 0 these widen in TauThread.v and the admin predicate.
  (4) lock_free_reach (Padovani's Def. II.1) is defined, not yet related.

- 2026-11-08. Stage 0b done (plan §10). R3 and its alternative fail (C1, C1′).
  R4 rejects the Forwarder. A link loop with a chatter step defeats R2 (C3).
  Revised: R1, R2′ (with a link clause), R4′ (acyclic forwarding graph), and
  Rank as well-foundedness of W. Rank needs no number, and fuel is one
  constant N per program. Constant world adopted for the lock-free relation
  only. Core adoption goes to the author (three box types get stronger).

- 2026-11-08. Stage 3a done on lf-rules. R1 is strict tail position
  (syntactic). R2′ checks that ends passed to recursion or link are fresh in
  the round. R4′ is backed by a typing annotation, because terms carry no
  types. Finding: in the current calculus the descending chains of C1 and
  KobForwarder sit in box constraints and creation hypotheses, not in W, so
  `wf_world W` alone accepts C1. Rank catches them only under the constant
  world, where those facts become facts of W. This makes the constant world
  essential for stage 2b, not optional.

- 2026-11-08. Stage 3c analysis done (plan §13). All lock-free examples of
  Padovani 2013/2014, PVV14 and Kobayashi 2002 are covered or outside the
  calculus, except the growing ring III.7. Decision: relax R2′ to R2-recv
  with fed slots (fragment check only). Ring, ReceivedChain and the ABP to
  be checked in Rocq. Example (10) of padovani2014deadlock was mislabelled
  in an older store fact, now separated.

- 2026-11-08. Stage 2a done on the liveness side. No approved statement
  changed. Widening the lockfree admin step to links makes thread_acc false
  in the untyped semantics (a thread links a channel it already closed,
  forever). Decision under delegation: lf_criterion gains the premise that
  every link redex of a reachable configuration has a restricted end.
  Typing supplies it, as it supplies the linearity clauses of fuel_bound.
  lf_criterion is a theorem of this branch, not an approved statement.

- 2026-11-08. Stage 3c done in Rocq. The core types Padovani's growing ring
  (GrowRing.v) and the alternating bit protocol (ABP.v). Both pass the
  revised checks with R2-recv, and Rank holds by a pair rank. ReceivedChain is
  now in the fragment. The starving server fails exactly by the fed-slot
  clause. The fuel bound N = (d+1)·2L stays valid on paper. TreeSum fails
  R2-recv as well as R1, so R1′ alone would not admit it. CheckAll lists 396
  Print Assumptions, of which 109 are the commented-out translation entries.
  All 287 active ones are closed.

- 2026-11-09. Stage 2b-core done. The constant world is in the base and
  live relation. KTNewEx is gone, and top-level channels come from creation
  hypotheses (`created`, `soundness_created`). All composition statements
  and the soundness family keep their form. Lemmas that concluded
  `∃ W'` with `wext_fresh` now conclude at the same W. Boxes of FreshBetween,
  FreshMany, FactoryEx and GuardCex got stronger types. SegmentInterleave is
  out of the build: its channel needs facts against the point opened from
  TreeSum's result, which only a stronger TreeSum box type gives (author).
  lf-rules merged (1d0e977). The merge is clean in git but Fragment.v breaks,
  because its closed typings predate the creation hypotheses. A port runs on
  lock-freedom, stage 2b on branch lf-fuel.

- 2026-11-09. Fragment port to the constant world done. Rank is asked of
  `cworld Ψ`, the world where the run of a program over creation hypotheses
  Ψ starts. It places variable k at the constant k and has exactly the facts
  of Ψ, so creation facts are facts of W. `lfsource Ψ t T` takes
  `created (Wpo []) Ψ` and `wf_world (cworld Ψ)`, and `lfsource_lfptyped`
  turns it into `lfptyped (cworld Ψ)` with `cworld Ψ` strict. Forwarder,
  TailCall and ReceivedChain are stated as `∃ W, strict W ∧ lfptyped W …`.
  ABP is retyped over a ladder of rank constraints (θ, then ζ, υ, χ), the
  construction of the CFST scheduler made generic. GrowRing's C₀ is already
  a creation constraint. Every rejection keeps its statement, and
  `kob_cworld_not_wf` shows that Rank rejects the world of Kobayashi's
  forwarder itself. CheckAll lists 404 Print Assumptions, 293 active, all
  closed.

## Decisions

- 2026-11-08, author. Links: the link τ costs 0, so link loops count as
  τ-divergence (plan decision 3). Part of stage 2.
- 2026-11-08, author. SemRounds (G4) after lock freedom.
- 2026-11-08, author. Uniformity (oracle or annotations in types): open,
  the author asked whether the oracle keeps compositionality.

- Open for the author: an axiom of classical logic, or constructive fairness
  with deadlines (plan §6.3).
- Open for the author: the constant world (plan §6.4) as the preferred
  uniformity option.

- 2026-11-08, author. The constant world goes into the core, not only the
  lock-free fragment. FactoryEx, FreshBetween and FreshMany get stronger box
  types.
- 2026-11-08, author. skip-drop and skip-drop-release deleted on GitHub.
  Local tags archive/skip-drop and archive/skip-drop-release keep them.

## Related work hooks

- padovani2014deadlock p2 and p7. Tickets bound delegation and natural
  priorities give the well-founded order. Lock freedom requires both (p7).
  Fuel and rank are their counterparts.
- padovani2014deadlock p15, Def. B.8. The measure is priority, tickets and
  depth. lf_criterion uses rank, fuel and admin depth.
- padovani2014deadlock p8. The lock-freedom proof inducts on a measure of
  priority and tickets. lf_criterion inducts on (rank, fuel).
- balzer2023logical p13. An observation index stays constant under internal
  steps. The live relation does the same with cost-0 internal steps.
- namakonov2026lawyer p2. Step-indexing "is inherently at odds with liveness
  reasoning". The uniformity problem (plan §2, G1) is this conflict, met for
  lock freedom. The choice oracle is our way around it.
- lee2025lilo p1. Stratified propositions replace step-indexing for liveness.
  An alternative to the oracle, not pursued.
