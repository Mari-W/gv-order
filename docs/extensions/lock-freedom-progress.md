# Lock freedom: progress

Branch `lock-freedom`, off `liveness` at 3d9aef9. Plan: lock-freedom-plan.md.
Updated after every stage and every agent result.

| Stage | Status | Rocq files / theorems | make | Admitted | Open problems |
|---|---|---|---|---|---|
| 0  Paper proof (criterion, fuel and rank from the fragment) | 0a done, 0b next | none | n/a | n/a | decisions 1 to 4 of the plan await the author |
| 1  Fair semantics, lock_free, local_progress, lf_criterion | in progress | to come | not run | 0 | none yet |
| 2  Budgeted live relation with oracle | not started, waits for the author | | | | changes composition statements by ω |
| 3  Static fragment, fundamental theorem, lf_soundness | not started | | | | |
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
