# Design check, per-end capture (entry 12)

Overnight run of 2026-11-20, branch redesign-clean3 after entry 6 (credits
only on ends and closures). Write-up only, no Rocq change. The argument below
is on paper and was not checked in Rocq.

## Verdict

It holds, and it removes the floor h. Capture becomes aging. The body of a
closure at credit a sees `Θ − a` and `Δ − a`, each end at its own credit minus
a. FV-Arrow asks the counters at call time to be at least the counters at
creation minus a. With that, E-SpawnLam is E-Abs at a = 1 followed by
E-Spawn as far as credits go, and the loss example of entry 12 (A at N and B
at 1, handed to a child that acts on B while it holds A) keeps A at N − 1.
What still separates E-SpawnLam from E-Abs is the pair of points of the arrow
(the lower point and the future of the body), which is the generalized arrow
of entry 12 and not part of this check.

## Why it is sound

- Today FV at `(T ⊸[c ; ϑ ; h] U)^a` asks the counters φ at creation at least
  `h + a` and accepts at call time any φ′ on the same ends with every counter
  at least h (fuel/Fuel.v, `Vty`). The proposal drops h, asks φ at least a on
  the ends that are not idle, and accepts any φ′ with `φ′(o) ≥ φ(o) − a`.
- Aging keeps the bound. `age_arr` turns a into `a − c` for `c ≤ a`, and
  `Vty_age` turns φ into `φ − c`. For `c ≤ a ≤ φ(o)` the difference
  `(φ(o) − c) − (a − c)` is `φ(o) − a`. A hand-over moves the value with one
  unit less on every counter and ages its type by 1, the same computation.
- E-Abs in the cost semantics (`cost_e_abs`, cost/CostRules.v) needs the body
  environment at the call counters. At creation `thfuel` gives
  `φ(o) ≥ cr(Θ(o))`, so `φ′(o) ≥ φ(o) − a ≥ cr(Θ(o)) − a`, which is the
  credit of `Θ − a`. The values of Δ come from `Vty_age` at `φ − a` and from
  monotonicity in the counters (`Vfuel_mono`) at φ′. An idle end ages by
  truncation, and `fsub` is monotone, so the same bound holds for it.
- Sub-Arr no longer compares floors. `(T ⊸ U)^a ≤ (T ⊸ U)^{a'}` needs
  `a' ≤ a`, because the body was typed for `cr − a` and FV at a′ promises
  only counters at least `φ − a'`.
- Capturing a closure inside a closure is aging the inner closure by a, so
  Cap-Arr goes as well.

## Rule and lemma changes if the author takes it

- types/Types.v. `TLolli` loses the floor h.
- static/Contexts.v. `tcap`, `lcap`, `thcap` go. Sub-Arr becomes
  `fle a' a` with the cost, transformer and argument and result conditions.
- static/Typing.v. E-Abs asks `thage a Θ Θh` and `lage a Δ Δh` where it asks
  `thcap h a` and `lcap h a`. E-SpawnLam stays until the arrow points of
  entry 12 are general.
- fuel/Fuel.v. FV-Arrow as above.
- fuel/FuelValues.v. `Vty_recount` and `Vfuel_recount` give way to
  `Vty_age` and `Vfuel_mono`.
- cost/CostSem.v. `gfuel_cap`, `envf_cap`, `thfuel_cap`, `Vty_cap_above`,
  `Vfuel_cap_above`, `gfuel_cap_above`, `thfuel_cap_above` and
  `envf_cap_above` go, and `cost_e_abs` uses `envf_age` and `envf_mono`.
- The other capture lemmas (`tcap_unl`, `tcap_unl_r`, `tcap_df`,
  `tcap_df_eq`, `lcap_df`, `lcap_df_eq`, `lcap_lsame`, `lcap_unl`,
  `lcap_nones`, `lcap_Forall2`, `lren_lcap`, `thcap_df`, `thcap_df_eq`,
  `thcap_dom`, `thcap_erase`, `thcap_lookup`) go or are replaced by their
  aging versions.
- static/Weakening.v, static/Renaming.v, static/PointSubst.v and the
  examples follow the shape of `TLolli`.
