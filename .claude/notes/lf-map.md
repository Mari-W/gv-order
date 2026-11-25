# Lock-free part of the map, rewrite of 2026-11-25 (branch lf-map)

Only docs/explorer/map.json changed. No Rocq change, no page change. The
scripts that made the edit are `.claude/notes/lf-map-edit-{1,2,3,4}.py`. Run
them from the repo root with `python3 -I`. `check.sh` ends with 0 errors and
the same single warning as main (bare word "Connect" in p-typing).
`page-test.js` passes 15 of 15.

## Mirror and merge, what the Rocq says

Checked in theories/fuel/Fuel.v (`Fdef`, `Fobl`, `f_*`), relation/Relation.v
(`Ebody`, `Obl`, `o_*`) and soup/State.v, soup/Soup.v.

What holds exactly:
- `FuelE` has the clauses (stop) and (step) of `Erel` and no (ready).
- `Fobl` has one rule per label, and each rule changes the held ends as its
  `o_*` counterpart does. Spawn splits off the ends of the thunk. Send
  splits off the ends of the payload. Receive quantifies over incoming values
  with disjoint ends. Close removes the end. Select and branch move it. Link
  removes two dual ends. New adds two dual ends.
- Additions are counters, tickets, the frame `d` and `N`.

What differs, so "fuel is E without (ready), with counters" is not exact:
- Index. Every fuel step reads its successor at each `j < n`. `Erel` reads it
  at `β + c ≤ α` by the cost, and a free step stays at `α` through the least
  fixed point.
- No world. `FuelE` has no Kripke quantifier and reads no point.
- Closure under injective renamings (`kinj`, `renk`) inside `Fdef`.
- Value clause on `is_val`, where `Erel` uses `irred`. The child of a spawn
  needs `FuelE` of `v ()` as a thread, where O-Spawn needs `v` in `V`.
- `f_force` lowers every counter and the frame. `o_force` is a free or costed
  step like `o_beta`.

Merged judgment. Not presented. The Rocq proves no lemma that merges `Erel`
and `FuelE`. A single fixed point with a fuel component reads at a receive
only values in both `V` and `FV`, and it chooses one session type at a
creation where `o_new` and `f_new` choose one each (the head comment of
soup/Soup.v says no soup can take one from the other). The conjunction implies
such a fixed point, and the converse is unproved. The map keeps two
judgments, sets them side by side in fu-vs, and states the differences there
and in a deviation of kind `other`.

## Per block

- fu. Formula is (stop), (step), the abbreviation `e' at Φ' ! d'`, `Φ`, and
  `fsem`. The renaming quantifier is gone. `f ≤ m` is gone from `Φ`, because
  `FuelE` does not enforce it. `cs.csem` left the block.
  Deviations: simplified (renaming closure, `Fdef`, `kinj`, `renk`), notation
  (`at` abbreviates the premise of each `Fobl` rule).
- fu-obls. Rebuilt in the shape of e-obl. One shared block defines `act o`,
  `positive`, `Φ↓` and `idle`. Rules F-Beta, F-Spawn, F-New, F-Force, F-Send,
  F-Recv, F-Close, F-Link, F-Select, F-Branch with `Φ = Φ_M ⊎ Φ_r` splits,
  `Φ↓[o ↦ S^{m,m}]` for an action, `d ∸ 1` for the frame. F-Recv now reads
  `β < α` (it said `γ ≤ β`). F-Select and F-Branch are separate rules.
  Deviation: notation (`refill`, `fhand`, `mres`, `mrem`).
- fu-vs. Table rows: thread, end, value, step `e →ℓ e'` with the index each
  side reads, reducible term, worlds. Caption states the exact mirror claim.
  The row labelled "a step α" is gone. Deviation `other` on the merge.
- soup. Main line reads `W ⊑ W_a ∧ tfree T ∧ ∃ Δ : K, U. wa(a, Δ) ∧ ∀ t.
  q(t) = e ⇒ e ∈ E[κ_L]⟦Δ^E_t ⊢ U_t⟧ ∧ e ∈ F⟦Δ^F_t ⊢ thread ! ∞⟧`. `Δ` is
  one map `o ↦ (S_x, P^{f,m})` over `K`. The consistency conjuncts live in the
  note of `wa`. The `lf_next` row left the box (it is not part of the
  relation). Deviations: merged (`A`, `Π`, `ctrs` into `Δ`, exact by `sp_pts`
  and `sp_dom`), simplified (`wa` names the other eleven conjuncts of
  `soup_consistent`). New note `sp.delta`. Note `sp.own` is now `wa`, and it
  lists each conjunct, including the interface bound `⌊N/2⌋` from `khalf`,
  which the map did not state before.
- t-lf-wf. Row "ranked W, process typing at a finite bound asks a ranked
  world". Deviation simplified (`wok`, `wfit` case split).
- w-wf. LF line is `ranked W ⟺ world_wf W ∧ ∃ ϱ. x ≺_W y ⇒ ϱ(x) < ϱ(y)`
  (`swf` is `wf` of relation/Ranks.v, which is exactly this). `ok_N` is gone.
  Deviation renamed (`swf`).
- p-typing. LF premises of P-Term, P-Connect and P-Connect^n read
  `ranked`. Deviation simplified (`wok`). DF view unchanged.
- w-ext. LF rows read `ranked` (models, joins). Note w.R7 got a renamed
  deviation.
- r-new. `wf(≺^ρ_C)` hovered the world note. It now hovers a new note
  `new.wf` (well-foundedness of a relation, `well_founded` in `new_ok`).
- sr-ord. The existential property lost `EM ∧ FC`, its note has
  `assumes: [EM, FC]`.

## Theorems (coordinator request a, b)

Kept rows. th-chain: DF two rows, LF `lf_fundamental` and
`lf_sems_adequacy`. th-sound: `soundness`, `lf_soundness`. th-fund-proc:
`fundamental_proc`, `lf_fundamental`. th-adeq: `adequacy`, `adequacy_sw`,
`lf_adequacy`, `lf_sems_adequacy`. th-compose: three DF rows, `lf_p_term`,
`lf_p_connect`. th-terms: `fundamental`, `live_fundamental_ranked`,
`fsem_of_cost`. th-conserv unchanged.

Dropped rows, each named in one caption sentence. n-ary connect (DF and LF),
`soundness_source`, `lf_soundness_source`, `live_soundness`,
`lf_soundness_run`, `lf_soundness_padovani`, `live_fundamental_proc`,
`live_sub_df`, `lf_thread_progress`, `lf_tp_gen`, `lf_soup_term`,
`fundamental_typed`, `live_fundamental`, `live_fundamental_typed`, `wfit`,
`cost_fundamental`. Their notes and the notes only they used are deleted
(41 notes, plus `type.TEnv`). DF content changed here: the DF rows
connect-n and soundness-source left th-sound, and w-wf no longer lists
th-sound under usedIn.

Axioms are tags. No formula or signature carries EM, FC or DC. `assumes`:
th.lf-soundness [EM, FC], th.lf-fundamental [EM], th.lf-p-term [EM],
th.lf-adequacy [EM, FC] (the section context of LFAdequacy.v takes both, the
map did not show them before), th.lf-sems-adequacy [EM, FC],
th.live-fundamental-ranked [EM], ord.exprop [EM, FC]. Notes th.em, th.ac,
th.dc are deleted.

## Other fixes

- Thirteen note arguments said "tickets m ≥ f". `FuelE` does not enforce it,
  only the lock-free process relation does (`sp_cap`). Now "tickets m".
- fu.Phi got a simplified deviation, counters and tickets are `fuel`
  (ℕ ∪ {∞}) in the Rocq, finite in the lock-free process relation.
- Merged main twice (3e0f84f assumes support, 5ffbf46 type variables Z).
  The index letter β stays for lower indices, as e-rel on main uses it.

## Not touched

p-rel and the fusion notes. fv only through main's Z rename. t-lf-counters
and sj-all are unchanged, both already read ranked worlds and carry no
Rocq-only structure the request named.
