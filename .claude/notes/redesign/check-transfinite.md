# Design check, transfinite step indices (Phase A2)

2026-11-21, branch redesign. Write-up only, no Rocq change. The argument is
on paper and was not checked in Rocq.

## Verdict

It works, and the price is classical logic. With the judgments read at every
ordinal of a universe above the space of creation choices, the existential
property holds, the creation choice of O-New is an ordinary `∃ S π C` inside
the relation, and χ and the `∃ N, a, χ` before `∀ n` go. One choice per
creation then holds along the whole run, by the argument of Lemma 2.2 of
Transfinite Iris. Three costs remain.

- The existential property is proved by contradiction, with excluded middle and
  a choice of one failing index per witness (spies2021transfinite, p12). The
  Coq model of Transfinite Iris assumes excluded middle and the axiom of choice,
  and the adequacy of Lantana depends on seven classical axioms (lantana2027,
  README). v2 is closed under the global context today.
- Turning one choice per step into a sequence of states along a run still needs
  dependent choice, the obstacle of entry 4.
- The port touches the one fixpoint, five definitions and the level arithmetic
  of 43 files.

If the author accepts the existential property and dependent choice as explicit
hypotheses of the lock-free adequacy theorem (the form already decided for
entry 4), the design holds. If not, χ stays, and it is constructive.

## 1. The index

The judgments hold at every ordinal, `∀ α : Ord`, the validity `|=` of
Transfinite Iris. The lock-free judgment reads

    Σ ⊪_W p : T  :=  ∀ α. ∃ a. erase(s_q a) = p ∧ a ∈ S^W_α⟦Σ ⊢ T⟧

and the existential property turns it into `∃ a. ∀ α. …`, the form of today
(F20), as a lemma instead of a definition. Along a run the argument is the one
of Lemma 2.2 of Transfinite Iris (p5). From `∀ α. a ∈ S_α` and a step of cost
c, the step lemma at `α + c` gives, for every α, a choice x with the next state
`a_x ∈ S_α`. The family `α ↦ a_x ∈ S_α` is down-closed, so the existential
property gives one x with `a_x ∈ S_α` for every α. The next state is again
valid, and the next step repeats the argument. Every creation choice is made
once and holds at every level and for the rest of the run.

A fixed index fails. After one step from a limit λ the continuation holds at
every β < λ, and one choice for all β < λ needs the cofinality of λ to exceed
the number of choices (the supremum argument of Theorem 6.2, p12). At λ = ω
this is false for any infinite choice space, which is risk (a) of entry 2 and
the example `∃ n. ⊲ⁿ⊥` of Transfinite Iris (p5). Birkedal, Bizjak and
Schwinghammer index their must-relation over ω1 because countable choice makes
must-convergence close at ω1 and not at ω (birkedal2013stepindexed, p2, p14).
ω1 would suffice here only for a countable choice space. Ours contains the
constraint C, and a world fact is a predicate `w_facts : fact → Prop`
(types/Worlds.v), so the space is not countable. The ordinals must therefore
take suprema over every type of the universe that holds worlds, as the
Kirst–Smolka ordinals of the Transfinite Iris mechanization do (p12).

## 2. Steps at a limit and the least fixpoint

A step of cost c at level α obliges the continuation at every β with
`β + c ≤ α`, where `β + c` is the c-fold successor.

    at_cost_E α c El X W Θ T F e  :=  (c = 0 → X W Θ T F e) ∧ (c ≠ 0 → ∀ β. β + c ≤ α → El β W Θ T F e)

At a successor `α = γ + c` this is level γ, by down-closure. At a limit λ it is
every β < λ, for every c ≥ 1, the later of Transfinite Iris,
`(⊲P) α = ∀ β < α. P β` (p12). The synchronization of cost 2 needs no extra
case. Varr already states its body this way, `j + c_beta κ ≤ n`
(relation/Relation.v), and keeps the form with the ordinal order. FuelE reads
its obligations at the predecessor n′ of `S n′` (`mk_flevel`, fuel/Fuel.v), and
reads them at every β < α instead.

Cost-0 steps keep their least fixpoint. `Eind` and `Pind` at level α are the
inductive predicates over the cost-0 steps of level α, and every step of
positive cost leaves them for the family below α. A limit is not special for
them. In κ_L a creation costs 0, so O-New sits inside `Eind` at α itself,
`∃ S π C. X_α(…)`. The existential property applies to it as well, because E is
down-closed in the level.

The fixpoint becomes well-founded recursion on the ordinal order. `mk_level`
reads `below j` only at j < n, so no contractiveness is needed, and the
unfolding is stated up to pointwise `↔`, as `FuelE_S` does today with
`Fdef_ext`, so no functional extensionality enters. The uniform families of
Birkedal, Bizjak and Schwinghammer, `R_λ = ⋂_{β<λ} R_β` at limits, are the same
construction (p7).

## 3. The rules Transfinite Iris loses

Transfinite Iris loses `⊲(∃ x. Φ x) ⊢ ∃ x. ⊲ Φ x` and `⊲(P ∗ Q) ⊢ ⊲P ∗ ⊲Q`
(p13). With finite indices both hold at every level, because every positive
level is a successor. Our analogues are an existential witness and a split of
the environment Θ that a proof produces at level α. Every obligation of v2
states them outside the shifted level.

- `o_new` and `o_new_at` read `∃ S. at_cost_E n c …`, `f_new` reads
  `∃ S. El n′ …`.
- `o_spawn` and `o_send` split Θ by `∃ ΘM Θr` before `at_cost_E`, and `f_send`
  splits by `mres` and `mrem` of the moved ends.

At a limit these are the strong forms `∃ x. ⊲ Φ x`. A proof uses a lost rule
exactly when it rebuilds such a witness at α from witnesses at the levels below
α alone. In v2 a witness comes from one of two sources.

- A typing derivation, in both fundamental theorems and the cost fundamental
  theorem. The witness is the derivation's, the same at every level.
- A hypothesis at the same level α. This is the case in Bind and Blind (compat/),
  in closure under fusion and renaming (`Pbody_mapX`, Relabel), in
  `sem_p_connect` (the step of one component carries its own witness), in
  monotonicity in the level and in the world, and in `live_sub_df_n`
  (compat/LiveDF.v), which reads validity of the live relation.

I found no lemma that needs either lost rule. The one place where witnesses of
different levels meet is the lock-free process relation along a run
(`step_new`, `step_new_at` in soup/SoupStep.v, `lfsoup_step_all` in
soup/SoupRun.v), and there the existential property replaces the universal root
and χ. The limit cases of the 28 `induction n` and 46 `destruct n` sites are
where a counterexample would show up, and each must be checked when it is
ported.

## 4. The cost in Rocq

- Ordinals. Lantana vendors coq-ordinal 0.5.6 (about 9.7k lines with
  cardinals, Zorn's lemma and Hessenberg sums), uses two copies of it against a
  universe inconsistency, and builds on Transfinite Iris (lantana2027, PAPER.md).
  v2 needs much less, an ordinal type with `≤`, a well-founded `<`, successor,
  suprema of families over a small type, and finite addition. Brouwer trees
  give these constructively in a few hundred lines. The existential property
  takes excluded middle and a choice of indices on top.
- Universes. A creation choice contains a world, which contains Prop-valued
  facts, so it lives in a universe u, and the ordinals must take suprema over
  u and live above it. v2 is not universe-polymorphic. Lantana's two copies show
  that this check can fail and must be tried first.
- The fixpoint. relation/Sfix.v (34 lines) becomes recursion on `Acc` of the
  ordinal order with a setoid unfolding, about 150 lines.
- Definitions. `at_cost_V`, `at_cost_E`, `at_cost_P`, `Varr`, `Vthunk`, `Etop`,
  `Ptop`, `Rel` (relation/Relation.v), `mk_flevel`, `Fdef`, `FLev`
  (fuel/Fuel.v), the index of `Soup` (soup/Soup.v) and `lf_sem`.
- Proofs. 405 lines with level arithmetic in 43 files (compat/ 20, soup/ 7,
  fuel/ 5, relation/ 4, cost/ 3, examples/ 2, types/ 2). `lia` closes none of
  their level goals any more. Each becomes an ordinal lemma (transitivity,
  monotonicity of `+ c`, `β + c ≤ α → β < α`), and every unfolding lemma at a
  successor (`FuelE_S`, the uses of `sfix_unfold`) gains a limit form.
- Adequacy. `lfsoup_step_all` uses the existential property. `lfsoup_run`
  needs the sequence of states, by dependent choice as a hypothesis or by a
  relational statement of the criterion. The deadlock-freedom adequacy reads
  finite levels, which validity over the ordinals contains.
- Axioms. Both hypotheses appear in `Print Assumptions` of the lock-free
  results unless they are stated as premises. The deadlock-freedom results
  need neither.

## 5. Finite indices and the fixed annotated configuration

The fixed annotated configuration can go as a definition. The state a lives in
a small type (a configuration, the finite map K, and today the function `s_tk`),
so `∀ α. ∃ a. …` implies `∃ a. ∀ α. …` by the existential property, and the
state can be an ordinary existential of the relation at each level. It comes
back as a lemma once per step, and the run still needs the sequence of those
states, which is dependent choice.

Finite indices are not what adequacy needs. Lock-free adequacy reads the
relation at level 1 at each position (`ak_inv k 1`, soup/LFAdequacy.v), and
deadlock-freedom adequacy reads a level above the length of a run prefix. Both
are finite levels, contained in validity over the ordinals. The two relations
are instances of one generic R^κ over one fixpoint, so they move to ordinals
together.

## Plain `new` on top (entry 2)

In the deadlock-free relation the creation choice is free. O-New at κ_DF (cost
1) reads

    c fresh ⇒ ∀ a ∉ A_W. ∃ S π C. π ∈ {a} ∪ {x·κ | x a point of Θ} ∧ strict(W ⊕ C) ∧
              ∀ β. β + 1 ≤ α → e′ ∈ E^{W⊕C}_β⟦Θ[c⁺ ↦ S@π, c⁻ ↦ S̄@π̄] ⊢ T⟧

and deadlock-freedom adequacy needs no choice fixed across levels, because it
checks one reachable state at a time. This part works with finite indices
as well.

The lock-free relation states the same O-New at κ_L, inside `Eind` at α, and
constrains it. The annotated configuration gains the world of the run and the
points of the new ends, `lf_next` becomes a relation that takes the choice, and
the existential property fixes `(S, π, C)` once per creation, as in section 1.
What the constraint is stays the open question of entry 2, risk (b). Each world
of a run is strict, and the criterion (lockfree/Criterion.v) needs one
well-founded order on ranks for the whole run, that is, a well-founded union of
the worlds along it. Ordinal indices suggest a constraint. The creation choice
also picks an ordinal rank for each new point, such that every fact of the grown
world between ranked points goes up in rank. The existential property fixes the
ranks once, the union of the worlds of a run is then ranked and well-founded,
and the criterion ranks a pending thread by the ordinal of its end. rx-chain
needs an infinite descending sequence of ranks and is rejected. The static side
must then show that the constraints E-New allows admit such ranks, and the
client-server constraint `ι+k ≺ (κ+k)‾` must be tested against it. That test is
not done here.

## Literature used

- spies2021transfinite. The existential property and its proof (p12), the
  later at an ordinal (p12), the dependence of witnesses on finite indices and
  Lemma 2.2 (p5), the lost commuting rules and Theorem 7.1 (p13), the classical
  axioms of the model (p12).
- birkedal2013stepindexed. Uniform families over an ordinal and their fixed
  points (p7), must-convergence closing at ω1 under countable choice (p2, p14).
- lantana2027. The ordinal library, its two copies and the existential
  property instance (PAPER.md), the seven axioms of adequacy (README).
