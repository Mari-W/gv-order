# Design check, points as ordinal layers (Phase A3)

2026-11-21, branch redesign. Write-up only, no Rocq change. Every argument
here is on paper. The last section lists what was checked and what was not.

## Verdicts

1. Layers work, with one restriction on plain `new`. The world of a run
   becomes one rank assignment from points to ordinals, and `≺` reads `<`.
   The union of the worlds of a run is then well-founded by construction, so
   `wfworld` as a premise of adequacy, the families with their laws and risk
   (b) of entry 2 go. Two things stay. A creation at a fresh root fixes the
   ranks of the whole tree of points below that root, and a creation at a
   field picks nothing. The constraint C of a fresh root may relate the new
   points to context points only upwards (context below new), and E-New asks
   that C with program order be well-founded on the new tree. That premise is
   where `wfworld` survives, now per creation. It rejects rx-chain. The
   criterion ranks a pending thread by the ordinal of the point of the end it
   waits on.
2. The client-server program types. Its constraint has an infinite rising
   chain under one ceiling, `ι+k ≺ ζ` for every k, so it has no ranks in ℕ and
   ranks below ω³ in the ordinals. Every lock-free example types, with the
   measure its `W_*_wfworld` lemma already uses as the rank. Nothing failed,
   and no repair is needed.
3. Fuel extension removes N and does not remove K. Counters and caps become
   ordinals, an action refills to the cap, and a tick at a limit chooses a
   smaller ordinal (fixed once by the existential property). Statically a
   limit credit cannot be aged, it must first be lowered by subtyping, which
   is `oblP_fuel_extend` read as a typing rule. The invariant
   `tk(o) ⊕ tk(ō) ≤ K` and E-Link `a1 ⊕ m2 > K` carry over with the natural
   sum ⊕, because ⊕ cancels under `<` and ordinal `+` does not. K stays a
   bound. With caps ω on both ends, every program without links types at the
   one fixed bound `K = ω·2`. For programs with links I found no fixed K, and
   the weaker forms that hold are an ordinal K per judgment or the partner
   bound per end of check-links-without-tickets.md, which needs no K.
4. Nothing else in Lantana replaces a piece of ours at a price worth paying
   now. Obligations per action are our moving points already. The forest with
   free moves to the grandparent and the always/until guarantees would add
   structure without removing any.

## 1. Layers as the meaning of points

### The world

A semantic world is a finite set A of roots, each with a rank function on its
tree.

    W = (A, ϱ)      ϱ_a : tree(a) → Ord  for every a ∈ A
    tree(a)         every point whose name has root a: a, its shifts, its dual,
                    its fields at any depth, and their shifts and duals
    W ⊨ x ≺ y       iff  ϱ(x) < ϱ(y)
    W ⊑ W′          iff  A ⊆ A′ and ϱ′ agrees with ϱ on A

Program order is a property of each ϱ_a, `ϱ(x) < ϱ(x⁺)` and
`ϱ(x) < ϱ(x‾⁺)`, asked when the rank function is chosen. The order of a world
is transitive and well-founded because `<` on ordinals is. `strict`,
`wfworld`, `w_fams`, `w_laws`, `law_inst`, `pgen`, `wstep` and the
transitive closure leave the semantic side (types/Worlds.v). The static side
keeps symbolic points and facts. A static fact `x ≺ y` holds in W when
`ϱ(x) < ϱ(y)`, and a static context Γ holds in W when every hypothesis does.

A world only grows along a run, and no rank changes once chosen. The union of
the worlds of a run is therefore one rank assignment, and its order is
well-founded. This is risk (b) of entry 2, settled. The criterion needs one
well-founded order for the whole run (lockfree/Criterion.v, `HR`), and the
ordinals are that order.

### Why a field creation picks nothing

Ordinals are not dense. Between `α` and `α + 1` there is no ordinal, so a new
point cannot always be placed between two old points whose ranks were fixed
without foresight. The client-server program shows that this case is real. a
sits at ρ and b at the field ρ·0, and the facts interleave them,

    ρ+k ≺ (ρ·0+k)‾        ρ·0+k ≺ (ρ+k+1)‾.

If the creation of a ranked the points of ρ alone with `ϱ(ρ+k) = ϱ((ρ+k)‾) = k`,
the creation of b would need `ϱ(ρ·0+k+1)` strictly between `k+1` and `k+2`.
No ordinal exists there. The creation of a must leave room, and it can do so
only if it ranks the field points as well. So a creation at a fresh root
ranks its whole tree, fields included, and a later creation at a field `x·κ`
finds its ranks fixed. This is what families did with laws fixed for every
generated root up front, now per root and without families. The rank gaps
that a root creation leaves for its fields are the room for later insertions,
fixed in advance.

### Why a fresh root may sit only above context points

A fact `π ≺ y` from a new point to a context point asks `ϱ(π) < ϱ(y)`. The
relation reads a box body at every instance that satisfies the box
hypotheses, so y may have rank 0, and then no rank for π exists. The opposite
direction always works. For facts `y ≺ π` choose

    ϱ_a(x) = σ + ρ_C(x)      σ = sup { ϱ(y) + 1 | y a context point, y ≺ z ∈ C }

where `ρ_C` is a rank function of the order that C and program order generate
on tree(a). Then `ϱ(y) < σ ≤ ϱ_a(z)` for every fact from a context point, and
`σ + ·` is strictly monotone, so facts inside the tree hold. The supremum
ranges over a set of points, which is countable (`point_countable`,
types/Points.v), but the set is given by a predicate, so forming it is
classical. A rank function `ρ_C` exists exactly when that order is
well-founded. A strictly monotone map into the ordinals gives a well-founded
order, and every well-founded order has its rank function. So the premise
below is exact for the shape of C it admits.

### The changed rules

E-New, plain `new` as in entry 2 with the two restrictions.

    (ῑ, π) ∈ {(ρ, ρ)} ∪ {(ε, x·κ) | x a point of Γ}
    π = ρ    ⇒  every fact of C has a point in tree(ρ), every fact between
                tree(ρ) and a context point goes from the context point up,
                and C ∪ po is well-founded on tree(ρ)               (wf-new)
    π = x·κ  ⇒  Γ ⊢ C
    ───────────────────────────────────────────────────────────────── E-New
    Θ ; Γ ; Δ ⊢ new : ∃^⊥ ῑ. C. ((S@π)^N ⊗ (S̄@π̄)^N)

(wf-new) replaces `strict(Γ ∪ C)`. It is a premise about constraints and
reads no semantics. A field creation can carry no constraint of its own,
because every fact about `x·κ` was fixed with the root of x. The facts it
would add can be stated when the other roots involved are created, from below.

O-New, at κ_L inside `Eind` at level α.

    c fresh ⇒ ∀ a ∉ A_W. ∃ S π C ϱ_a.
        (π = a ∧ ϱ_a : tree(a) → Ord ∧ (W ⊕ (a, ϱ_a)) ⊨ C ∪ po)  ∨  (π = x·κ ∧ W ⊨ C)
        ∧ e′ ∈ E^{W ⊕ (a, ϱ_a)}_α⟦Θ[c⁺ ↦ S@π, c⁻ ↦ S̄@π̄] ⊢ T⟧

The existential property of transfinite indices (check-transfinite.md)
fixes `(S, π, C, ϱ_a)` once per creation and for every level. The annotated
configuration gains ϱ, and `lf_next` becomes a relation that takes the
choice. `knew` places the ends at a fresh root (fresh with respect to A, no
`kfresh` per family) or at the field.

The fundamental theorem for E-New builds `ϱ_a = σ + ρ_C` as above. It reads
no term and no syntax.

The lock-free criterion. `lf_run_criterion` keeps its statement. The
adequacy instance takes `E = Ord`, `R = <` and

    we k t = ϱ(kpt K o)      for the end o that t waits on.

`lf_stab` holds as today, because neither K nor ϱ changes the point or rank
of an end whose holder does not take part. `lf_rank` holds as today with
`ϱ(we k s) < ϱ(we k t)` in place of `W ⊢ we k s ≺ we k t`. The holder s of the
partner end at point `x‾` waits on o2 with readiness `pt(o2) ≺ (x‾)‾ = x`.
`lf_adequacy` loses its premises `strict W` and `wfworld W`.

Other premises that change.

- P-Connect compares two worlds at their shared roots. Strictness of the join
  (`strict_join_iff`) becomes well-foundedness of the amalgam at the shared
  roots, so that one rank function serves both sides. I have not checked this
  part beyond stating it.
- `ptyped_strict` becomes "every derivation sits over a static world whose
  facts admit ranks".
- The deadlock-free relation can read the same ranked worlds. It then
  inherits the two restrictions of E-New. It can also keep strict symbolic
  worlds with the free O-New of check-transfinite.md. The second gives up the
  single generic R^κ over one notion of world. The first loses no program that
  v2 types today (see section 2) and loses the plain-`new` programs with a
  fact from a new point down to a context point.

### rx-chain is rejected

rx-chain (docs/explorer/gen/rejects.js) creates c below the point of w, hands
`c′` to a child that runs the same body, and closes c while holding w.
Readiness asks `π ≺ ῑ` for the point ι of w. The child receives ι′ = π̄ and
asks `π′ ≺ π`, and so on. Every thread waits on the one it spawned.

- At a fresh root. C contains `π ≺ ῑ`, a fact from a new point down to a
  context point. E-New rejects it.
- At a field `ι·κ`. C must be entailed, so the box needs the hypothesis
  `ι·κ ≺ ῑ`, and its recursive call at `(ι·κ)‾` needs the same hypothesis one
  level down. main's root creation must then rank a tree that contains the
  descending chain `ρ‾ ≻ ρ·κ`, `ρ·κ ≻ ((ρ·κ)‾·κ)` and so on. C ∪ po is not
  well-founded on tree(ρ), and (wf-new) rejects main.
- Semantically. A body that must create below a point of rank α is in the
  relation at rank α only if its child is at some rank below α. At rank 0 no
  creation below exists. By well-founded induction on α the body is in the
  relation at no rank.

### Comparison with nonstrict_move.v

nonstrict_move.v weakens `obl_move` to allow a new parent whose witness layer
equals the payment layer. Its loop creates a fresh obligation at layer 0 with
fuel 2 in each round, moves the old one below it with its last unit, pays the
step with the new one, and recurses. Adequacy then proves False on the fair
run of the loop (`nonstrict_move_absurd`). Every round renews the fuel at the
same layer, so no measure decreases.

Two of our programs match it. rx-relink is the renewal. Each round the waiter
faces a fresh end with a full counter, and the tickets of
check-links-without-tickets.md reject it, as strict layers reject the renewal
in Lantana. rx-chain is the descent. It would go through if readiness asked
`x ≼ ȳ`, because then every new channel could sit at the rank of the previous
one, and the chain would never descend. The lesson of nonstrict_move.v
transfers. The comparison that orders waits must be strict. With ranks in the
ordinals and `≺` read as `<`, strictness is built in.

### Where this is Lantana's layers and where it differs

The same.

- A layer is an ordinal (`layer := ord.t`, lantana/algebra/layer.v), and so is
  a rank.
- A thread may wait only on something below what it holds. In Lantana the
  witness induction of an obligation at layer ℓ1 stores fuel only of
  obligations at layers `ℓ2 > ℓ1` (`wit_fuels_add`). Ours is readiness, acting
  on x while holding y needs `x ≺ ȳ`. Read the rank `ϱ(ȳ)` of the waiting
  partner as the layer of the obligation to act on y, and the two conditions
  coincide.
- A creation directly below a thread picks any layer (`parent_le` is True
  for a thread). A fresh root picks any ranks above its context points.

Different.

- Static points are symbolic. The type system never names an ordinal. A type
  states constraints, and the fundamental theorem picks ordinals from the
  well-foundedness of C. Lantana proofs name layers, for example `ℓ ⊕ 1` in
  the ticket lock.
- A channel has two ends, and each end is both a wait and an obligation. Each
  end has its own rank, and the ranks of x and `x‾` are unrelated except through
  program order `x ≺ x‾⁺`. Lantana obligations have one owner and no dual.
- Our obligations move up by themselves. An action moves an end from x to
  `x⁺` above x and `x‾`. In Lantana an obligation is discharged once, and the
  ticket lock allocates each round's obligation at the same layer ℓ of the
  lock and lets fuel and witness credits carry the rounds.
- Fields. A root ranks its whole tree in advance, and a field creation picks
  nothing. Lantana has no analogue, because each `obl_new` chooses its layer
  then.

## 2. The client-server test and the lock-free examples

The program is examples/ClientServer.v. main creates a at a fresh root ρ and
b at the field ρ·0, spawns `srv ⟨a′, b′⟩` and runs `cli ⟨a, b⟩`. Both boxes
have the type

    □∀ι κ ζ. C. ∗ ⊸ (S1@ι ⊗ S2@κ ⊸^ζ ∗)
    C = {ι+k ≺ (κ+k)‾, κ+k ≺ (ι+k+1)‾, ι+k ≺ ζ, κ+k ≺ ζ | k}

and each self call instantiates C at `(ι⁺, κ⁺, ζ)`. In plain `new` the first
creation carries `C = Λ_0(ρ)`, the laws `cs_L`, which state C at
`(ρ, ρ·0, ρ·1)` and at `(ρ‾, (ρ·0)‾, ρ·1)`. The second is a field creation
with no constraint.

Ranks. With `fsum`, `off` and `depth` as in v2/examples/LFTools.v,

    ϱ(x) = ω²·fsum(x) + ω·off(x) + depth(x)

gives `ϱ(ρ+k) = ϱ((ρ+k)‾) = ω·k`, `ϱ(ρ·0+k) = ϱ((ρ·0+k)‾) = ω·k + 1` and
`ϱ(ρ·1) = ω²`. Every fact holds.

    ι+k ≺ (κ+k)‾      ω·k < ω·k + 1
    κ+k ≺ (ι+k+1)‾    ω·k + 1 < ω·(k+1)
    ι+k ≺ ζ           ω·k < ω²
    κ+k ≺ ζ           ω·k + 1 < ω²
    x ≺ x⁺, x ≺ x‾⁺    the offset rises by one, fsum and depth stay

All facts point from a point of tree(ρ) to a point of tree(ρ), so (wf-new)
holds with σ = 0. The self call instantiates C at points of the same tree,
whose ranks satisfy it, and `hold_at` asks nothing new. The program types.

The ceiling ζ lies above `ι+k` for every k, and `ϱ(ι+k)` rises with k. No
natural number bounds an unbounded sequence of naturals, so ranks in ℕ fail
here and ordinals are necessary. The least ranks need only `ω + 1`
(`ϱ(ρ+k) = 2k`, `ϱ(ρ·0+k) = 2k + 1`, `ϱ(ρ·1) = ω`).

Every lock-free example. All their worlds have no constants and no facts, and
one family 0 at most (grep for `World ∅ (λ _, False)` in v2/examples). Each
family law has root `ι₀` only (`wf_laws`), so each translated root creation
carries a C inside the new tree, and each `new_κ o` becomes a field creation
with no constraint. Each `W_*_wfworld` lemma proves that a lexicographic
triple rises along every law at every generated root and along program order,
and a triple `(p, q, r)` maps to the ordinal `ω²·p + ω·q + r` with the same
order. That lemma is the (wf-new) premise of the root creation, with its
measure as the rank function.

| example | creations | rank |
|---|---|---|
| LFClose | none | `off` (`wfworld_bare`) |
| LFCycle | ρ, field ρ·0 | `(fsum, off, depth)` |
| LFFactoryEx | ρ in mk₀, field ρ·0 in mk₁ | `(fsum, depth, off)` |
| LFFreshBetween | ρ, fields ρ·1, ι·0 | `(fsum, off, depth)` |
| LFFreshMany | ρ, fields ρ·1, ι·0 | `(fsum, off, depth)` |
| LFClientServer | ρ, field ρ·0 | `(fsum, off, depth)` |
| LFController | ρ, fields ρ·0, ρ·2 | `(fsum, off, depth)` |
| LFGrowRing | ρ, fields X·1, Y·0 at every depth | `(depth, off)` |

All ranks lie below ω³. LFGrowRing ranks the whole infinite tree of its one
root in main, which is exactly what a field creation that picks nothing needs.
No example fails.

The same argument covers every program v2 types today. `wfworld W` of a v2
world gives a rank function on all its points, and its restriction to the tree
of each generated root ranks that root's creation. The loss is only against
the planned plain `new`, for a creation at a fresh root with a fact down to a
context point. Such a program must create at a field of the context point
instead, as FreshBetween does.

## 3. Fuel extension in place of a fixed N and K

### Lantana

`oblP_fuel_extend` trades one unit of fuel at layer ℓ2 for any fuel μ at a
layer `ℓ1 < ℓ2`. The measure `▽` at layer l is η of the join of all measures
at all layers below l (lantana/algebra/measure.v). So no amount is fixed up
front. The amount is chosen when the unit is spent.

### Our counters as ordinals

- Caps, credits and counters range over ordinals. A new end and an acted end
  start at the cap of the end.
- A tick or a hand-over lowers a counter by one at a successor and chooses a
  smaller ordinal at a limit. The choice is part of the state update, so
  `own_next` becomes a relation, and the existential property fixes the
  choice once per step, as it fixes creation choices.
- Statically, aging `a − c` is defined when `a = λ + n` with λ a limit or 0 and
  `c ≤ n`, and gives `λ + (n − c)`. A limit credit cannot be aged. The
  derivation first lowers it by subtyping (credits only go down,
  `sess_sub_credit`). This is `oblP_fuel_extend` as a typing rule, spending
  one unit of ω buys any finite credit.
- The measure of a pending thread is the counter of its partner end under `<`
  on ordinals. It drops at a tick from a limit, because the choice is below.
  `lf_run_criterion` asks a decidable order (`HRm_dec`), and `<` on ordinals
  is decidable only classically. Excluded middle is an allowed hypothesis of
  lock-free adequacy, so this costs nothing new.

The three rejected programs keep their verdicts.

- rx-postpone. The loop must pass b back at its parameter credit. A parameter
  credit ω must be lowered to a finite n before aging, and `n − c` is below ω.
- rx-delegate. A received payload has credit `a − 1` for the payload credit a
  of the protocol. At `a = λ + n` the resend asks `λ + n` and has `λ + n − 1`.
  At a limit a the receive is undefined, so the protocol cannot carry it.
- rx-relink. Below.

### Tickets, the bound and E-Link

The decided form is `tk(o) + tk(ō) ≤ K` with E-Link `a1 + m2 > K` and
`a2 + m1 > K`. With ordinals the sum must be the natural sum ⊕, which is
strictly monotone in each argument, so

    α ⊕ γ < β ⊕ γ   iff   α < β.

Ordinal `+` lacks this (`0 + ω = 1 + ω`). The link argument goes through.
`tk(o2‾) ⊕ m2 ≤ K < a1 ⊕ m2` gives `tk(o2‾) < a1`, so the waiter on `o1‾`
drops from a partner counter of at least a1 to one below a1. The invariant
holds for the new pair,

    tk(o1‾) ⊕ tk(o2‾) < tk(o1‾) ⊕ m1 ≤ K.

The partner bound `K − m` of the decided form is no longer a number. For
`K = ω` and `m = 1` every finite x satisfies `x ⊕ 1 ≤ K` and ω does not, so the
set has no largest element. The rules only use the invariant, so this loses
nothing.

Can K go? N already went with the caps, and K is the remaining bound.

- Without links, yes. Give both ends of every channel the cap ω. Then
  `ω ⊕ ω = ω·2`, and every program without links types at the one fixed bound
  `K = ω·2`. Each use site lowers ω to the finite credit it needs, and two
  components no longer agree on a number before P-Connect.
- With links, no fixed K was found. E-Link asks the strict excess
  `a1 ⊕ m2 > K`, so the linked ends need caps above what any channel splits
  between its two ends. At `K = ω·2` with all caps ω no link types. Caps above
  ω help in some cases, for example `m1 = m2 = ω + 1` with finite partners.
  The encoding `m ↦ ω + (m − K0/2)` of a finite derivation at bound K0 fails
  for a link with `m2 < K0/2 < a1`, because a finite part added to `ω + ·`
  never passes `ω·2`. I did not search further.
- Weaker forms that hold. (i) K an ordinal parameter of the judgment, chosen
  per program as N is today. (ii) K per end, which is the partner bound
  `(m, m̄)` of check-links-without-tickets.md read in ordinals. There E-Link
  asks `a1 > m̄2` and `a2 > m̄1`, uses no sum at all, and needs no K.

Refill on each action. The acted end is refilled to its cap, as decided. A
cap ω means the next finite budget is chosen at the first tick after the
action, fixed by the existential property.

The gain for closed programs is small. A finite derivation lowers ω at
finitely many sites, so the largest of those credits is a finite cap that
also types it. I know no closed program that types with ω caps and with no
finite caps. The gain is modular. With caps ω the refill is no longer a
number that every component must share.

## 4. What else in Lantana could replace a piece of ours

- Obligations per action. Lantana discharges an obligation once and
  allocates a new one each round (the ticket lock). Our end moving from x to
  `x⁺` with a refilled counter is already a new obligation per action, at a
  higher rank. Nothing to replace.
- Witness induction with refunds (`wit_fuels_add`, `wit_fuels_decr`). It
  pays for busy waiting. A waiting Lantana thread keeps stepping, and the
  fuel of its own obligations comes back once per witness credit. Our waiting
  thread is blocked and takes no step, so F-Tick charges it nothing. Not
  needed.
- The forest with moves (`obl_move`, `obl_move_up`). A move to a new parent
  pays one unit at a layer above the parent, and a move up to the grandparent
  is free. Our hand-over pays one unit (`khand`, minus one), which is
  `obl_move`. A free move up would need a parent map on ends in K, for example
  an end nested as a payload below the end that carries it, and a new
  invariant on counters along that map. It would make some forwarding free,
  and it puts rx-delegate at risk, which payload credit now rejects. Cost a
  new component of the state and its invariant. Not worth it now.
- Measures (`measure.v`). Sum, product, exponent and `▽` give a syntax for
  ordinal budgets. If credits become ordinals beyond `ω + n`, this syntax is
  the way to write them in types. Section 3 needs only `λ + n` with
  `λ ∈ {0, ω}` for programs without links. Adopt it only if ordinal K per end
  is taken.
- Always/until guarantees (the trace layer, `⊨ₜ`, `untilI`). They state
  liveness per program as a temporal formula over every fair behavior. Ours
  states lock freedom of a run (`lf_run`) and derives it by
  `lf_run_criterion`. The guarantees would let us state per-end response
  properties and the Padovani corollary (entry 5) in one framework. Cost a
  coinductive behavior type, a fairness counter and LTL connectives, which
  nothing in v2 has. Not needed for lock freedom.

## What was checked and what was not

Checked on paper.

- The rank construction `σ + ρ_C` for E-New and its exactness for the
  admitted shape of C.
- The client-server facts at the ranks `ω²·fsum + ω·off + depth`, and that ℕ
  admits no ranks for them.
- The examples, by reading each `W_*_wfworld` lemma and checking that its
  world has no constants and no facts.
- rx-chain at a fresh root, at a field and semantically.
- The link argument and the invariant with ⊕, rx-postpone and rx-delegate
  with limit credits.

Not checked.

- Anything in Rocq.
- P-Connect with ranked worlds, the amalgam condition at shared roots.
- The universe level of the rank functions. A rank assignment lives in a
  world, and the ordinals must take suprema over sets of points, which is the
  universe question of check-transfinite.md, section 4.
- Whether every finite derivation with links retypes at some fixed ordinal K.
- The fundamental theorem cases other than E-New, which I expect to change
  only by reading facts through ϱ.

## Literature used

- lantana2027. `obl_new`, `parent_le` and `parent_below` (True below a
  thread), `obl_move`, `obl_move_up`, `oblP_fuel_extend`, `oblP_fuel_mon_gen`,
  `oblP_fuel_add`, `wit_fuels_add` and `wit_fuels_decr`
  (lantana/program_logic/obl_forest.v), layers as `ord.t` with Hessenberg
  notations (lantana/algebra/layer.v), the measure syntax and `▽`
  (lantana/algebra/measure.v), the non-strict move and its loop
  (lantana_heap_lang/examples/nonstrict_move.v), layers in the ticket lock
  (lantana_heap_lang/examples/ticket_lock.v).
- spies2021transfinite, through check-transfinite.md, for the existential
  property that fixes each choice once.
