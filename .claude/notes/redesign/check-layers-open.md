# Design check, the open points of the layers write-up (A3, continued)

2026-11-21, branch redesign. Write-up only, no change to v2/. Every argument
is on paper, except one scratch Rocq file for the universe levels (section 4),
which compiles against the built v2. The last section lists what was checked
and what was not. The starting point is check-layers.md, whose notation this
file keeps. W is a static world (constants and facts), R a ranked world
`(A, ϱ)` with `ϱ : point → Ord` meaningful on the trees of the roots in A, and
`R ⊨ W` says that every fact of W holds under ϱ.

## Verdicts

1. The restriction on plain `new` is real. It does not come from the way the
   fundamental theorem picks ranks. It comes from the Kripke reading of boxes
   and of E, which read a body at every world that satisfies its hypotheses,
   together with the fact that every set of ordinals has a least element. No
   choice of rank shape (ω·α, gaps by the natural sum, any class of admissible
   ranked worlds) removes it, because room below every point would give an
   infinite descending sequence of ordinals. The condition is also not exact.
   A fact down to a context point is sound when Γ already supplies the room,
   and a static sufficient condition exists (wf-new⁺ below, a map from the new
   points below the context into points of Γ). O-New needs no change. I
   recommend keeping (wf-new) of check-layers.md and filing (wf-new⁺) until a
   program needs it. rx-chain stays rejected under both. A recursion that
   creates below its predecessor a bounded but data-dependent number of times
   is lock free and stays rejected under both.
2. P-Connect asks `wf (W1|S ⊔ W2|S)` for the shared roots S, in place of
   strictness, and P-Term asks `wf W` in place of `strict W`. The analogue of
   `strict_join_iff` holds with the same zone decomposition. A component
   exposes the derived order of its static world on the points of the shared
   roots and no ranks. The composite gets its ranking as the rank function of
   the join, and the semantic composition reads both components at one ranked
   world, so no two rankings are ever reconciled. The client-server program
   split into client and server passes. A two-root cycle is rejected. A
   world pair whose amalgam is strict but has an infinite descending chain is
   accepted by today's condition and rejected by the new one.
3. Every other case of the fundamental theorem goes through with ranks and
   changes only by reading facts through ϱ. E-Link, the actions, E-Spawn and
   field creations touch no rank, because every point an end can move to was
   ranked with its root. P-Term, P-Connect and the process relation lose
   their strictness premises. Subsumption, E-Pack, E-Open, E-Force and the
   readiness premises all rest on one new lemma, the soundness of static
   entailment in ranked worlds.
4. The levels work, with one universe-polymorphic Brouwer tree used at two
   levels instead of two copies of a library. Ranks are `Ord@{Set}`, with
   suprema over subtypes of `point`, which lives in `Set`. A ranked world then
   lives in `Type@{Set+1}`, the level of v2's `world` today. Step indices are
   `Ord@{s}` with `Set+1 ≤ s`, because they need suprema over creation choices,
   which contain ranked worlds. Rocq confirms both levels and rejects a rank
   ordinal with a supremum over choices. The rank function of a well-founded
   relation is constructive with these suprema.

## 1. The restriction on plain `new`

### It is real

Claim. Let 𝒲 be any class of ranked worlds that the relation quantifies over,
closed under the creations the fundamental theorem performs. If E-New may put
a fresh point π below a context point y with no hypothesis about y, then 𝒲 is
empty.

Proof. The rule must be sound at every world of 𝒲 and every instance of y,
because a box body is read at every `R′ ⊒ R` and every instance that satisfies
its hypotheses (`TBox` in `Vbody`, relation/Relation.v), and E is read at every
extension (`Ebody`). So every R ∈ 𝒲 and every point y with a rank in R has an
extension in 𝒲 with a point π, `ϱ(π) < ϱ(y)`. The new point π is again a
point of a world in 𝒲, and the rule applies to it. Starting from any R0 and
any y0 this gives `ϱ(y0) > ϱ(π1) > ϱ(π2) > …`, an infinite descending
sequence of ordinals. No such sequence exists. ∎

The proposed shapes fail at the first or second step of this argument.

- Ranks ω·α. The least of them is `ω·0 = 0`, and a box variable can be
  instantiated at a point of rank 0 (a root a with `ϱ(a‾) = 0` is a ranked
  world, a‾ has no program-order predecessor). Even from `ϱ(y) = ω·(α+1)` the
  new point gets a rank `ω·α + n`, which is not of the form ω·β, so the shape
  is not kept and the next creation below π has no room of its own. Keeping
  k levels of room needs `ω^k`, and an unbounded k is the descending sequence.
- Gaps by the natural sum. Ordinals have no infinitesimals. Any `ε > 0` has
  `α ⊕ ε ≥ α + 1`, so a gap is an ordinal and the claim applies unchanged.
- Room for infinitely many points below y is easy (ω finite ranks below ω).
  Room that every new point inherits is the descending sequence.

The trouble is not only rank 0. Between two context points the situation is
the same. If C asks `z ≺ π ≺ y`, a world with `ϱ(z) = α` and `ϱ(y) = α + 1`
satisfies Γ and has no rank for π.

The restriction belongs to ranked worlds. The deadlock-free relation over
symbolic strict worlds has none, because a strict order extended by an acyclic
set of new facts is again strict, so `strict(W ⊕ C)` always admits the new
point wherever C puts it.

### Not exact, and a static relaxation

The exact condition is "every ranked world that satisfies Γ has an extension
by ranks for tree(ρ) that satisfies C and program order". That statement
reads semantics, so it cannot be a typing premise. A static sufficient
condition copies ranks from points of Γ.

    D  =  the points of tree(ρ) that lie (C ∪ po)-below a point u
          with a fact u ≺ y ∈ C, y a context point
    U  =  tree(ρ) ∖ D

D is closed downwards in tree(ρ), so every fact between D and U goes from D to
U, and every program-order step `x ≺ x⁺`, `x ≺ x‾⁺` stays in D, goes from D to
U, or stays in U.

    π = ρ  ⇒  every fact of C has a point in tree(ρ), and there is a map
              h : D → points of Γ with
                Γ ⊢ h(u) ≺ h(v)   for every u ≺ v of C ∪ po inside D
                Γ ⊢ z ≺ h(u)      for every z ≺ u ∈ C, z a context point
                Γ ⊢ h(u) ≺ y      for every u ≺ y ∈ C, y a context point
              and C ∪ po is well-founded on tree(ρ)                  (wf-new⁺)

With D empty this is (wf-new) of check-layers.md. The fundamental theorem
builds the ranks at every `R ⊨ Γ`.

    ϱ_a(u) = ϱ(h(u))                                        u ∈ D
    ϱ_a(u) = sup ( { ϱ_a(v) + 1 | v ≺ u ∈ C ∪ po, v ∈ U }
                 ∪ { ϱ(z) + 1 | z ≺ u ∈ C ∪ po, z ∈ D or z a context point } )
                                                            u ∈ U

The second line is a definition by well-founded recursion on C ∪ po on U, a
supremum over a subtype of `point` (section 4). Facts inside D hold by the
first clause of h and the soundness of entailment, facts from the context into
D by the second, facts from D down to the context by the third. Every fact
into a point of U is below its supremum. Program order is covered by the
three cases above. So `R ⊕ (a, ϱ_a) ⊨ C ∪ po`.

Well-foundedness on D is not used by this construction (D maps strictly into
ranks of R), so the last line of (wf-new⁺) needs it on U only. I kept it on
the whole tree, which costs only boxes whose hypotheses no ranked world
satisfies.

h is not exact either. With `Γ ⊢ z ≺ y` and `Γ ⊢ z′ ≺ y′` and C asking
`π ≺ y` and `π ≺ y′`, no single point of Γ lies below both, yet `ϱ(π) = 0`
works in every world, because y and y′ each have a point below them. A
finer condition would compare heights in Γ with heights in C. I did not
pursue it.

### O-New is unchanged

O-New of check-layers.md already lets the creation choose any `ϱ_a` with
`(R ⊕ (a, ϱ_a)) ⊨ C ∪ po`, whatever direction the facts of C have. The
restriction lives in E-New alone, so changing (wf-new) to (wf-new⁺) changes no
relation clause.

    c fresh ⇒ ∀ a ∉ A_R. ∃ S π C ϱ_a.
        (π = a ∧ (R ⊕ (a, ϱ_a)) ⊨ C ∪ po)  ∨  (π = x·κ ∧ R ⊨ C)
        ∧ e′ ∈ E^{R ⊕ (a, ϱ_a)}_α⟦Θ[c⁺ ↦ S@π, c⁻ ↦ S̄@π̄] ⊢ T⟧

### rx-chain stays rejected

rx-chain (docs/explorer/gen/rejects.js) closes c at π while holding w at ι,
so C contains `π ≺ ῑ`, and the child runs the same body at `π̄`, whose partner
point is π.

- Under (wf-new). The fact goes down to a context point, rejected, as in
  check-layers.md.
- Under (wf-new⁺). h(π) must be a point of Γ below `ῑ`. ῑ has offset 0 and no
  program-order predecessor, so the box hypotheses H must supply one. The
  recursive call instantiates H at `π̄` and so needs a point below π. If it is
  a new point, it lies in D, and h maps it to a point of Γ below h(π). If H
  supplies a descending chain of length n below ῑ, the call needs a chain of
  length n inside D, and h needs length n + 1 in Γ. So H must state an infinite
  descending chain below ῑ. main instantiates the box at its own root ρ (or
  at an interface root), so the tree of ρ (or the static world) contains that
  chain, and C ∪ po is not well-founded there (or `wf W` of P-Term fails).
- Semantically. The claim above, or the induction on ϱ(ῑ) of check-layers.md.

The same argument rejects the variant with a counter, which creates below its
predecessor n times for an input n and then stops. It is lock free. Its box
cannot state a hypothesis that depends on n, so H again needs an infinite
chain. The only way out I see is a static grade per root, a natural number in
the type of `new` that bounds how often creations may nest downwards, with
ranks ω^d·β for grade d. That makes types name ordinals, which check-layers.md
rules out. I did not work it out.

### Recommendation

Keep (wf-new). (wf-new⁺) is sound and strictly more permissive, but none of
the examples needs it. FreshBetween and FreshMany create below a context point
at a field, which (wf-new) accepts. A field creation picks no ranks and can
already sit between context points whose ranks were fixed with room.

## 2. P-Connect with ranks

### The rule

Families go with plain `new`, so `w_fams W1 ## w_fams W2` goes. Static worlds
are `(A, facts)`, and `wf W` reads `well_founded (w_lt W)`.

    ptyped_N W1 (Σ1 ∪ ΣC) (C1, E1) T      ptyped_N W2 (Σ2 ∪ Σ̄C) (C2, E2) ∗
    (the disjointness premises of today)
    wf (W1|S ⊔ W2|S)        S = A_{W1} ∩ A_{W2}
    ────────────────────────────────────────────────────────────── P-Connect
    ptyped_N (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans(ΣC), E1 ⊎ E2) T

`W|S` is `wrestrict W S`, the derived order of W between points whose roots
lie in S, so it contains chains of W through its private points. P-Term asks
`wf W` in place of `strict W`. `ptyped_strict` becomes `ptyped_wf`, every
derivation sits over a well-founded static world, by induction with the lemma
below.

### The join lemma

    world_wf W1 → world_wf W2 →
      wf (W1 ⊔ W2) ↔ wf W1 ∧ wf W2 ∧ wf (W1|S ⊔ W2|S)            (wf_join_iff)

From left to right, each of the three orders is contained in the order of the
join (`wext_join_l`, `wext_join_r`, `rjoin_lt` in types/Worlds.v), and a
suborder of a well-founded order is well-founded.

From right to left, suppose an infinite descending chain
`x0 ≻ x1 ≻ x2 ≻ …` of single steps of the join. A step is a fact of W1, a fact
of W2, or program order (`jstep_inv`). A fact of `W_i` relates points of the
zone of `W_i` (`world_wf`), and program order keeps the root. So two
consecutive points outside the shared zone lie in the same private zone, or
outside both zones, and the step between them is a step of the owning world
(`step_out` for program order).

- If the chain meets shared points only finitely often, its tail lies in one
  private zone, and it is an infinite descending chain of that world.
- Otherwise, between two consecutive shared points `u_i ≻ … ≻ u_{i+1}` the
  inner points lie in one private zone, so `W_j ⊢ u_{i+1} ≺ u_i` for one j,
  which is a step of `W_j|S`. The shared points form an infinite descending
  chain of the amalgam.

Both contradict the right-hand side. This proof is classical. It extracts the
chain from a failure of `Acc` with dependent choice. A constructive proof by
nested `Acc` induction (on the amalgam at shared points, on `W_i` at private
points) follows the same decomposition, and the zone lemmas it needs
(`lt_zone`, `join_exit`, `join_amalgam`) exist for `strict_join_iff`. I did not
write it.

### What each component exposes, and where the ranking comes from

A component exposes `W_i|S`, its derived order on the points of the shared
roots. That order can be infinite (every shift and field of a shared root).
It exposes no ranks. The two components rank the shared trees independently,
and their rank functions need not agree on any point, so a condition that
compared them would reject correct compositions.

The composite needs a ranking in two places.

- Adequacy needs one ranked world R with `R ⊨ W1 ⊔ W2` to start the run. It is
  the rank function of `w_lt (W1 ⊔ W2)`, which exists because the order is
  well-founded (`rank_of` in section 4, constructive).
- The semantic composition (`sem_p_connect`) reads the composite at a ranked
  world `R ⊨ W1 ⊔ W2`. Then `R ⊨ W1` and `R ⊨ W2`, each component's relation
  holds at R itself, and the composition argument of today runs at R. A
  fresh root created by either component is fresh for R, so the two cannot
  collide, and the renaming of families apart (`wfrename`) goes.

### Tests

The client-server program split into two components. The channels a and b
become the cut ΣC at the constant root ρ, a at ρ and b at ρ·0. The client
forces its box at `(ρ, ρ·0, ρ·1)` and the server at `(ρ‾, (ρ·0)‾, ρ·1)`, so
each static world holds the instance it uses (laws `cs_L` of
examples/ClientServer.v, polarity b = true and b = false).

    W_cli  ρ+k ≺ (ρ·0+k)‾     ρ·0+k ≺ (ρ+k+1)‾     ρ+k ≺ ρ·1     ρ·0+k ≺ ρ·1
    W_srv  ρ‾+k ≺ ρ·0+k        (ρ·0)‾+k ≺ ρ+k+1     ρ‾+k ≺ ρ·1    (ρ·0)‾+k ≺ ρ·1

S = {ρ}, so the amalgam is the union of both. The measure of
`W_cs_wfworld` (field sum, offset, depth, examples/LFClientServer.v) read as
`ω²·fsum + ω·off + depth` ignores polarity and gives `ω·k` on `ρ±+k`,
`ω·k + 1` on `(ρ·0)±+k` and `ω² + 1` on ρ·1. Every fact of both worlds
rises (`ω·k < ω·k + 1 < ω·(k+1)`, everything below `ω² + 1`), and so does
program order. The amalgam is well-founded and P-Connect accepts. (check-layers.md
gives ρ·1 the rank ω². Depth 1 makes it `ω² + 1`. Nothing depends on it.)

A cycle across two components. a at the constant ρ, b at the constant τ. The
first component holds a⁺ and b⁺, receives on a, then sends on b. Waiting on a
while holding b asks `ρ ≺ τ‾`. The second holds a⁻ and b⁻, receives on b, then
sends on a. Waiting on b while holding a⁻ asks `τ‾ ≺ ρ`. Each world alone is
well-founded. S = {ρ, τ}, and the amalgam has `ρ ≺ τ‾ ≺ ρ`, so it is not
well-founded and P-Connect rejects. Today's strictness condition rejects it
too.

A descent across two components. Let δ_n be the n-fold field ρ·0·…·0 at
offset 0. W1 has the facts `δ_{2k+1} ≺ δ_{2k}` and W2 the facts
`δ_{2k+2} ≺ δ_{2k+1}`. Program order relates no two δ. Each world is
well-founded, its facts are disjoint pairs. The amalgam is the chain
`δ0 ≻ δ1 ≻ δ2 ≻ …`, acyclic and not well-founded. Today's P-Connect accepts
this pair, and lock-free adequacy then needs `wfworld` of the join as a
separate premise. The new P-Connect rejects it, which folds that premise into
the rule. I did not write a program whose two components need exactly these
facts.

## 3. The other cases of the fundamental theorem

Every case below uses one new lemma in place of reading `W ⊢ x ≺ y`.

    R ⊨ W → R ⊨ Γ → slt W Γ x y → ϱ_R(x) < ϱ_R(y)                (ent_sound)

It holds by induction on `fl` (static/Contexts.v). World facts and hypotheses
hold by assumption, program order holds because every rank function satisfies
it, and `<` is transitive. Monotonicity in the world is simpler than today.
`R ⊑ R′` keeps every rank of R, so every fact true in R stays true in R′.

| case | goes through | what changes |
|---|---|---|
| E-Link with caps | yes | Nothing about ranks. `o_link` reads points only to check that o1 and o2 sit at x and x‾. The link creates no point, and o1‾, o2‾ keep x‾ and x. In adequacy `lf_stab` holds because the waiter's own end keeps its point, and `lf_rank` holds because the holder s of o2‾ at x waits on o′ with `pt(o′) ≺ x‾`, so `ϱ(pt o′) < ϱ(x‾)`. The cap invariant `tk(o) + tk(ō) ≤ K` is about counters only. |
| actions | yes | An action moves an end from x to x⁺, to `(x·i)‾` (select) or to `x·i` (branch). All lie in the tree of the root of x and were ranked at its creation. A payload end already sits at its field of x (`payload_at`), so a send relocates nothing. Readiness reads through `ent_sound`. |
| E-Spawn | yes | Nothing. `o_spawn` splits Θ, and the moved ends keep their points. |
| E-New at a field | yes | Nothing to rank. `Γ ⊢ C` gives `R ⊨ C` by `ent_sound`. |
| P-Term | yes | `strict W` becomes `wf W`. The semantic judgment reads the thread at every `R ⊨ W`. The premise `strict W1` of `Pbody` goes, because a ranked world has no cycle. |
| P-Connect | yes | As in section 2. `strict_join_iff` becomes `wf_join_iff`, and `w_fams` disjointness and `wfrename` go. |
| subsumption | yes | Nothing. `tsub` relates types at the same points (`Vrel_tsub_pinst`), and Sub-Ex compares bodies. Where a constraint is weakened, `ent_sound` carries the facts. |
| E-Pack, E-Open, E-Box, E-Force | yes | `hold_at` and `hc_open` are static. `ent_sound` turns `hold_at W Γ C xs` into `wholds R C xs`. |
| E-Abs, E-App, readiness | yes | `lbx_below_h`, `ub_below_s` and the readiness clauses read through `ent_sound`. |

Ranked worlds remove these premises. `strict W1` in `Pbody`, `strict W`
and `wfworld W` in `lf_adequacy`, and the strict-join hypotheses of FlagPair
(`fp_unrealizable` becomes "no ranked world satisfies both threads at both
flags", the same cycle `x ≺ ȳ ≺ x`).

## 4. Universe levels

### What Lantana does

Lantana keeps two copies of the Ordinal library. The vendored copy gives the
layers `ℓ : ord.t`, the opam copy `Ord.t` gives fuel and witness amounts, and
the README of `ordinal/` says that two copies sidestep a universe
inconsistency (lantana2027, ordinal/README.md). `ord.t` is a monomorphic
inductive with one constructor `build (A : MyT) (os : A → t)` and
`MyT := Type` (ordinal/ordinal.v). The existential property instance for the
step index imports the opam copy (algebra/ordinal_existential_properties.v).
So one monomorphic ordinal type cannot serve both as data inside the objects
the step index takes suprema over and as the step index.

### Our stratification

v2 has the same two roles. A ranked world holds ranks, a creation choice holds
a ranked world and a constraint, and step indices take suprema over creation
choices (check-transfinite.md, section 1). So the rank ordinals must sit
strictly below the step-index ordinals. One universe-polymorphic definition at
two levels does this without a second copy.

    Polymorphic Cumulative Inductive Ord@{u} : Type@{u+1} :=
      | OZ | OS (a : Ord) | Osup (A : Type@{u}) (f : A → Ord).

    ranks         ROrd = Ord@{Set}      : Type@{Set+1}
    ranked world  (A : gset nat, ϱ : nat → point → ROrd) : Type@{Set+1}
    choice        (world, point, fact → Prop, …)          : Type@{Set+1}
    step indices  SOrd = Ord@{s}, Set+1 ≤ s             : Type@{s+1}

Ranks need suprema only over subtypes of `point`. The rank function of a
well-founded relation R on points is a `Fix` with the supremum over
`{y : point | R y x}`, which lives in `Set`. This is constructive, and the
σ of check-layers.md is a supremum of the same kind. The ranked world then
lives in `Type@{Set+1}`, which is where v2's `world` lives today
(`w_facts : fact → Prop`). Prop is impredicative, so the facts and C inside
worlds and choices raise no level, and no relation is ever stored inside a
world or a choice. That is why one polymorphic tree at two levels suffices
here.

Brouwer trees with suprema over ℕ only (`Ord : Set`) would also hold every
rank v2 needs (all ranks are countable), but then the rank function of a
relation given by a Prop predicate needs a decision of that predicate, so it is
classical. The `Set`-indexed suprema cost nothing in levels and keep the rank
construction constructive.

### The scratch check

The file below compiles against the built v2 (Rocq 9.1, `rocq c -R . GV`). It
is not part of v2.

    From GV Require Import types.Worlds.
    Check world.                           (* world : Type@{Set+1} *)
    Check point.                           (* point : Set *)
    Polymorphic Cumulative Inductive Ord@{u} : Type@{u+1} :=
      | OZ | OS (a : Ord) | Osup (A : Type@{u}) (f : A -> Ord).
    Polymorphic Inductive ole@{u} : Ord@{u} -> Ord@{u} -> Prop :=
      | ole_z b : ole OZ@{u} b
      | ole_s a b : ole a b -> ole (OS@{u} a) (OS@{u} b)
      | ole_sl a b : ole a b -> ole a (OS@{u} b)
      | ole_supl (A : Type@{u}) f b : (forall x : A, ole (f x) b) -> ole (Osup@{u} A f) b
      | ole_supr a (A : Type@{u}) f (x : A) : ole a (f x) -> ole a (Osup@{u} A f).
    Polymorphic Definition olt@{u} (a b : Ord@{u}) : Prop := ole (OS a) b.
    Definition ROrd := Ord@{Set}.                       (* : Type@{Set+1} *)
    Record rworld := RW { rw_consts : gset nat; rw_rank : nat -> point -> ROrd }.
                                                        (* : Type@{Set+1} *)
    Definition rank_of (R : point -> point -> Prop) (H : well_founded R) : point -> ROrd :=
      Fix H (fun _ => ROrd)
        (fun x rec => Osup {y : point | R y x} (fun y => OS (rec (proj1_sig y) (proj2_sig y)))).
    Record choice := Ch { ch_world : rworld; ch_pt : point; ch_C : fact -> Prop }.
                                                        (* : Type@{Set+1} *)
    Universe s. Constraint Set < s.
    Definition SOrd := Ord@{s}.                         (* : Type@{s+1} *)
    Definition sup_choices (f : choice -> SOrd) : SOrd := Osup choice f.
    Definition lift (a : ROrd) : SOrd := a.             (* cumulativity *)
    Fail Definition bad := Osup@{Set} choice (fun _ => OZ).
      (* universe inconsistency: Cannot enforce Set+1 <= Set *)

Everything except the last line is accepted, and the last line fails with the
inconsistency shown. So the levels are forced and consistent. v2 stays
monomorphic. Only `Ord`, `ole` and `olt` are polymorphic.

Not checked in the scratch file. Well-foundedness of `olt`, transitivity of
`ole`, and the arithmetic. Ranks need only `OS`, suprema and `<`. The natural
sum ⊕ of check-layers.md (fuel extension, the ticket invariant with ordinal
counters) is a separate question, and Brouwer trees give no obvious ⊕ with the
cancellation `α ⊕ γ < β ⊕ γ ↔ α < β`. Lantana imports a file
`classical_hessenberg` for its sums (prelude/ordinal_copy_facts.v), whose
content I did not read. Ranks do not need ⊕.

## What was checked and what was not

Checked on paper.

- The claim that no class of ranked worlds admits a fact down to an
  unconstrained context point, and why ω·α and natural-sum gaps fail.
- Soundness of (wf-new⁺) by the rank construction, and that it is not exact
  (the two-upper-bounds example).
- rx-chain and its counter variant under (wf-new) and (wf-new⁺).
- `wf_join_iff` by the classical chain argument, with the zone facts of
  types/Worlds.v.
- The split client-server worlds at the ranks `ω²·fsum + ω·off + depth`, the
  two-root cycle, and the descending pair that strictness accepts.
- The cases of section 3 against the obligations of relation/Relation.v and
  the rules of static/Typing.v.

Checked in Rocq, in a scratch file outside the repository's proofs.

- The universe levels of section 4 and the rejection of a rank ordinal with a
  supremum over choices.

Not checked.

- Anything in v2.
- A constructive proof of `wf_join_iff`.
- Well-foundedness of `<` on the Brouwer trees in Rocq.
- A finer exact static condition for downward facts.
- A program that realizes the descending pair of section 2.
- The live relation (compat/LiveDF.v) with ranked worlds.
- Static grades per root.

## Literature used

- lantana2027. The two copies of the Ordinal library and their roles
  (ordinal/README.md), the definition of `ord.t` with suprema over one fixed
  universe (ordinal/ordinal.v), the existential property instance over the
  opam copy (algebra/ordinal_existential_properties.v).
- spies2021transfinite, through check-transfinite.md, for suprema over the
  choice space in the existential property.
