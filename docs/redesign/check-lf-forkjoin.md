# Design check, lock-free fork-join with a termination measure

2026-11-22, branch redesign-fwd. Write-up only, no change to v2/. I read the
Rocq on redesign at a5e99e2 (static/Typing.v, static/Contexts.v,
static/Guard.v, relation/Relation.v, relation/Ranks.v, types/Worlds.v,
fuel/Fuel.v) and examples/ForkJoin.v on redesign-fj. Every argument is on
paper. The last section lists what was checked and what was not.

The question. Recursive fork-join with replies is lock free whenever its
recursion stops, and Padovani's lock-freedom system rejects it because its
priorities are naturals (padovani2014deadlock, p10). Kobayashi and Sangiorgi
recover lock freedom of `fact` with termination. Can v2's lock-free side do
the same, and what plays the role of termination?

## Verdicts

1. Kobayashi and Sangiorgi add one rule, LT-Hyb, to Kobayashi's lock-freedom
   types. It concludes `Δ ⊢_LT P` from robust deadlock freedom of P under Δ,
   robust termination of P and `nocap(Δ)`. Termination comes from a separate
   analysis, the level type systems of Deng and Sangiorgi made robust, with a
   size-change check on data for primitive recursion. All three premises are
   semantic. Section 1 has the details.
2. Of the four candidates, only an explicit measure on the box can play the
   role of termination. Counters, credits and tickets bound how long one end
   waits for its holder and how often it travels. They do not bound the depth
   of a recursion, and the endless fork-join meets all of them. The cost
   judgment bounds the steps of cost 0 of one thread, and fork-join spawns a
   new thread per level. Ordinal ranks already exist (relation/Ranks.v), and
   the descent of ranks along the recursive forces is a termination argument.
   They fail at the box and not at the creation, because a box must work at
   every instance of its hypothesis, the least-ranked one included.
3. Termination evidence does not get around Proposition 7 of
   check-general-new.md. Any box with one hypothesis H for all calls and a
   recursive force at a lower point has no model, whatever proves that the
   recursion stops. The box has to be indexed by the call depth. The minimal
   form is one natural-number measure j per box, instantiated at the meta
   level as the session variables of E-Box already are, with H, U and the cost
   as functions of j, the self usable only at j′ < j, and one data type
   `Nat_j` that tells the body at run time which branch it is in.
4. The design of section 4, measured boxes, types the binary and unary
   fork-join at every depth, `fact`-shaped chains and `fibo`-shaped trees. It
   leaves rx-chain, rx-relink, rx-postpone and rx-delegate rejected, because
   it changes no premise about counters, tickets, aging or E-New, and an
   unmeasured box keeps Proposition 7. It needs no ordinal rank above ω and no
   excluded middle. The Rocq cost is one type former, one term annotation,
   four typing rules and an induction on j in the box case of the fundamental
   theorem.

## 1. The hybrid system of Kobayashi and Sangiorgi

The source is kobayashi2010hybrid, indexed today with facts, page numbers of the
PDF at www-kb.is.s.u-tokyo.ac.jp/~koba/papers/hybrid.pdf.

The rule (p8).

    Δ ⊨_RD P     Erase(Δ) ⊨_RTer P     nocap(Δ)
    ─────────────────────────────────────────── (LT-Hyb)
                   Δ ⊢_LT P

SLT-Hyb adds robust confluence and gives strong lock freedom under strong
fairness. The paper states that the premises are semantic requirements and
that the system is parametric in the method that checks them (p2).

- Robust deadlock freedom under Δ (Definition 3.17, p7) is deadlock freedom
  of every closing instance and every derivative after any interaction with
  the environment, plus the obligations of Δ. Kobayashi's deadlock-freedom
  types guarantee it (Theorem 3.1, p8).
- Robust termination (Definition 3.16, p7) asks that every derivative reached
  by any well-typed sequence of transitions with the environment has no
  infinite internal sequence. Plain termination is too weak, and the paper's
  counterexample is `c[b] | c(x).(x | ∗a.x)`, which terminates alone and
  diverges after receiving a.
- `nocap(Δ)` (Definition 3.19, p8) asks every capability level of Δ to be ∞,
  so P meets its obligations without relying on the environment. Without it,
  `∗a(x).b[x]` and `a[c] | ∗b(x).a[x]` each satisfy the other two premises
  and compose to a wrong judgment (p8). Remark 3.2 says that dropping nocap is
  unsound even when LT-Hyb is used once in a derivation.

How termination is established (Sections 5 and 6, p13 to p16). The authors
reuse the four type systems of Deng and Sangiorgi. In the simplest one, Lev,
every channel type carries a natural level, and a replicated input
`∗p(x).P` must have a level above every name output in P outside inner
replications, so a multiset of levels decreases under reduction (p13). Lev
cannot type a replicated input that outputs on itself. Lemma 5.2 turns such
a system into one for robust termination when erasing levels is injective on
the channel types of the initial environment (p14). For recursion like the
factorial, TyPiCal uses the second Deng–Sangiorgi system, which allows an
output on a channel of the same level when the argument is smaller in the
order of the naturals, and checks this with a size-change termination
library. This also verifies an Ackermann server (p16).

What they type. The factorial of the paper is tail recursive with an
accumulator, `∗fact_it(n, x, r). if n = 0 then r[x] else fact_it[n−1, x×n, r]`,
and LT-Hyb is applied to the server alone, so a divergent client does no harm
(p2, Example 3.3 on p9). Padovani attributes lock-free typability of his
non-tail `fact`, process (3), to this hybrid approach (padovani2014deadlock,
p10). The paper does not show process (3). Its rule would cover it once a
termination analysis proves (3) terminating, and the second Deng–Sangiorgi
system accepts the decreasing argument x − 1.

The hybrid rule needs termination of the whole component it is applied to,
spawned threads included. Section 7.1 shows a process that sends on a
whatever P does, which LT-Hyb rejects unless P also terminates (p16).

Two consequences for v2. A rule in the shape of LT-Hyb has semantic premises,
which v2's typing rules never take. And the termination analysis that makes
it work is a level discipline on recursive calls with a decreasing data
argument. Section 4 builds exactly that discipline into the box, so v2 needs
no hybrid rule and no nocap condition. Its lock-free relation is
compositional already.

## 2. The candidates

### Counters, credits and tickets

A counter bounds the number of actions a thread performs on other ends while
it holds an end without using it (fuel/Fuel.v, header). A credit pays for
counters of captured ends, and the cap `tk(o) + tk(ō) ≤ N` bounds how often an
end travels. All three are local to one thread and one end. The endless
fork-join, rx-chain with replies, performs at most three actions per level
while it holds w, hands each child one end with its counter minus one, and
links nothing. It meets every counter, credit and ticket condition at N = 3.
It is not lock free, because the close of main waits for a tree that never
stops growing. So no condition on these three can distinguish the bounded
fork-join from the endless one. They are not a termination measure.

### The cost judgment

The steps of cost 0 sit in the least fixpoint `Eind` of each level, so one
thread takes finitely many of them between two costed steps. The fuel layer
charges one level per step, spawn included. Both bound one thread. Fork-join
terminates as a tree of threads, and the endless variant has a finite run in
every thread. The cost judgment cannot see the depth of the tree.

### Ordinal ranks

Ranks are Brouwer trees (relation/Ranks.v). A ranked world orders points by
rank (types/Worlds.v, `w_lt`), ranks persist along `⊑` (`wext_rank`), and the
creation of O-New picks the new ranks at run time (`o_new` is an existential
over S, π and W′ ⊒ W). So a run of the depth-n fork-join can already use
ranks n, n − 1, …, 0 below a root of rank n, and the creation choice can
depend on the run. The descent of ranks along recursive forces is a
termination argument of the Deng–Sangiorgi kind, with ranks as levels.

The obstruction is the box. V of `□∀ιs. H. U` asks the thunk to work at every
world W′ and every instance xs with `wholds W′ H xs` (relation/Relation.v,
the `TBox` clause of `Vbody`). Among those is an instance whose point has the
least rank that H allows. There the body has to create below a point with no
room, whatever data it holds. This is the semantic form of Proposition 7.
Transfinite ranks do not change it. A root of rank ω admits every finite
depth, but H must then say that the instance has rank at least ω, and the
child, one rank lower, needs the same.

### An explicit measure on the box

This works and is section 4. It is the Deng–Sangiorgi discipline on v2's
boxes. A box carries a measure j, its hypothesis and type may depend on j,
and its body may force itself only at a smaller measure.

## 3. Why termination evidence cannot avoid call-indexed boxes

Proposition 7 of check-general-new.md assumes one box hypothesis H, a branch
of the body that forces the box at xs′ with `Γ_b ⊢ H at xs′` and
`Γ_b ⊢ f(xs′) ≺ f(ιs)`, and a sound E-New. It concludes that W, Γ0 and H have
no common model. The proof takes a model with the least rank of `f(xs)` and
builds one with a smaller rank. It never asks whether the recursion stops.

So any proof of termination, static or semantic, leaves the static block in
place as long as the box states one H for every call. The recursive call of
fork-join needs room of depth n − 1 below the child, and the call above it
needs room n. One H cannot state both, and the box must be indexed by
something that decreases along the calls.

The index alone does not suffice either. The body is one term, and at the
bottom index it still contains the recursive force. A case split on data
adds no fact (check-general-new.md, the descent). So the type of the data
must depend on the index, so that at index 0 the recursive branch is
missing. These two pieces are the minimal form.

- A measure j ∈ ℕ per box. E-Box types the body at every j, as it already
  types the body at every session instance ss. The self is usable at j′ < j.
- A type `Nat_j` of numerals at most j, whose case rule omits the successor
  branch at j = 0.

A static bound d is the special case with d + 1 separate boxes
(check-general-new.md, the bounded descent). The measure folds these boxes
into one.

## 4. The design, measured boxes

### Syntax and types

- Terms. `!^μ e`, a box marked as measured. It steps as `!e` does, and the
  mark is read only by the guard.
- Types. `□^μ ∀ιs ∀κs ∀j. H_j. U_j` with `H : ℕ → bcs` and `U` a type that may
  mention the measure variable j, through `Nat_m` and the cost annotations.
  A measure expression m is `j − k` or a constant k.
- `Nat_m`, the numerals `zero` and `succ v` with at most m successors, written
  with Inj as unary sums are. `Nat` without index is not needed for closed
  programs.

### Rules

    ∀ j ∀ ss.  ∅ ; Γ, H_j ; Δ, f : □^{<j} ∀ιs ∀κs ∀j′. H_{j′}. U_{j′}
                 ⊢ e : U_j[ss]
    ──────────────────────────────────────────────────────────── (E-Box-μ)
    ∅ ; Γ ; Δ ⊢ !^μ e : □^μ ∀ιs ∀κs ∀j. H_j. U_j

    e : □^{<b} ∀ιs ∀κs ∀j. H_j. U_j     j′ < b     Γ ⊢ H_{j′} at xs
    ──────────────────────────────────────────────────────── (E-Force-μ)
    force e : U_{j′}[xs, ss]

    zero : Nat_k                    v : Nat_k ⟹ succ v : Nat_{k+1}

    e : Nat_k     e1 : T     k ≥ 1 ⟹ (x : Nat_{k−1} ⊢ e2 : T)
    ──────────────────────────────────────────────── (E-Case-Nat)
    case e of zero ⇒ e1 | succ x ⇒ e2 : T

A box of bound ∞ is the outside view, so main forces at any j′. The premises
`j′ < b` and `k ≥ 1` are comparisons of natural numbers fixed by the meta-level
quantifier of E-Box-μ. They read no semantics and add no syntactic clause to
the relation. E-Case-Nat at k = 0 types e2 under nothing, so the recursive
force in the successor branch needs no instance. The other premises of E-Box
and E-Force (`lenv_unl`, `tcontr`, `ub_below_s`, `sinsts`) carry over
unchanged.

### Relation

    v ∈ V^W_n⟦Nat_k⟧          iff  Θ = ∅ and v is a numeral with at most k successors
    v ∈ V^W_n⟦□^b ∀ιs ∀κs ∀j. H_j. U_j⟧
                              iff  Θ = ∅, v = !^μ e, fends e = ∅, and for every
                                   j < b, W′ ⊒ W, xs, ss with wholds W′ H_j xs,
                                   thunk e ∈ V^{W′}_n⟦U_j[xs, ss]⟧

Fuel reads `Nat_k` as data with no end, and a measured box as a box per force.
The relation gains no syntactic clause.

### Soundness of E-Box-μ

The case of `typed_sem` proves V of the box at level n by induction on j. At
j the self at bound j is in V at the same level n by the induction
hypothesis, so the body's premise gives V at j. No later is needed, because
the recursion is well-founded in j and not guarded by the step index.

The guard (static/Guard.v) puts the self of every box at ▷, and fork-join
uses its self inside the first spawn, before any action. So the unmeasured
worker also fails the guard of the lock-free judgment. For a measured box
the guard leaves the self unmarked, which the induction on j justifies. The
guard exists to stop `!(f = force f)` from diverging at cost 0
(static/Guard.v, header). A measured self lowers j at every force, so a chain
of measured forces is finite. The mark `!^μ` is what lets the guard, which
reads no types, tell the two boxes apart.

### What it types

Binary fork-join of depth j. With ι·u for a field word u, ι·ε read as ῑ on
the right of a fact, and κ ∈ {0, 1},

    H_j(ι) = { ι·u·0 ≺ (ι·u·1)‾,  ι·u·κ ≺ (ι·u)‾  |  |u| < j }

    wk = !^μ (λ⟨w, n⟩. case n of
           zero   ⇒ close w
         | succ m ⇒ let ⟨c1, c1′⟩ = new in let ⟨c2, c2′⟩ = new in
                    spawn (λ_. (force f) ⟨c1′, m⟩); spawn (λ_. (force f) ⟨c2′, m⟩);
                    close c1; close c2; close w)

at type `□^μ ∀ι ∀j. H_j. (End@ι ⊗ Nat_j ⊸ 1)`. Both channels are created at
the fields ι·0 and ι·1 by E-New-Field, as in examples/ForkJoin.v. Readiness of
the three closes asks the three facts with u = ε, which are in H_j. The forces
at instance (ι·κ)‾ and measure j − 1 ask `H_{j−1}((ι·κ)‾)`, and every fact of
it is a fact of `H_j(ι)` with u extended by κ, because a field is the same
from both ends. At j = 0 the successor branch is absent. main receives no
input. For a numeral of value d it creates w at a fresh root ρ with laws
`H_d(ρ‾)`, forces wk at (ρ‾, d) and closes w. The laws are finite and
well-founded by the measure (d − depth, field sum, offset), the measure of
`fj_wf_new` extended by depth, so (wf-new) accepts them.

The unary chain, the shape of Padovani's `fact` without arithmetic, is the
same with one child and `H_j(ι) = { ι·0^{i+1} ≺ (ι·0^i)‾ | i < j }`. A
`fibo`-shaped tree forces the self at j − 1 and j − 2 and splits m once more.
Its hypothesis contains the facts of both subtrees, a finite set for each j.

Ranks stay finite, at most d plus the offsets, so no ordinal above ω and no
excluded middle enter. An open server that answers requests of unknown size
needs `Nat` as a payload, an existential over j opened by a rule typed at
every j. Each request then creates its own root with laws `H_j`, and ranks
stay finite again. That rule is a seventh change and is not needed for the
fork-join question.

At a finite N, the worker performs two actions on c1 and c2 while it holds w,
and hands each child one end with its counter minus one. N = 3 meets these
counts. I did not check the cost annotations `c_j` of the box family, which
grow with j.

### What it must still reject

- rx-chain. Its recursion has no case split. At j = 0 its body forces the
  self, and no j′ < 0 exists, so E-Box-μ has no derivation at j = 0. Written
  with an unmeasured box it meets Proposition 7 as before. A variant that
  carries a numeral and never consumes it fails E-Force-μ, because
  `Nat_j` is not below `Nat_{j−1}`, and any variant that consumes it stops at
  depth j.
- rx-postpone. The loop that holds b is unmeasured and has cost ∞, so aging
  rejects it as before. A measured loop stops after j rounds and then closes
  b, and that program is lock free.
- rx-delegate. Every send hands e on with its counter minus one. Measured
  boxes change no counter, so an endless delegation still runs out. A
  measured delegation stops.
- rx-relink. E-Link asks the credit of each linked end to exceed the partner
  bound. Measured boxes do not touch E-Link, and the rejection by tickets
  stays.

Measured boxes only add programs whose recursion is bounded by the measure.
Each of the four counterexamples is lock free once its recursion is bounded,
so none of them becomes typable in its endless form.

### Rocq cost

- types/Types.v. A constructor for `Nat_m`, a flag and a family on `TBox`
  (`H : nat → bcs`, measure expressions in U), with their cases in every
  function over `ty` (instantiation, duality of payloads, erasure, scoping,
  heads, size). `TBox` occurs 60 times in 20 files on redesign.
- lang/Syntax.v. The mark on `EBox`, ignored by `tstep`. Its cases in
  `emap`, substitution and `is_val`.
- static/Typing.v. E-Box-μ, E-Force-μ, zero, succ and E-Case-Nat, or E-Box and
  E-Force with the measure as an extra premise. Conservativity, weakening,
  renaming and point substitution gain the routine cases.
- static/Guard.v. The self of `!^μ` stays unmarked. One rule.
- relation/Relation.v. Two clauses of `Vbody`. fuel/Fuel.v, two clauses of
  `Vfuel`.
- compat/LiveRules.v and static/Fundamental.v. The box case by induction on
  j, the force case, three easy cases for numerals. cost/CostRules.v, the
  same five cases.
- examples/. ForkJoin.v at every depth, unary and binary, deadlock free and
  lock free.

My estimate is 800 to 1200 lines, most of them routine cases of the new
constructor. The two places that can fail are the box case under the marks of
`GrelL` and `sem_later`, and the guard exemption against the counterexamples
of Appendix B #12 to #15 (examples/GuardEx.v).

## Relation to the parallel check

If the deadlock-free side moves to acyclic orders, fork-join with one
unmeasured box may type there, as Padovani's `fact` types in his
deadlock-freedom system. The lock-free side keeps well-founded ranks, because
`lf_adequacy` ranks a pending thread by the point of its end. Measured boxes
are then the lock-free counterpart of the deadlock-free typing. A measured
derivation erases to an unmeasured one by forgetting the measure, if the
deadlock-free side admits the descent, so conservativity between the two
sides survives.

## What was checked and what was not

Checked on paper.

- The rule LT-Hyb, its three premises, robust termination and nocap, and how
  termination is obtained, against pages 2, 4, 7, 8, 9, 13, 14 and 16 of
  kobayashi2010hybrid.
- That counters, credits, tickets and the cost judgment accept the endless
  fork-join, by the counts above.
- That V of a box quantifies over every instance of its hypothesis, against
  `Vbody` on redesign.
- The facts of `H_j` for the unary and binary worker, the inclusion
  `H_{j−1}((ι·κ)‾) ⊆ H_j(ι)`, and the four rejections.

Not checked.

- Anything in Rocq. No statement here is mechanized.
- The box case of the fundamental theorem under the marks, the guard
  exemption against examples/GuardEx.v, and the cost annotations of the box
  family.
- The LF judgment for the one-round fork-join of examples/ForkJoin.v, which
  the guard blocks as it stands.

## Literature used

- kobayashi2010hybrid. LT-Hyb and SLT-Hyb (p8), robust termination and its
  counterexample (p7), nocap and its counterexample (p8), weak lock freedom
  (p4), the tail-recursive factorial server (p2, p9), the Lev system (p13),
  Lemma 5.2 (p14), the size-change extension and the limitation of Section
  7.1 (p16).
- padovani2014deadlock. `fact` and `fibo` deadlock free and not lock free,
  and the attribution to the hybrid approach (p10), natural priorities in
  the lock-freedom system (p7).
