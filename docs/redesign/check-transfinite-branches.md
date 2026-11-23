# Design check, per-branch orders on older points (joint plan, LR item 5)

2026-11-23, branch fx-transfinite from redesign f1fb155. Write-up only, no Rocq
change. Approved by the author as step one of item 5 of the joint plan
(~/proglang/research/lean/cll-order/.claude/notes/joint-plan-v2.md, section LR).
The argument is on paper and was not checked in Rocq.

## Verdict

No. Ordinal step indices with the creation choice inside the relation do not
give per-branch orders on points created before the branch. Both are already
in the Rocq on redesign (section 0), and the obstruction is the world, which
the index never touches. A ranked world fixes the order between any two of its
points for good (Lemma F in section 1). The relation asks every thread to be
ready after both labels of an offer, at worlds that order the older points as
the world of the creation does. The program R of CLL≺ (D23) is lock-free and
fails the lock-free relation for this reason (section 2).

Soundness needs one order per run and no more (section 3). Two changes of the
world realize that, and neither depends on the index beyond what v2 already
has.

- A. The world carries the slice of the run, a map λ from points to the
  label or value exchanged there. The creation picks ranks per slice, an
  offer whose label disagrees with λ obliges nothing, and ranks stay fixed
  once chosen. This accepts R. It needs two conditions, each point hosts at
  most one exchange in a run, and the point that decides a branch exists when
  the younger of the two ordered points is created. About 40 files change,
  12 of them in substance (section 4).
- B. Ranks are chosen late. A creation may leave a root unranked, one thread
  owns the right to rank it, and the label that resolves the branch carries
  the facts to the partner. This covers deciding points created later as
  well, and changes the world, every step obligation, the session types and
  the criterion. It touches most of v2 (section 5).

A is the one to test first.

## 0. What the Rocq already has

The port that check-transfinite.md section 4 estimated at 43 files is done on
redesign (pending.md, report of the second run of 2026-11-21). On
fx-transfinite the following hold.

- The step index is `Ix := ord`, Brouwer trees (relation/Ord.v), and the
  relation is one `osfix` (`RelA`, relation/Relation.v).
- O-New picks the session type, the point and the grown world,
  `∃ S π W', W ⊑ W' ∧ at_cost_E n (c_new κ) …` (`o_new`).
- The existential property is `exist_prop` (relation/ExProp.v), with
  excluded middle and functional choice as arguments. `lfsoup_step_all`
  (soup/SoupRun.v) fixes one creation choice `tchoice` for every level.
- A soup state carries its ranked world `s_W` (soup/State.v), and a creation
  moves to the world it chose (`world_next`, soup/Soup.v).
- `lf_adequacy` (soup/LFAdequacy.v) feeds the criterion with the order of the
  chain of worlds of the run, `wchain_lt`, which is well-founded by
  `wchain_lt_wf` (types/Worlds.v).

So the question of item 5 is no longer about the index. It is whether the
world, with the choice already inside the relation, can order older points
per branch.

## 1. Ranked worlds freeze the order of their points

Lemma F. If W is ranked, W ⊑ W′, and x, y are points of roots of W, then
`w_ord W' x y ↔ w_ord W x y`.

Proof. `w_ord_rank` turns both sides into a comparison of ranks, and
`wext_rank` says the ranks of W′ at x and y are those of W. ∎

A root brings all its points at once. `wgrow` ranks every point of a new root,
so its successors x⁺ and its fields x·κ, including the branch points
`bra_pt x i = x·(bfield i)` and the payload points, are ranked at the creation
of the root. Lemma F then says that no extension orders two of them
differently, and no extension adds a fact between them.

The relation reads both labels of an offer. `head_step` lets `EBra (Chan o)`
step with `SBra o i` for each i (lang/Semantics.v), and `Esteps` has a conjunct
for every such step (O-Branch). The same holds for every received value at
O-Recv. `Ebody` quantifies over every W1 ⊒ W, and `Eind` asks readiness at
every level, the level of a cost-0 step included. A thread holding older points
x, y before an offer is therefore in `E[live]^W _ α` with α ≥ 1 only if the
readiness of each branch holds at some extension of W. By Lemma F every such
extension orders x and y as W does. Two branches that need x ≺ y and y ≺ x
make the thread fail at every α ≥ 1.

The index plays no part in this. The argument reads one unfolding at a level α
and readiness one step later, at the levels j with j + c_take ≤ α. A finite α,
a successor and a limit behave alike. Moving the choice inside the relation
does not help either. The choice of O-New is made at the creation step, and its
continuation must already hold for every later label. A choice that depended on
the label would need the label at a time when the relation still quantifies
over both.

## 2. The counterexample R

R is the process of D23 in ~/proglang/research/lean/cll-order/.claude/notes/
counterexamples.md, the shared test program of the joint plan.

    T = case e { l : e().c⟨a⟩.(a[].0 | f⟨g⟩.(c().g[].0 | f().0)),
                 r : e().f⟨g⟩.(g[].0 | c⟨a⟩.(f().a[].0 | c().0)) }
    U = c̄(b).b().c̄[].0        V = f̄(h).h().f̄[].0
    R = (ν c c̄)((ν f f̄)(T | V) | U)

with e free at `&{l : ⊥, r : ⊥}`, c at x, f at y and c, f : 1 ⊗ ⊥. Each
blocking state generates one fact α ≺ β^⊥, which is our readiness fact
u ≺ v̄ (`below_rest`, relation/Readiness.v, and cll-insights.md item 1). With
`pay` the payload field the four facts are

    T in l    x⁺ ≺ ȳ·pay            T in r    y⁺ ≺ x̄·pay
    U         x̄·pay ≺ x⁺            V         ȳ·pay ≺ y⁺

and together they form the cycle x⁺ ≺ ȳ·pay ≺ y⁺ ≺ x̄·pay ≺ x⁺. Each branch
with U and V is acyclic, every run takes one branch, and R is lock-free.
CLL≺ accepts R by its conservativity theorem, and the joint plan names R as
the example of per-branch extensions for deadlock freedom (line C, item 1).

In the lock-free relation, with R transcribed to GV, the four points are fields and successors of the
roots of c and f, ranked when c and f are created. Take the soup state right
after the two creations, before e delivers a label. Every thread is in
`E[live]` at `s_W`. By section 1, T needs both of its facts at extensions of
`s_W`, and U and V need theirs. Lemma F puts all four into the one order of
`s_W`, which is a strict order, so no ranks exist. The state is in the soup at
no α ≥ 1, `lf_sem` fails, and the lock-free fundamental theorem cannot type R
under any rule set that keeps ranked worlds.

R is as small as such a counterexample gets in two respects. Branch facts of
one thread alone never conflict. T's two facts without U and V are met by one
rank with x⁺ and y⁺ low and the payload points high. So partners must generate
facts from the dual side back to x⁺ and y⁺, and a thread generates a fact only
while it holds two ends. That is why U and V receive an end. The decision must
also travel on a third channel. A decision on c itself moves the ends of c to
`bra_pt x l` or `bra_pt x r`, two distinct points with independent ranks, and
the conflict disappears.

## 3. One order per run is enough for soundness

The criterion asks for one well-founded relation and one measure per run
(`lf_run_criterion`, lockfree/Criterion.v, with `HR`, `Hstab` and `Hrank`).
`lf_adequacy_soup` instantiates it with `wchain_lt` of the worlds of the given
run (soup/LFAdequacy.v, lines 623 to 625). Nothing compares two runs. A world
structure in which every run grows a chain whose union is well-founded, and in
which readiness holds at the worlds of that chain, gives lock freedom.

So realizing only the order of the branch a run takes suffices. The relation
cannot realize it at the creation, because section 1 shows that the creation
has to serve both branches. Two ways remain. The relation gets the branch of
the run as a parameter (section 4), or the choice moves from the creation to
the branch (section 5).

## 4. Alternative A, the slice in the world

This is the oracle of fable-joint-review.md (D10), with four corrections. The
map lives in the world, so no signature changes. Senders are vacuous as well as
receivers. Received values count, so a case on data is covered. Each point must
host at most one exchange.

### 4.1 The change

A world gains a component

    w_obs : point → option obs        obs = a label or a value with channel names erased

and extension keeps it, `w_obs W' = w_obs W`. Ranks keep `wk_ext`, Lemma F
holds unchanged, and `wchain_lt_wf` needs no new proof.

Write `agrees W z v := w_obs W z = Some v`, with z the point of the receiving
end and the sender read at z̄. The obligations of the four exchanges gain one
antecedent each.

    o_branch o i e'   ⇒   agrees W x (label i) → (today's body)
    o_select o i e'   ⇒   agrees W x̄ (label i) → (today's body)
    o_recv o w e'     ⇒   agrees W x (value w) → (today's body)
    o_send o w e'     ⇒   agrees W x̄ (value w) → (today's body)

with x the point of o, and the same at Q-Branch, Q-Select, Q-Recv and Q-Send.
An exchange that disagrees with the slice, or happens at a point the slice
leaves at None, obliges nothing. Nothing else in the relation reads λ.

The creation choice is unchanged in form, `∃ S π W'`, but W′ may now depend on
`w_obs W`. In R the creation of f picks ranks with x⁺ ≺ ȳ·pay when λ sends l
at e and y⁺ ≺ x̄·pay when it sends r. Each slice gets an acyclic set of facts,
and one ranked world per slice exists.

### 4.2 Why it is sound

Kripke monotonicity. λ is fixed along ⊑, and the ranks are fixed as before.
Every lemma that moves E, V or P to a larger world (`Erel_mono`, `soup_inv_mono`)
keeps its proof, and the antecedent is read at the world the obligation is
read at.

Other threads holding the same points. All threads of a soup read the one
world `s_W` and hence the one λ. T in branch l and U waiting on b both read the
ranks of slice λ, so they agree on the order of x⁺, ȳ·pay, y⁺ and x̄·pay.
Composition (`lf_p_connect`) reads both components at one world and keeps that
agreement.

The soup invariant. The invariant itself does not change. The step lemmas
(`lfsoup_step` and its users in soup/SoupStep.v, SoupSync.v, SoupLink.v and
SoupRun.v) are stated for events that agree with `w_obs (s_W a)`. A creation
keeps λ, because `tc_W` extends `s_W`. `exist_prop` still fixes one choice per
creation for every level, and the choice space stays small, because λ is a
function between types in Set (spies2021transfinite, Theorem 6.2, p12).

Adequacy. Given a fair run r, set λ_r z to the label or erased value exchanged
at z in r, and None when r exchanges nothing there. Defining it decides
whether an exchange occurs at z somewhere along an infinite run, which uses
excluded middle, and picks the value, which uses functional choice. Both are
already arguments of `lf_adequacy`. The judgment holds at a ranked world with
`w_obs = λ_r`, because the fundamental theorem gives `lf_sem` at every world
that models the static world, for every λ. Every event of r agrees with λ_r,
so the soup follows r, and the chain of its worlds is ranked and well-founded
by `wchain_lt_wf`. Readiness before an exchange does not mention λ, so the
dependency chains of `lf_local_progress` are those of today.

Deadlock freedom. Its adequacy follows one finite prefix. λ is read off that
prefix with None elsewhere, which is decidable, so deadlock freedom stays
constructive.

The existing rules. The obligations under λ are weaker than today's, so the
existing fundamental theorems hold for every λ with their present proofs plus
an introduction of the antecedent. A proof that consumes an obligation, such
as a synchronization in `sem_p_connect`, gets the agreement from the event it
follows.

### 4.3 The two conditions

Point linearity. λ_r is a function only if every point hosts at most one
exchange in a run. v2 does not guarantee this today. `e_new_fld` places a
channel at x·κ with no freshness premise, so one thread can create two
channels at the same field. A link of ends at x and x̄ leaves two channels at
one pair of points, although only one exchange happens across them. The first
task of A is the lemma "each point hosts at most one exchange per run", with a
freshness premise on fields if the lemma fails without it.

The deciding point must have a name. Facts between two older points are added
at the creation of the younger one, and their guard names the point that
decides the branch. In R that point is the interface end e, which exists before
c and f, and A accepts R. The variant R′ creates e after c and f at a fresh
root, through E-New. The guard would have to name a root that does not exist
yet, and the semantic E-New picks that root after the ranks of f are fixed. A
rejects that derivation. With e placed at a field of x through E-New-Field, by
a thread that still holds c, the guard names x·κ and A accepts the program.
Whether every derivation of the first kind can be moved to a field is open. A
thread that holds no older point and selects on a fresh channel selects a label
it computed itself, which is a correlated choice (D23 and O9), and CLL≺ rejects
those as well.

### 4.4 The static side

The relation alone does not type R. The typing needs guarded facts and two
rules that introduce a guard.

- A constraint of E-New may carry a guard, a literal z:i over a point z of Γ
  or of a field of the new point. `sw_lt`, `swf`, `wf_join_iff`,
  `acyc_join_iff` and `wmodels` are read per slice, the slice being an
  assignment to the literals. A world models a guarded fact when the fact holds
  in it whenever `w_obs` makes the guard true.
- E-Offer types `case (bra e) of …` with the literal z:i available in branch
  i. Its semantic proof has `agrees W z (label i)` in hand at the O-Branch
  obligation, so the guarded facts hold there and at every extension.
- E-SelectIn types the continuation of a selection of label i at z̄ with the
  literal z:i, by the same argument at O-Select.

A literal never comes from the type of an end alone. Without the two compound
rules the relation would need a clause tying the points of the environment to
λ, which adds a syntactic condition to the relation and needs the author's
agreement first (memory, no syntax in the relation).

### 4.5 Cost

Files that change in substance (12).

- types/Worlds.v. `w_obs`, the clause of `wext`, the constructors
  `wranked_of`, `wgrow`, `wrank`, `wstrict_of`, guarded facts and the per-slice
  versions of `sw_lt`, `swf`, the two join theorems and `wmodels`. The join
  proofs run unchanged inside one slice.
- types/Points.v. `fact` gains a guard, with `FLt` kept as the unguarded case.
- relation/Relation.v. The antecedent at eight obligations and the mapping
  lemmas `Esteps_mapX` and `Psteps_mapX`.
- soup/SoupStep.v, soup/SoupSync.v, soup/SoupRun.v, soup/LFAdequacy.v. Steps
  restricted to agreeing events and λ_r in adequacy.
- A new soup/Slice.v with λ_r and point linearity.
- static/Typing.v. Guarded constraints in `new_ok`, E-Offer, E-SelectIn and,
  if needed, freshness of fields.
- static/Fundamental.v and soup/LFTyped.v. E-New picks ranks per slice by
  `rank_of` of relation/Ranks.v on the slice, plus the cases of the two new
  rules.
- static/Hiding.v. P-Connect per slice.

Files that change mechanically (about 28). compat/Redex.v, Connect.v,
ConnectCross.v, ConnectExt.v, ConnectExtMsg.v, ConnectSteps.v, Rename.v,
RenameInd.v and LiveRules.v introduce or forward the antecedent. Rename needs
λ invariant under renaming of channels, which the erasure of names gives.
relation/Closure.v and relation/Adequacy.v follow the obligations, the latter
with λ of the prefix. soup/SoupLink.v, LFEvents.v, LFLocal.v and LFRunFacts.v
follow the restricted steps. static/PointSubst.v, PointSubstTyped.v,
Conservativity.v, Consts.v, Constants.v, Contexts.v, Inversion.v, ConnectN.v,
ConnectNExact.v and FundamentalProc.v carry guards through substitution and the
per-slice premises. The 25 example files that state facts keep `FLt` as
unguarded facts and should need no edit beyond rebuilding. The four notation
tests need regenerated .expected files. A new examples/LFR.v types R.

Fuel (fuel/) does not change. Its obligations stay as they are, and the soup's
fuel part already steps along every event.

Risk lies in point linearity and in the per-slice ranks at E-New. The rest is
an extra hypothesis threaded through proofs that do not use it.

## 5. Alternative B, ranks chosen late

A creation may leave its root unranked. An unranked root may only sit above
ranked points, `z ≺ x` with z ranked, and carries no fact to another unranked
root. Extension may then rank a root that W leaves unranked, with ranks above
every ranked point below it. Such a rank always exists, because no ranked
point lies above the root. The union of a chain is still well-founded, because a
descending sequence takes at most one step through unranked roots, by program
order, before it enters ranked points with falling ranks.

The cost is in what the late choice needs.

- Ownership. The thread that ranks a root at its branch needs every extension
  in its own `∀ W1 ⊒ W` to leave the root unranked. So the right to rank
  becomes a resource held in the environment, and extension becomes relative
  to what a thread holds.
- Every step may grow the world. Today only O-New does. The select or the case
  that resolves a branch needs `∃ W'` in its obligation, and the soup moves to
  that world at every event.
- The partner must learn the facts. In R, T resolves the branch and U and V
  wait on points whose rank T fixes. They cannot read that from their own
  relation. The label has to carry the facts, a choice type `⊕{l : [C_l] S_l}`
  whose constraints the selector proves and the receiver assumes. That is a
  new session-type former, with `dual`, `unfoldS`, `sequiv`, aging and
  contractivity extended to it.
- The criterion needs a new chain lemma for partly ranked worlds.

Here the ordinal index does matter, as it does for creations. The late choice
sits inside an obligation and depends on the level, and `exist_prop` fixes it
once per run. That part is already in place. Everything else touches most of
the 145 files of v2.

## 6. What to do next

- No port is needed for the index. It is done on redesign.
- For A, prove point linearity first, or find the program that breaks it
  through links or repeated fields. If it holds, prototype `w_obs`, the eight
  antecedents and λ_r on a copy of soup/ and check that `lf_adequacy` goes
  through. The static guards come after.
- Keep B as the fallback for deciding points created later, should a program
  outside correlated choices need it.

## Literature used

- spies2021transfinite. Theorem 6.2, the existential property for a small type
  (p12), which `exist_prop` mechanizes and which needs the slice to range over a
  small type.
