# Design check, the most general E-New at a fresh root

2026-11-21, branch redesign. Write-up only, no change to v2/. Every argument
is on paper. I read the Rocq on redesign-clean3 at bb04f3e, namely
static/Contexts.v (`wf_new`), compat/Redex.v (`Erel_new`), relation/Ranks.v,
types/Worlds.v, relation/Relation.v (`o_new`), compat/SemTyped.v and
static/Fundamental.v (`typed_sem`, the E-New case). The notation is that of
check-layers-open.md. R is a ranked world with rank function ϱ, tree(ρ) is the
tree of the new root, and a context point is a point outside tree(ρ), an
instance of a point of `bc_env C`. `Γ ⊢ x ≺ y` is `slt W Γ x y`. An entry is a
fact `z ≺ v` of C with z a context point and v in tree(ρ), an exit is a fact
`u ≺ y` of C with u in tree(ρ) and y a context point. The last section lists
what was checked and what was not.

## Verdicts

1. The exact condition is "every ranked model of W and Γ has an extension
   that satisfies C". At one model it holds iff the least ranks of tree(ρ)
   stay below every exit. The least ranks are the ones `Erel_new` already
   builds (`rank_base (new_step C) b0`). Two families of extremal models,
   the least model of Γ and models that lift one context point z by an
   ordinal M, turn this into static conditions on heights in the order of Γ.
2. The static premise (gen-new) of section 4 relates each point of
   tree(ρ) to finite sets of points of Γ. It is sound for every C. It is
   exact when each point of tree(ρ) below an exit has finitely many context
   points below it through C, which covers every finite C, up to contexts Γ
   that no ranked world satisfies. For finite C, W and Γ it is decidable by
   longest paths. For infinite C I did not prove it exact. The obvious
   per-pair height condition is unsound for infinite C (section 3).
3. (gen-new) replaces both (wf-new) and (wf-new⁺). (wf-new⁺) is the case
   with singleton sets and a function. Two examples separate them, the
   two-upper-bound example of check-layers-open.md and a two-entry example.
   The proof of (wf-new⁺) is constructive. The proof of (gen-new) takes the
   maximum of finitely many Brouwer trees, which needs a decision of `ole`.
   I recommend letting (wf-new⁺) land, then generalizing the function h to a
   relation, which stays constructive and already accepts the two-upper-bound
   example, and adding finite sets only if a program needs them.
4. rx-chain stays rejected, under every sound E-New. The descent n times is
   also rejected under every sound E-New, and no premise of E-New can change
   that. The obstruction is the box. A box body cannot statically call itself
   at an instance whose point lies below its own, because a model of the box
   hypotheses with the least rank at that point has no model below it
   (section 7). A descent with a static bound d types with d + 1 boxes under
   (gen-new) and (wf-new⁺), and not under (wf-new).

## 1. What the E-New case has to show

The E-New case of `typed_sem` gets a ranked world W1 with `wmodels W1 W` and
an instance σ with `hsat W1 σ Γ`, and has to put `ENew` into
`E^{W1}⟦∃^⊥ 1. Cσ. (S@ι ⊗ S̄@ῑ)⟧`. By `o_new` (relation/Relation.v) the
creation picks, at every W2 ⊒ W1, a session S, a point π and a world W′ ⊒ W2
with `wholds W′ C (π :: env σ)`. Every extension of a model is a model, so the
case holds exactly when

    (Ext)  for every model (R, σ) of W and Γ there are W′ ⊒ R and a point π
           with W′ ⊨ C at (π, env σ)

A model is a ranked world R with `wmodels R W` and `hsat R σ Γ`. `Erel_new`
today proves (Ext) under `wf_new` and ignores Γ.

Two reductions.

- A fresh root suffices. If some point π works, possibly an existing one,
  then the least ranks ℓ of section 2 work at a fresh root. The ranks of the
  tree of π in W′ satisfy every fact of C and program order, so they lie
  above ℓ pointwise by induction on C ∪ po, and every exit that holds for
  them holds for ℓ.
- Every context root can be taken ranked. A fact of Γσ that touches an
  unranked root holds by program order alone (`w_lt` needs `rin` otherwise).
  Ranking that root by offsets keeps every fact of Γσ and W, so it gives a
  model that extends R, and an extension for it is an extension for R.

## 2. The condition at one model

Fix a model. The context ranks are fixed. Define on tree(ρ)

    ℓ(u) = sup ( { ℓ(v) + 1 | v ≺ u ∈ C ∪ po, v ∈ tree(ρ) }
               ∪ { ϱ(z) + 1 | z ≺ u ∈ C, z a context point } )

by well-founded recursion on C ∪ po. This is `rank_base (new_step C) b0` of
`Erel_new`, with b0 the second set. Every rank function of tree(ρ) that
satisfies C ∪ po and the entries lies above ℓ pointwise. So an extension
exists at this model iff

    (a)  C ∪ po is well-founded on tree(ρ)
    (b)  ϱ(z) < ϱ(y) for every fact z ≺ y of C between context points
    (c)  ℓ(u) < ϱ(y) for every exit u ≺ y

(a) is needed because the new ranks satisfy every fact of C, and po alone is
well-founded, so a descending chain of C ∪ po uses infinitely many facts of
C. (Ext) is (a) together with (b) and (c) at every model. That statement reads
ranks, so it cannot be a premise. The rest of this file makes it static.

## 3. Heights and two extremal models

Write `x ≺_Γ y` for `Γ ⊢ x ≺ y`. If `≺_Γ` is not well-founded, Γ has no model,
because a descending chain lowers ranks, and (Ext) holds vacuously. Assume it
is well-founded and define

    rk_Γ(y)     = sup { rk_Γ(t) + 1 | t ≺_Γ y }
    ht_Γ(z, y)  = sup { ht_Γ(z, t) + 1 | z ≼_Γ t ≺_Γ y }     when z ≼_Γ y
    rk_C(u)     = sup { rk_C(v) + 1 | v ≺ u ∈ C ∪ po, v ∈ tree(ρ) }
    ht_C(z, u)  = sup ( { ht_C(z, v) + 1 | v ≺ u ∈ C ∪ po, z ≼_C v }
                      ∪ { 1 | z ≺ u ∈ C } )                    when z ≼_C u

with `ht_Γ(z, z) = 0`, and `z ≼_C u` saying that a path of C ∪ po runs from z
into tree(ρ) and through tree(ρ) to u. All four are static. They read `slt`,
the facts of C and program order.

Lemma 1, lower bounds. In every model `ϱ(y) ≥ rk_Γ(y)`,
`ϱ(y) ≥ ϱ(z) + ht_Γ(z, y)`, `ℓ(u) ≥ rk_C(u)` and `ℓ(u) ≥ ϱ(z) + ht_C(z, u)`.
By induction along the orders, because `α + ·` is strictly increasing and
continuous in its right argument.

Lemma 2, extremal models. Instantiate every point variable of Γ by a fresh
constant at offset 0 and rank the constants of W and these by a rank function
of `≺_Γ`. This gives a ranked world, because both rank functions below rise
along every fact of W, every hypothesis and program order.

- (i) The least model, `ϱ = rk_Γ`.
- (ii) For a context point z and an ordinal M ≥ rk_Γ(z), rk_Γ(y), the lifted
  model `ϱ_M(x) = max(rk_Γ(x), M + ht_Γ(z, x))`, with the second term only
  when `z ≼_Γ x`. Then `ϱ_M(z) = M`, and `ϱ_M(y) = M + ht_Γ(z, y)` when
  `z ≼_Γ y` and `ϱ_M(y) = rk_Γ(y) ≤ M` otherwise.

Proposition 3, necessity. If Γ has a model and (Ext) holds, then

    (N-a)  C ∪ po is well-founded on tree(ρ)
    (N-b)  Γ ⊢ z ≺ y for every fact z ≺ y of C between context points
    (N-c)  rk_C(u) < rk_Γ(y) for every exit u ≺ y
    (N-d)  z ≼_Γ y and ht_C(z, u) < ht_Γ(z, y)
           for every exit u ≺ y and every context point z with z ≼_C u

Proof. (N-c) at the least model, with Lemma 1 for ℓ. (N-d) at the lifted
model for z. There `ℓ(u) ≥ M + ht_C(z, u) ≥ M`. If z ⋠_Γ y then
`ϱ(y) ≤ M ≤ ℓ(u)` and (c) fails. Otherwise (c) reads
`M + ht_C(z, u) < M + ht_Γ(z, y)`, and left addition cancels under `<`.
(N-b) at the lifted model for z in the same way. ∎

Proposition 4, sufficiency for finitely many sources. Suppose every point u
below an exit has finitely many context points z with `z ≼_C u`. Then
(N-a) to (N-d) imply (Ext). With finitely many sources,

    ℓ(u) = max ( rk_C(u), max_z (ϱ(z) + ht_C(z, u)) )

because a finite maximum commutes with `+ 1` and left addition is
continuous, so both sides satisfy the recursion of ℓ. Each term stays below
ϱ(y) at every model by Lemma 1 applied to rk_Γ and ht_Γ. ∎

The finiteness is needed. With infinitely many sources the per-pair
conditions are unsound.

    Γ   z_k ≺ a_k ≺ b_k ≺ y      for every k, the z_k pairwise unrelated
    C   z_k ≺ v                  for every k
        v ≺ y

Here `rk_C(v) = 0 < 3 = rk_Γ(y)` and `ht_C(z_k, v) = 1 < 3 = ht_Γ(z_k, y)` for
every k, so (N-a) to (N-d) hold. The model `ϱ(z_k) = k`, `ϱ(a_k) = k + 1`,
`ϱ(b_k) = k + 2`, `ϱ(y) = ω` gives `ℓ(v) = sup (k + 1) = ω`, which is not below
`ϱ(y)`. The successor is not continuous, and Proposition 4 fails without the
maximum.

## 4. The rule

    π = ρ  ⇒  (i)   C ∪ po is well-founded on tree(ρ)
              (ii)  Γ ⊢ z ≺ y for every fact z ≺ y of C between context points
              (iii) there is a relation S between points of tree(ρ) and
                    nonempty finite sets of points with
                    - for every exit u ≺ y there is (u, T) ∈ S
                      with Γ ⊢ t ≺ y for every t ∈ T
                    - for every (s, T) ∈ S and every step s′ ≺ s of C ∪ po
                      in tree(ρ) there is (s′, T′) ∈ S such that every t′ ∈ T′
                      has some t ∈ T with Γ ⊢ t′ ≺ t
                    - for every (s, T) ∈ S and every entry z ≺ s
                      there is t ∈ T with Γ ⊢ z ≺ t                (gen-new)

The premise reads `slt`, the facts of C and program order, and nothing else.
It names no ordinal.

Proposition 5, soundness. (gen-new) implies (Ext). At a model take ℓ as in
section 2, which exists by (i). By induction on C ∪ po,
`(s, T) ∈ S ⇒ ℓ(s) ≤ max_{t ∈ T} ϱ(t)`. A step `s′ ≺ s` gives
`ℓ(s′) ≤ ϱ(t′_m) < ϱ(t) ≤ max ϱ(T)` for the largest t′_m of T′ and the t
above it, because `ent_sound` (check-layers-open.md, section 3) reads
`Γ ⊢ t′ ≺ t` as `ϱ(t′) < ϱ(t)`. An entry gives `ϱ(z) < ϱ(t)` the same way. At
an exit `ℓ(u) ≤ max ϱ(T) < ϱ(y)`. Facts between context points hold by (ii)
and `ent_sound`. Facts inside tree(ρ) and entries hold by the construction of
ℓ. ∎

Proposition 6, exactness for finitely many sources. Under the finiteness of
Proposition 4, if Γ has a model and (Ext) holds, then (gen-new) holds. By
Proposition 3, (N-a) to (N-d) hold. Let S hold `(s, T)` when T is finite and
nonempty, some t ∈ T has `rk_Γ(t) ≥ rk_C(s)`, and every source z of s has some
t ∈ T with `z ≼_Γ t` and `ht_Γ(z, t) ≥ ht_C(z, s)`. For an exit u ≺ y, (N-c)
and (N-d) give such points below y, because an ordinal below
`ht_Γ(z, y) = sup { ht_Γ(z, t) + 1 | z ≼_Γ t ≺_Γ y }` lies at or below some
`ht_Γ(z, t)`, and likewise for rk_Γ. For a step `s′ ≺ s` the same argument one
level down gives, for each witness t, a point t′ ≺_Γ t with the smaller
height, because `ht_C(z, s′) < ht_C(z, s)` and `rk_C(s′) < rk_C(s)`. For an
entry `z ≺ s`, `ht_C(z, s) ≥ 1` forces the witness t ≠ z, so `Γ ⊢ z ≺ t`. ∎

Exactness fails only on contexts with no model, where (Ext) holds for every
C. Adding the disjunct "`≺_Γ` is not well-founded" would make the rule exact
there too. I do not recommend it. It is a negative premise, and such a box
body is dead code in a closed program. E-Force needs `hold_at` of the box
hypotheses under the forcing context, so a box whose hypotheses have no model
can only be forced under a context with no model, and the derivation of a
closed program starts from `hc_empty` over a well-founded W, which has a
model.

For infinite C, (gen-new) is sound, and I did not prove it exact. Completeness
would need, for a point with infinitely many sources, a finite set of points
of Γ that bounds all their contributions uniformly over all models. The
example of section 3 is rejected by (gen-new), as it must be, because a
finite T reaches only finitely many z_k.

## 5. Deciding (gen-new) for finite C

For finite C, Propositions 3, 4 and 6 say that (gen-new) is equivalent to
(N-a) to (N-d). Those are finitely many questions.

- (N-a). The nodes are the endpoints of the facts of C in tree(ρ). Program
  order relates two nodes iff they have the same name and the second has the
  larger offset, at either polarity. C ∪ po is well-founded on tree(ρ) iff
  this finite graph has no cycle, because po alone raises the offset.
- rk_C and ht_C are longest paths in that graph, with weight 1 on a fact and
  the offset difference on a program-order edge. rk_C(u) adds the offset of
  the lowest node of the path, which counts the program-order chain from
  offset 0.
- (N-b) is `slt`. (N-c) asks a chain `t_0 ≺_Γ … ≺_Γ t_n = y` with
  `n = rk_C(u) + 1`. (N-d) asks a chain from z to y of length
  `ht_C(z, u) + 1`.
- When W and the hypotheses of Γ have finitely many facts, the chain
  questions are longest paths over the endpoints of those facts with the same
  weights, so the whole premise is decidable in polynomial time. When a
  hypothesis has infinitely many facts, as the client-server constraint does,
  the premise is finitely many chain statements, and a derivation proves them
  as it proves `hold_at`. Then it is not decidable in general, and neither is
  `slt`.

## 6. Against (wf-new) and (wf-new⁺)

(wf-new) is (gen-new) with no exits and no facts between context points. S is
empty. (wf-new⁺) gives S = { (u, {h(u)}) | u ∈ D }. D is closed downwards, so
every step below a point of D stays in D, and the three clauses of h are the
three clauses of S. So (gen-new) contains both.

Two examples separate them.

    two upper bounds   Γ  z ≺ y, z′ ≺ y′           C  π ≺ y, π ≺ y′
    two entries        Γ  z1 ≺ w1 ≺ y, z2 ≺ w2 ≺ y  C  z1 ≺ v, z2 ≺ v, v ≺ y

The first needs (π, {z}) and (π, {z′}), two pairs for one point, which a
function h cannot give. The second needs (v, {w1, w2}), because no single point
of Γ lies above both z1 and z2. Both are accepted by (gen-new) and rejected by
(wf-new⁺). Both are sound, by (N-c) and (N-d) with one source each.

An intermediate rule (gen-new₁) takes S between points of tree(ρ) and points
of Γ, a relation in place of the function h. It accepts the first example and
rejects the second. Its proof keeps the invariant `ℓ(s) ≤ ϱ(t)`, which
`ole_lim_l` and `ole_succ_succ` give constructively, exactly as for
(wf-new⁺). Finite sets need `max_{t ∈ T} ϱ(t)` to be one of the ϱ(t), which
on Brouwer trees needs a decision of `ole` and so excluded middle. A set is
needed even with a single source. With `Γ  z ≺ w ≺ y`, `p0 ≺ p1 ≺ p2 ≺ p3 ≺ y`
and the exit `ρ+3 ≺ y` with entry `z ≺ ρ+3`, no single point of Γ lies above z
and has rank at least 3, while `{w, p3}` works.

What the Rocq proof changes. The construction of `Erel_new` stays. The lemma
takes `wmodels W1 W` and `hsat W1 σ Γ`, which the E-New case of `typed_sem`
has (`HW`, `Hs`), proves the invariant by well-founded induction on
`new_step C`, and reads exits through it. O-New and every relation clause stay
as they are. Exits to a context point whose root W1 does not rank are covered,
because `Erel_new` grows those roots with offset ranks and the facts of Γ on
them are program order.

## 7. rx-chain and the descent

### A box cannot descend

Proposition 7. Let a box `□∀ιs. H. U` have a body typed under
`Γ_b = hc_open m H Γ0`, possibly extended in one branch by the constraint of a
creation (opened by E-Open). Suppose that branch forces the box itself at an
instance xs′ with `Γ_b ⊢ H at xs′` (`hold_at`) and `Γ_b ⊢ f(xs′) ≺ f(ιs)` for
some point expression f in the box variables. If the E-New rule of that
branch is sound, then W, Γ0 and H have no common model.

Proof. Among the models (R, σ, xs) of W, Γ0 and H, take one with the least
`ϱ(f(xs))`, which exists because ordinals are well-ordered. Soundness of the
creation's E-New, whatever its premise, gives an extension W′ with the
witness point. `ent_sound` gives `W′ ⊨ H at xs′` and
`ϱ(f(xs′)) < ϱ(f(xs))`, and Γ0σ still holds in W′. So (W′, σ, xs′) is a model
with a smaller value. ∎

A field creation needs no extension, and the same proof applies. A cycle of
calls through several boxes, each body forcing the next at a lower instance,
fails in the same way, with soundness of each creation applied in turn.

### rx-chain

rx-chain (docs/explorer/gen/rejects.js) closes c at π while holding w at ι,
so readiness asks `Γ_b ⊢ π ≺ ῑ`, and the child forces the box at `ι′ = π̄`.
With `f(ι) = ῑ`, Proposition 7 applies, so rx-chain has no derivation under
any sound E-New, (gen-new) included. Statically, with `H = {t ≺ ῑ}`, the exit
`π ≺ ῑ` needs `rk_Γ(ῑ) ≥ rk_C(π) + 1`, and `H at π̄` needs a point below π in
C. A chain of length n below ῑ in H forces a chain of length n below π in C,
and then (N-c) asks n + 1 in H, so H needs every length. Proposition 7 also
covers H with infinitely many facts.

### The descent n times

The variant that creates below its predecessor n times for an input n and then
stops is lock free. Its branch for `n > 0` has the same creation, readiness
fact and recursive force as rx-chain, under the same Γ_b, because a case
split on data adds no fact. Proposition 7 applies, and no premise of E-New
helps. The obstruction is that a box states one H for all calls, and a
recursive call must prove H at a lower instance.

I did not check whether the program is in the relation. At run time the
counter bounds the descent, and the creations can pick ranks n − 1, n − 2, …
below the rank of w̄ once n is known, so I expect it is. If so, the gap is in
E-Box and E-Force, not in E-New.

A static bound d types with d + 1 boxes. Box k has variables ι, t_1, …, t_k
and `H_k = {t_1 ≺ … ≺ t_k ≺ ῑ}`. Its body creates π with
`C = {t_{k−1} ≺ π, π ≺ ῑ}` and forces box k − 1 at `(π̄, t_1, …, t_{k−1})`.
(gen-new) accepts with `S = {(π, {t_k})}`, (wf-new⁺) with `h(π) = t_k`, and
(wf-new) rejects the exit `π ≺ ῑ`. main creates w at ρ with
`C = {ρ·0 ≺ ρ·1 ≺ … ≺ ρ·(d−1) ≺ ρ‾}` inside tree(ρ), which (wf-new) accepts,
and forces box d at `(ρ, ρ·0, …, ρ·(d−1))`.

### The examples of v2

ClientServer, FreshBetween, FreshMany, Cycle, FactoryEx, GrowRing,
Controller and their LF versions create at a fresh root under `wf_new`, so
they satisfy (gen-new) with S empty.

## What was checked and what was not

Checked on paper.

- (Ext) as the exact statement of the E-New case, against `o_new`,
  `sem_typed_at` and the E-New case of `typed_sem`.
- That a fresh root suffices and that unranked context roots can be ranked
  first.
- The least solution ℓ, its identity with `rank_base (new_step C) b0`, and
  conditions (a) to (c).
- Lemmas 1 and 2, Propositions 3 to 7, and the counterexample to the per-pair
  conditions.
- The two-upper-bound, two-entry and set-needed examples, rx-chain, the
  descent and the bounded descent.

Not checked.

- Anything in Rocq. No statement here is mechanized.
- Exactness of (gen-new) for C with infinitely many sources below an exit.
- Whether the descent n times is in the relation.
- That the lifted model of Lemma 2 satisfies the side conditions of `wmodels`
  beyond constants and facts. Its roots are the constants of W and the fresh
  constants, so I expect nothing else.
- Interaction with P-Connect, the live relation (compat/LiveDF.v) and the
  cost relations.
