# Fresh points

E-NewFresh creates a channel at a point that no existing name denotes and
relates that point to known points. It is sound for the logical relation as it
stands. The proof changes no statement of `soundness`, `fundamental`,
`fundamental_proc` or any composition lemma, and it leaves the definition of
world extension ⊑ₒ as it was. Branch `fresh-points`, sharp edges 90 to 92 for
the first stage and 93 to 96 for the second. The second stage lets the facts
speak of every later instant and carried point of the fresh channel, and it
retypes the closed examples with fresh points.

## Why the rule is needed

Every point the base system can name is built from names that exist already.
A point is a constant (a, k), a point variable with an offset, or a carried
point x.i of some point x. So no point lies strictly between two given points
unless the context already says so. `new : ∗ ⊸^⊥_⊤ S@ι ⊗ S′@ι` asks ι known in
Γ and gives the channel the point ι itself.

A box generic over ι κ with the constraint ι ≺ κ shows the gap. Its body holds
c at ι and e at κ, creates d, acts on c while it holds d and e, acts on d while
it holds e, and finally acts on e. The point δ of d needs ι ≺ δ ≺ κ. Program
order gives ι ≺ ι+1, but ι+1 ≺ κ does not follow from ι ≺ κ. A carried point
ι.i or κ.i is unrelated to both. `fb_between_underivable` in
examples/FreshBetween.v proves that the fact theory of the box body derives
ι ≺ x ≺ κ for no point x at all.

## The rule

```
ι fresh      C a set of facts u ≺ p and q ≺ v, with p and q points of ι and
             u and v points known in Γ
for every u ≺ p and q ≺ v in C with q on the name of p at an offset
             at least that of p:  Γ ⊢ u ≺ v                       (betweenness)
Θ; Δ, x : S@ι, y : S̄@ι ⊢^F_{Γ, C} t : U      ι not free in Θ, Δ, F, U
──────────────────────────────────────────────────────────────── E-NewFresh
Θ; Δ ⊢^F_Γ let (x, y) = new ∗ in t : U
```

A point of ι is a point whose root is ι. That is ι+k, a carried point
(ι+b).i+k, a carried point of a carried point, and so on. C may be infinite,
for example {ι+k ≺ κ ∣ k ∈ ℕ}. The Rocq constructor is `t_newfresh` in
static/Typing.v.

```
| t_newfresh Φ Ψ Θ Δ F e T S C :
    fresh_ok C →
    Forall (skn W Ψ) (bc_env C) →
    (∀ u p q v, fresh_lo C u p → fresh_hi C q v → ple p q →
       slt W Ψ (fresh_outer C u) (fresh_outer C v)) →
    typed W (fhyps_pinst (pshift 1) Φ)
      (hyps_inst (pshift 1) Ψ ++ [(bcs_inst (pshift 1) C, ids 1)])
      (tenv_pinst (pshift 1) Θ)
      (Some (TSess (dual S) (pvar 0)) :: Some (TSess S (pvar 0)) :: lenv_pinst (pshift 1) Δ)
      (sf_pinst (pshift 1) F) e (pinst_ty (pshift 1) T) →
    typed W Φ Ψ Θ Δ F (LetP (App ENew EUnit) e) T
```

C is a box constraint with one variable, the variable 0 for ι, and its outer
points `bc_env C` (static/PointSubst.v). `fresh_lo C u p` is a fact u ≺ p of C
with p rooted at ι and u rooted at an outer point, `fresh_hi C q v` the mirror
fact q ≺ v. `fresh_ok C` says that every fact of C is one of the two.
`fresh_outer C u` reads u in the context of the rule. `ple p q` says that p and
q have the same name and the offset of p is at most that of q.
`t_newfresh_lh` in static/Typing.v is the list form of the first stage,
L ≺ ι ≺ H with l ≺ h for every l ∈ L and h ∈ H, and it follows from the rule.

The fresh point ι is a bound point variable, the variable 0 of the body. E-Exp
binds the ιs of a box the same way. Everything the conclusion mentions shifts
past the binder, so ι is free in none of it, and freshness costs no side
condition. C enters the body as one more box hypothesis with ι as its
instance. The static system reads hypotheses already, so the body sees the
facts of C through `slt` and sees ι and its carried points as known through
`skn`. The body can then send on the new channel, create further channels at ι
or ι.i and pass ι to a force. `slt_hyp_fresh` reads a fact of C off the
hypothesis, and `slt_fresh_l` and `slt_fresh_r` do the same for the list
form.

The term is the let form of new with both ends bound. A bare `new ∗` in another
position keeps E-Const, which still needs its point known.

## What C may say

Every fact of C relates one point of ι to one outer point, in either direction
(sharp edges 93). In the first stage the point of ι was ι itself. Now it is
any point of ι, and C may hold infinitely many facts.

C has no ≡ fact. An alias ι ≡ x merges ι with an existing point, and E-Const at
x already does that. C has no fact between two points of ι either, such as
ι ≺ ι.0. Such a fact orders the fresh channel against its own carried points,
and betweenness would then have to follow paths that run inside ι. Delegation
and received chain need exactly these facts, so they keep their constants
(see the table below).

## Betweenness

Betweenness is the soundness condition. The world W of a run knows more facts
than Γ. Put ι between l and h while Γ does not derive l ≺ h. Then W may hold
h ≺ l, and l ≺ ι ≺ h ≺ l closes a cycle that no single thread sees.

With betweenness every path through ι enters from some l and leaves to some h,
and W has l ≺ h already. A cycle through ι therefore shortens to a cycle in W,
and W is strict. Putting ι only below some points, or only above some, needs no
clause, because no path then passes through ι. An empty L or an empty H makes
betweenness vacuous.

With facts on all points of ι the condition reads as follows. A path enters ι
by a fact u ≺ p and leaves by a fact q ≺ v. Inside ι it can move only along
program order of one name, from p to p+1 and further. C has no fact between
two points of ι and W knows nothing about ι, and a carried point (ι+b).i is
unrelated in order to ι+b. So the path can leave at q exactly when q has the
name of p and an offset at least that of p, and betweenness asks Γ ⊢ u ≺ v for
every such pair (sharp edges 94). The task statement also let the path pass
from a point to its carried points. That step does not exist in any world, so
the condition above is the exact one. For C = {ι ≺ δ} ∪
{δ+k ≺ κ ∣ k ∈ ℕ} it asks ι ≺ κ once for every k, and program order between δ
and δ+k is what makes every k count.

## Semantics

At O-New the logical relation picks a fresh constant a and a world W′ with
W ⊑ₒ W′ placing a. E-NewFresh picks W′ as W plus the facts L ≺ (a, 0) ≺ H, with
L and H read in W through the substitution of the enclosing boxes
(`wext_fresh_between` in rules/FreshRules.v). The world `Wb` generates these
facts, and `blt` gives its order in closed form. A pair is in the order when W
orders it, when the left point lies at or below some l and the right point is
(a, k), or when the left point is (a, 0) and the right point lies at or above
some h. Strictness of `Wb` and the absence of new facts between old points are
then case analyses on `blt`, and betweenness closes the one case that would
leave W.

The definition of ⊑ₒ needs no change. Today it already lets the fresh constant
relate to old points. It forbids only new facts between two old points, and
betweenness guarantees exactly that. E-Const uses the same freedom for its
alias (a, 0) ≡ ι. So `fresh_extension`, `wext_fresh_join`, P-Connect and every
lemma about ⊑ₒ apply unchanged (sharp edges 91).

The general rule uses `wext_fresh_between_gen`. Its facts are two relations,
`Lo x p` for x ≺ p and `Hi q y` for q ≺ y, with p and q rooted at a. The order
of the generated world `Wg` has four forms in closed form (`gblt`). A pair
(u, v) is in it when W orders it, when u lies at or below some x with Lo x p
and v follows p in program order, when u precedes some q with Hi q y and v lies
at or above y, or when u precedes q with Hi q y, y lies at or below x with
Lo x p, and v follows p. Transitivity is a table of sixteen cases. Betweenness
closes the four cases where a path leaves a after entering it, and the cases
where an a-point would lie at or below a known point are impossible.

The semantic rule `sr_newfresh` in rules/SemanticRules.v takes the two
relations with the fresh point written as the variable 0. It asks the
continuation to be good in every later world W₁ that knows (a, 0) and has
x ≺ `pfresh a p` and `pfresh a q` ≺ y. `pfresh a` puts a in place of the
variable. It keeps offsets and carried points and is injective on points rooted
at the variable, so the order between two of its results is the order between
the templates (`pfresh_ple`). `sem_typed_newfresh` proves the composite good.
Its proof steps through new by hand, picks the world above, then steps through
the let by `Erel_det_beta` and hands the two channel ends to the body. The case
of `typed_sem_rules` reads C at σ and the fresh constant (`open1_comp`,
`pt_inst_outer`) and proves the hypothesis of the body from the two relations
(`bcs_hold_fresh_intro`).

## What changed in the proofs

| File | Change |
|---|---|
| rules/FreshRules.v | new, 305 lines. `Wb`, `blt`, `glt_blt`, `Wb_strict`, `Wb_fresh`, `wext_fresh_between`, `comp_single_one`, `comp_single_both`, `sem_typed_newfresh` |
| rules/SemanticRules.v | constructor `sr_newfresh` and its case of `sem_rules_fundamental`, 15 lines |
| static/PointSubst.v | `fresh_bcs`, `fresh_open`, `fresh_hold`, `bcs_inst_fresh`, and composition and extensionality of `tenv_pinst` and `sf_pinst`, 116 lines |
| static/Typing.v | constructor `t_newfresh`, `slt_fresh_l`, `slt_fresh_r`, 35 lines |
| static/Fundamental.v | one case each in `typed_term_wf_s`, `typed_sem_rules` and `typed_pinst`, four small equations, 105 lines |
| examples/FreshBetween.v | new, 302 lines |

The second stage added to rules/FreshRules.v the section `between_gen`
(`Wg`, `gblt`, `glt_gblt`, `Wg_strict`, `Wg_fresh`), `wext_fresh_between_gen`,
`pfresh` with `pfresh_ple`, and the general `sem_typed_newfresh`. It added to
static/PointSubst.v `fresh_lo`, `fresh_hi`, `fresh_ok`, `fresh_outer`,
`pt_inst_outer`, `open1_comp`, `bcs_hold_fresh_intro` and `slt_hyp_fresh`, and
to static/Typing.v `t_newfresh_lh`. The three cases in static/Fundamental.v
read the general constraint. examples/FreshTools.v, FreshMany.v and six
*Fresh.v files are new.

No other file changed. No statement changed. The case of `typed_sem_rules`
follows the case of E-Exp. It instantiates ι with the fresh constant and the
outer variables with σ, and `plist_pup_shift` cancels the shift. The case of
`typed_pinst` follows E-Exp under `pup 1 σ`.

## Examples

examples/FreshBetween.v holds the motivating example.

```
between : □(∀ι κ. {ι ≺ κ}. ∗ ⊸^⊥_⊤ Close@ι ⊗ Close@κ ⊸^κ_⊤ ∗)
between = !(f = λp. let (c, e) = p in
                    let (d, d′) = new ∗ in
                    let () = spawn (λu. let () = u in close d′) in
                    let () = close c in let () = close d in close e)

main = let (f, u) = ⟨between, ∗⟩ in let () = u in
       let (c, c′) = new ∗ in let (e, e′) = new ∗ in
       let () = spawn (λu. let () = u in close c′) in
       let () = spawn (λu. let () = u in close e′) in
       (force f) ⟨c, e⟩
```

- `fb_typed` types the box with E-NewFresh at L = [ι] and H = [κ]. Betweenness
  is the box hypothesis ι ≺ κ.
- `fb_between_underivable` shows that no point x of the box context has
  ι ≺ x ≺ κ. A relation that contains every derived fact and admits no such x
  witnesses it. The step from there to the failure of E-Const on the body is
  argued here in prose. E-Const gives d its point x itself, close c then asks
  ι ≺ x, close d asks x ≺ κ, and E-Conv moves x only along ≡, which relates
  point variables by equality alone.
- `fb_main_typed` types main with E-Const at (0, 0) and (1, 0) in any world that
  orders the two, and `fb_deadlock_free` applies `soundness` at the world with
  the one fact (0, 0) ≺ (1, 0).
- `fb_main_typed_fresh` types the same main with E-NewFresh for both top-level
  news, c at a fresh γ with L and H empty and e at a fresh ε with L = [γ]. The
  program then needs no constant and no fact, and `fb_deadlock_free_empty`
  applies `soundness` in the empty world `Wpo []`. This is the second example
  of the task. Fresh points remove the constants and facts that a closed
  program otherwise states in its world.

examples/FreshMany.v holds the example of the second stage. The box has the
type of `between`, and d acts three times between ι and κ.

```
many = !(f = λp. let (c, e) = p in
                 let (d, d′) = new ∗ in
                 let () = spawn (λu. let () = u in
                                     let (v, d′) = recv d′ in let () = v in
                                     recvclose d′) in
                 let () = close c in
                 let () = close (send ⟨∗, send ⟨∗, d⟩⟩) in close e)
```

- `fm_typed` types the box with C = {ι ≺ δ} ∪ {δ+k ≺ κ ∣ k ∈ ℕ}. The sends block
  at δ and δ+1 and the close at δ+2, each while e waits at κ. The list form
  cannot state δ+1 ≺ κ.
- `fm_deadlock_free` closes it as in FreshBetween.v at the world with
  (0, 0) ≺ (1, 0), and `fm_deadlock_free_empty` with fresh top-level news in
  the empty world.

## The closed examples with fresh points

Each file *Fresh.v next to an example types the same program with E-NewFresh
at some of its top-level news and proves it deadlock free through `soundness`.
The originals are unchanged (sharp edges 95).

| Example | File | Fresh channels | World before | World after | Box constraint |
|---|---|---|---|---|---|
| sync | SyncFresh.v | c, no facts | constant 0 | empty | none |
| cycle | CycleFresh.v | c, then d with γ ≺ ε | constants 0, 1, one fact | empty | none |
| scheduler | SchedulerFresh.v | r₀, then r₂ with γ+1 ≺ ε. r₁ by E-Const at γ | constants 0, 1, 2, one alias, one fact | empty | none |
| request/reply | RequestReplyFresh.v | a, then b with {γ+k ≺ ε+k, ε+k ≺ γ+k+1} | constants 0, 1, infinitely many facts | empty | unchanged |
| tail call | TailCallFresh.v | c with {γ+k ≺ ζ} | constants 0, 1, infinitely many facts | constant 1 for the ceiling ζ, no fact | unchanged |
| relay | RelayFresh.v | d with four facts against (a,0), (a,0)[0], (a,1), (a,0)[0]+1 | constants 0, 1, infinitely many facts | constant 0 and the facts of c on its carried points | unchanged |
| delegation | none | none | constant 0, two facts | unchanged | none |
| received chain | none | none | constant 0, infinitely many facts | unchanged | unchanged |
| forwarder | none | none | constants 0, 1, aliases and facts | unchanged | unchanged |
| factory under □∀ι | none | none | constants 0, 1, two facts | unchanged | unchanged |

Sync, cycle, scheduler and request/reply now hold in the empty world. Tail call
keeps one constant, because its ceiling is a point and no channel. No box
constraint gets simpler. The constraints describe the recursion of a box for
every instance and do not depend on where main creates its channels.

The four examples that keep their worlds do so for three reasons.

- Delegation and received chain. Their facts relate a channel to its own
  carried points, (a,0) ≺ (a,0)[0] in delegation and (a,0)[0]…[0]+1 ≺ (a,0)[0]…[0]
  one level deeper in received chain. C relates a point of ι only to an outer
  point. In delegation d sits at the carried point (a,0)[0] itself, which E-Const
  provides and which must stay that point because the receiver expects it there.
- Forwarder. Its world aliases the carried points of its two channels,
  (b,k)[0] ≡ (a,k)[0] for every k. C has no ≡ fact, and a single ≡ fact would
  not cover the infinite family either.
- Factory under □∀ι. main creates no channel. The box creates its channels at
  the instance points of force, and force asks those points known in the world.

## What stays open

- Facts between two points of ι in C, such as ι ≺ ι.0. Betweenness would have
  to follow paths that run inside ι, and C would need its own strictness.
  Delegation, received chain and relay need such facts.
- ≡ facts in C. The optional part 3 of the second stage, one ≡ fact between ι
  and a known point with E-Const as a special case, was not done. An alias
  ι ≡ x identifies every successor and carried point of ι with those of x, so
  the world needs the alias construction of E-Const (`W0'` in
  rules/TermRules.v) combined with `Wg`. That is a second closed-form
  argument, larger than the one for `Wg` (sharp edges 96).
- A bare `new ∗` outside the let form at a fresh point. Its result type would
  have to bind ι, which no type former of the base system does.
- Inference of L and H. The algorithmic system of algorithmic.md generates
  fresh point variables at new already. It would emit L and H as constraints
  and check betweenness.
- gvsharp-orders.lagda does not describe the rule yet. The author updates it.
