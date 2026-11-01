# Fresh points

E-NewFresh creates a channel at a point that no existing name denotes and
relates that point to known points. It is sound for the logical relation as it
stands. The proof changes no statement of `soundness`, `fundamental`,
`fundamental_proc` or any composition lemma, and it leaves the definition of
world extension ⊑ₒ as it was. Branch `fresh-points`, sharp edges 90 to 92.

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
ι fresh      L, H lists of points known in Γ
for every l ∈ L and h ∈ H:  Γ ⊢ l ≺ h                            (betweenness)
Θ; Δ, x : S@ι, y : S̄@ι ⊢^F_{Γ, L ≺ ι ≺ H} t : U      ι not free in Θ, Δ, F, U
──────────────────────────────────────────────────────────────── E-NewFresh
Θ; Δ ⊢^F_Γ let (x, y) = new ∗ in t : U
```

The Rocq constructor is `t_newfresh` in static/Typing.v.

```
| t_newfresh Φ Ψ Θ Δ F e T S L H :
    Forall (skn W Ψ) (L ++ H) →
    (∀ l h, l ∈ L → h ∈ H → slt W Ψ l h) →
    typed W (fhyps_pinst (pshift 1) Φ)
      (hyps_inst (pshift 1) Ψ ++ [(bcs_inst (pshift 1) (fresh_bcs L H), ids 1)])
      (tenv_pinst (pshift 1) Θ)
      (Some (TSess (dual S) (pvar 0)) :: Some (TSess S (pvar 0)) :: lenv_pinst (pshift 1) Δ)
      (sf_pinst (pshift 1) F) e (pinst_ty (pshift 1) T) →
    typed W Φ Ψ Θ Δ F (LetP (App ENew EUnit) e) T
```

The fresh point ι is a bound point variable, the variable 0 of the body. E-Exp
binds the ιs of a box the same way. Everything the conclusion mentions shifts
past the binder, so ι is free in none of it, and freshness costs no side
condition. The facts L ≺ ι ≺ H enter the body as one more box hypothesis,
`fresh_bcs L H`, with ι as its instance. The static system reads hypotheses
already, so the body sees l ≺ ι and ι ≺ h through `slt` and sees ι as known
through `skn`. The body can then send on the new channel, create further
channels at ι and pass ι to a force. `slt_fresh_l` and `slt_fresh_r` read the
two kinds of facts off the hypothesis.

The term is the let form of new with both ends bound. A bare `new ∗` in another
position keeps E-Const, which still needs its point known.

## What C may say

C is two lists. L holds the points below ι and H the points above it. Every fact
of C has the form l ≺ ι or ι ≺ h with l and h known in Γ (sharp edges 90).

C has no ≡ fact. An alias ι ≡ x merges ι with an existing point, and E-Const at
x already does that. C has no fact about ι+k or a carried point ι.i either.
Program order turns l ≺ ι into l ≺ ι+k on its own. A fact ι+k ≺ h would need
its own betweenness clause, and no example asks for one. Carried points of ι
are fresh too, and a sender places a channel at ι.i with new at ι.i, which ι
known makes legal.

## Betweenness

Betweenness is the soundness condition. The world W of a run knows more facts
than Γ. Put ι between l and h while Γ does not derive l ≺ h. Then W may hold
h ≺ l, and l ≺ ι ≺ h ≺ l closes a cycle that no single thread sees.

With betweenness every path through ι enters from some l and leaves to some h,
and W has l ≺ h already. A cycle through ι therefore shortens to a cycle in W,
and W is strict. Putting ι only below some points, or only above some, needs no
clause, because no path then passes through ι. An empty L or an empty H makes
betweenness vacuous.

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

The semantic rule `sr_newfresh` in rules/SemanticRules.v asks the continuation
to be good in every later world W₁ that knows (a, 0) and has L ≺ (a, 0) ≺ H.
`sem_typed_newfresh` proves the composite good. Its proof steps through new by
hand, picks the world above, then steps through the let by `Erel_det_beta` and
hands the two channel ends to the body.

## What changed in the proofs

| File | Change |
|---|---|
| rules/FreshRules.v | new, 305 lines. `Wb`, `blt`, `glt_blt`, `Wb_strict`, `Wb_fresh`, `wext_fresh_between`, `comp_single_one`, `comp_single_both`, `sem_typed_newfresh` |
| rules/SemanticRules.v | constructor `sr_newfresh` and its case of `sem_rules_fundamental`, 15 lines |
| static/PointSubst.v | `fresh_bcs`, `fresh_open`, `fresh_hold`, `bcs_inst_fresh`, and composition and extensionality of `tenv_pinst` and `sf_pinst`, 116 lines |
| static/Typing.v | constructor `t_newfresh`, `slt_fresh_l`, `slt_fresh_r`, 35 lines |
| static/Fundamental.v | one case each in `typed_term_wf_s`, `typed_sem_rules` and `typed_pinst`, four small equations, 105 lines |
| examples/FreshBetween.v | new, 302 lines |

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

## What stays open

- ≡ facts and facts on ι+k or ι.i in C. The rule would need betweenness for
  every pair that a path through those points connects.
- A bare `new ∗` outside the let form at a fresh point. Its result type would
  have to bind ι, which no type former of the base system does.
- Inference of L and H. The algorithmic system of algorithmic.md generates
  fresh point variables at new already. It would emit L and H as constraints
  and check betweenness.
- gvsharp-orders.lagda does not describe the rule yet. The author updates it.
