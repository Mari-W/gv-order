# Recursion via the exponential: the design taken, and the one not taken

The development supports term recursion through the unlimited modality `□T`, whose introduction
form `!e` binds its own occurrence:

```
force (!e) —β→ e[!e/x]          so    fix x.e ≔ force (!e)
```

This is the paper's §4.4 comonadic exponential (Lindley–Morris ESOP'15) made recursive, which
§4.2's footnote 2 explicitly sanctions: *"Alternatively, we can rely on the recursive exponential
from Section 4.2."* The alternative — carrying Lily's separate exponential `!T` alongside a
non-recursive `□T` — was evaluated and rejected. This note records why, and what it would take,
so the decision does not have to be re-derived.

---

## What the paper's §4.2 actually says

Fig. 8 adds intuitionistic variables in a third environment `Γ`, a recursively defined thunk
`(x = e)`, and a call-by-name elimination:

```
v ::= … | x | (x = e)                 e ::= … | let x = e in e
let x = (y = e) in e′ —β→ e′[fix y.e/x]        fix y.e ≔ let y = (y = e) in e
V_n⟦!T⟧ = { (x = e) | fix x.e ∈ E_n⟦T⟧ }
```

**`Γ` holds variables at the underlying type `T`, not at `!T`.** The figure's `!`s do not survive
text extraction from the PDF, but only one reading is type-consistent:

- `fix y.e = let y = (y = e) in e` has the type of `e`, namely `T`.
- The reduction substitutes `fix y.e : T` for `x`, so `x : T`.
- If `x` were at `!T`, that substitution would be ill-typed, since nothing gives `fix y.e : !T`.

So E-IVar is `·; Γ, x : T; · ⊢ x : T`, E-Exp is `·; Γ, x : T; · ⊢ e : T ⟹ ·; Γ; · ⊢ (x = e) : !T`,
and E-Let-Exp binds `x : T` in the body.

## Why that does not fit this mechanization

Two independent mismatches with the machinery in `Typing.v` and `LogRel.v`, neither of which the
`□` route has:

|  | `□` (taken) | Lily `!` (not taken) |
|---|---|---|
| Type of the bound variable | `□T` | `T`, arbitrary |
| Duplicable? | **yes, by its type** — `unlimited (TBang T)` | not by its type; `T` could be `∗ ⊸ ∗` |
| What the β rule substitutes | `!e` — **a value** | `fix y.e` — **not a value** |
| Grounding required | `Vrel j ∅ (TBang T) (EBang eb)` | `Erel j ∅ T (fix y.e)` |

**1. Duplicability is not readable off the type.** `lenv_split`'s contraction rule `lsplit_unl` and
the weakening rule `lwk_drop` fire on entries whose *type* satisfies `unlimited` (`Types.v`). A
Lily `Γ`-variable sits at `T` and must still admit contraction and weakening, so duplicability
would have to be recorded per-binding instead.

**2. `Γ`-variables are bound to terms, not values.** `grounding` (`LogRel.v`) demands
`Vrel n Σ1 T (γ 0)`, and `Vrel_val` says every member of `Vrel` is a value. `fix y.e` is a
`let`, so `is_val` is `false` and it **cannot inhabit any `Vrel`**. Lily therefore needs a second,
term-level grounding no matter how the environment is spelled. The `□` merge commit notes the same
point from the other side: keeping the elimination substitution-free is what let the value-based
grounding carry over unchanged.

`□` sidesteps both because its bound variable is at `□T` (unlimited by type) and its β rule
substitutes the value `!e`. The pieces then line up exactly: grounding at a `□T` binding yields
`Vrel j ∅ (TBang T) (EBang eb)`, which `Vrel_bang_iff` unfolds to
`∀ i < j, Erel i ∅ T (subst1 (EBang eb) eb)` — precisely the induction hypothesis `sem_typed_bang`
consumes.

## What adding Lily's `!T` would require

Should the separate exponential ever be wanted (e.g. to keep a *non*-recursive, normalizing `□`
alongside it), the cheapest faithful route avoids a second de Bruijn namespace by making the
linear/unlimited distinction part of the binding rather than the type:

```coq
Inductive binding := BLin (T : ty) | BUnl (T : ty).
Definition lenv := list (option binding).

Definition bnd_unl (b : binding) : Prop :=
  match b with BUnl _ => True | BLin T => unlimited T end.
```

- `lsplit_unl` / `lwk_drop` / `lenv_unl` fire on `bnd_unl` instead of `unlimited`.
- `grounding` splits by binding: `BLin T` keeps `Vrel n Σ1 T (γ 0)`; `BUnl T` becomes
  `Σ1 = ∅ ∧ ∀ j < n, Erel j ∅ T (γ 0)` — exactly what `fix y.e` satisfies.
- `typed_erec : lenv_unl Δ → typed ∅ (Some (BUnl T) :: Δ) e T → typed ∅ Δ (ERec e) (TExp T)`
  and `typed_lete` binding `Some (BUnl T) :: Δ2`, which makes the β rule type-preserving.
- New syntax `ERec` (binds 1) and `LetE` (binds 1 in the second component), the head rule
  `let x = (y = e) in e′ —β→ e′[fix y.e/x]`, congruence `TStepLetE`, frame `FLetE`, and
  `tstep_lete_inv`.
- `Vdef` gains
  `TExp T1 => Σ = ∅ ∧ ∃ eb, v = ERec eb ∧ fchans eb = ∅ ∧ ∀ j < n, lE (below j) ∅ T1 (LetE (ERec eb) eb)`,
  plus `Vrel_exp_iff` / `Vrel_exp_empty` mirroring the `□` ones, and a `Vrel_unl_empty` case.
- Lemma 4.3 (`sem_typed_erec`) by strong induction on the index — the same shape as
  `sem_typed_bang` — and Lemma 4.4 (`sem_typed_lete`), which `Erel_bind` reduces to the
  `sem_typed_letu` template since `FLetE` is an evaluation frame.

**Cost.** Changing `lenv`'s element type touches `lenv_empty`, `lenv_only`, `lenv_split`,
`lenv_wk`, `lenv_unl`, `lenv_avail`, `lenv_avail_lin`, `grounding`, every `typed_*` rule, and every
`sem_typed_*` lemma that matches on `Some T` — roughly the twelve semantic-typing lemmas plus
`fundamental_term`. The alternative spelling, a genuine third environment `Σ; Γ; Δ ⊢ e : T`, costs
the same and additionally introduces an `IVar` namespace with its own shift/substitution threaded
through `rename`, `subst`, `closed_at`, `allfv`, `freevar`, and every positional `destruct` pattern
in `Progress.v`.

Everything except the two typing rules and the `Vdef` case is modality-agnostic, so the syntax and
semantics sketched above can be added without disturbing `□`.

## Consequence of the choice

`□` is no longer normalizing: `force (!x. force x)` diverges. Nothing in the metatheory depends on
that — the logical relation is step-indexed and the theorem is deadlock freedom, so a diverging
term is simply never `pirred` and `Prel_safe` always lands in the "can step" disjunct. But a future
normalization statement about the `□` fragment is no longer available; that is the one thing the
rejected design would have bought.
