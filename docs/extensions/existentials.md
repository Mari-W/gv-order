# Existential points

Branch `exists`, built on `fresh-points`, sharp edges 97 to 102. Part 1 adds
existential points to the base order-based relation. Part 2 makes ∀ a type
former of its own and □ a plain modality over it. Each part sits in its own
commits. The statements of `soundness`, `fundamental`, `fundamental_proc` and of
every composition lemma are the same as on `fresh-points`.

## Part 1. Existential points

### The type former

```
T ::= … | ∃^ℓ ι₀ … ιₙ₋₁. C. T
```

A value of ∃^ℓ ιs. C. T is a value of T at some instance of the bound points ιs.
An instance is a list xs of points, one per ι, and T[xs/ιs] puts xs in place of
the ιs. The constraint C is a box constraint over the ιs and outer points, the
same kind of constraint □ already carries (sharp edges 65). The instance meets
C when every fact of C[xs/ιs] holds. The lower point ℓ is an outer point or ⊤.
Every channel the value holds lies at or above ℓ, and ℓ = ⊤ means that the
value holds no channel. ℓ is what the frame of a surrounding term sees, because
the points of the value are bound and the frame cannot name them. The Rocq
constructor is `TEx (lb : option point) (n : nat) (C : bcs) (T : ty)` in
types/Types.v, ported from branch `cfst` without its session variables and
branch roots, and heads(∃^ℓ ιs. C. T) = {ℓ} ∖ {⊤}.

### The rules

```
xs known in Γ     C[xs/ιs] holds in Γ     ℓ ≼_Γ heads(T[xs/ιs])
Θ; Δ ⊢^F_Γ t : T[xs/ιs]
──────────────────────────────────────────────────────────── E-Pack
Θ; Δ ⊢^F_Γ t : ∃^ℓ ιs. C. T


Δ(i) = ∃^ℓ ιs. C. T      T not unlimited
Θ; Δ[i ↦ T] ⊢^F_{Γ, C} t : U        ιs not free in Θ, Δ, F, U
──────────────────────────────────────────────────────────── E-Open
Θ; Δ ⊢^F_Γ t : U


Θ₁; Δ₁ ⊢^{F ∪ heads(Θ₂, Δ₂)}_Γ t₁ : ∃^ℓ ιs. C. T₁ ⊗ T₂
Θ₂; Δ₂, x : T₁, y : T₂ ⊢^F_{Γ, C} t₂ : U     ιs not free in Θ₂, Δ₂, F, U
──────────────────────────────────────────────────────────── E-OpenPair
Θ₁, Θ₂; Δ₁, Δ₂ ⊢^F_Γ let (x, y) = t₁ in t₂ : U
```

The constructors are `t_pack`, `t_open` and `t_openp` in static/Typing.v. E-Open
and E-OpenPair bind the ιs as the point variables 0, …, n-1 of the premise and
shift everything else past them, as E-Exp does for the ιs of a box. C enters
the premise as one more box hypothesis with the ιs as its instance. E-Open
opens a variable of Δ in place and comes from `cfst`. E-OpenPair is new. It
opens the scrutinee of a let pair, and E-NewFresh needs exactly this form,
because its term `let (x, y) = new ∗ in t` binds no variable of existential
type (sharp edges 99).

Channel creation gets a second signature. The first one, at a known point x, is
unchanged.

```
new : ∗ ⊸^⊥_⊤ S@x ⊗ S̄@x                        x known
new : ∗ ⊸^⊥_⊤ ∃^ℓ ι. C. S@ι ⊗ S̄@ι               C fresh, betweenness, ℓ ≺ ι in C
```

C is the constraint of the second stage of E-NewFresh (`fresh_ok`). Every fact
of C relates a point of ι to a known outer point, and betweenness asks Γ ⊢ u ≺ v
for every u ≺ p and q ≺ v of C with q at or after p in program order of one
name (sharp edges 94). ℓ is the outer point u of a fact u ≺ ι of C. The Rocq
constructor is `KTNewEx` in `konst_ty`.

### The value clause

```
V^W_n⟦Θ ⊢ ∃^ℓ ιs. C. T⟧ = { v | ℓ ≼_W heads(Θ), and some xs known in W
                                  meets C in W with v ∈ V^W_n⟦Θ ⊢ T[xs/ιs]⟧ }
```

T[xs/ιs] is no subterm of the type, so a value relation by structural recursion
on T cannot call itself there. `Vdef` therefore reads its type under a point
substitution σ, and the clause for ∃ passes the substitution
`pt_inst (plist xs) ∘ pup n σ` to the body. `Vrel` is `Vdef` at σ = `pvar`.
`Vdef_comp` and `Vdef_inst` show that reading T under σ is reading T[σ], and
`Vrel_ex_iff` gives the clause above. The same device lets V-Box read its thunk
through `Vdef` on its body. Before, V-Box read the thunk through the arrow
relation `Vfun` at the instantiated body, and that was correct only while no
λ could lie in V at a type other than an arrow. A λ now also lies in V at an
existential over an arrow (sharp edges 100).

### Semantic rules

rules/ExRules.v proves the three rules good, `sem_typed_pack`,
`sem_typed_open` and `sem_typed_openp`. E-Pack moves E along `Erel_Vsub`, which
turns E at T into E at T′ when every later value of T is a value of T′. E-Open
and E-OpenPair read the witness off V-Ex and hand it to the premise, which is
good at every instance that meets C in every later world.

The existential signature of new is a second case of `Erel_app_new` in
rules/TermRules.v. At O-New the relation picks a fresh constant a. The case
builds the world of the fresh constraint with `wext_fresh_con`
(rules/FreshWorlds.v). That world is a fresh extension W ⊑ₒ W′ placing a, C
holds in it at the instance (a, 0), and ℓ ≺ (a, 0) holds in it because ℓ ≺ ι is
a fact of C. The pair of channel ends at (a, 0) then lies in V-Ex at the
instance [(a, 0)].

### What became derived

E-NewFresh follows from the existential signature of new and E-OpenPair
whenever C has a fact u ≺ ι for the fresh point ι itself.

```
t_newfresh_open    : premises of t_newfresh  and  fresh_lo C u ι  ⟹  E-NewFresh
t_newfresh_lh_open : premises of t_newfresh_lh  and  L ≠ []        ⟹  E-NewFresh, list form
```

Both are lemmas in static/Typing.v. The proof types `new ∗` by E-App at the
signature `KTNewEx` with ℓ = u and opens the result with E-OpenPair. The body
premise is the premise of `t_newfresh` without change.

`t_newfresh` stays a primitive rule. The derivation needs the premise
`fresh_lo C u ι`, a fact u ≺ ι in C, and `t_newfresh` does not have it. The task
said to stop at such a premise and report it (sharp edges 98).

### The fresh-points examples

Every fresh-points example compiles. The ones whose constraint has a fact
below the fresh point itself now go through the derived lemmas.

| File | Fresh channel | Rule now |
|---|---|---|
| FreshBetween.v | d in the box, L = [ι] | `t_newfresh_lh_open` |
| FreshBetween.v | c at the top, L = [] | `t_newfresh_lh` |
| FreshBetween.v | e at the top, L = [γ] | `t_newfresh_lh_open` |
| FreshMany.v | d in the box, ι ≺ δ in C | `t_newfresh_open` |
| FreshMany.v | top-level c and e | as FreshBetween.v |
| CycleFresh.v | c, then d with L = [γ] | `t_newfresh_lh`, then `t_newfresh_lh_open` |
| SchedulerFresh.v | r₀, then r₂ with L = [γ+1] | `t_newfresh_lh`, then `t_newfresh_lh_open` |
| RequestReplyFresh.v | a, then b with γ ≺ ε in C | `t_newfresh_lh`, then `t_newfresh_open` |
| RelayFresh.v | d with (a,0) ≺ δ in C | `t_newfresh_open` |
| SyncFresh.v | c, L = [] | `t_newfresh_lh` |
| TailCallFresh.v | c with only facts above it | `t_newfresh` |

### What broke and how it was fixed

- `Vdef` took the substitution argument. `Vdef_val`, `Vdef_fchans` and
  `Vdef_prim_empty` generalize over it, and every `Vrel_*_iff` rewrites
  `pt_inst pvar` and `pinst_ty pvar` away (`tpt_inst_pvar`, `tinst_pvar`). The
  instantiation algebra the relation needs (`tinst_comp`, `tinst_ext`,
  `tpup_comp`, `tbcs_comp`) moved into types/Types.v. static/PointSubst.v keeps
  its names and proves them from these.
- A proof by induction on T that the relation is invariant under something
  (world extension, point and channel renaming, conversion, the move lemma of
  JunkRenaming.v) now reaches the body of ∃ only at an instance. `ty_ind_ex`
  is induction on the size of T with the hypothesis at every instance of the
  body of □ and ∃. Eight such inductions use it. The lemma `Vrel_lam_inv` (a
  λ is in V only at an arrow) is false now and is gone. The box cases that used
  it apply the induction hypothesis at the instance instead.
- `teqW`, `eqT`, `steq`, `ty_roots`, `pscoped`, `heads` and the transposition
  `tysw` have an ∃ case. `steq` compares ∃ on the nose, as it compares □,
  because the points of both live under a binder.
- `konst_ty` has an eighth constructor. Its inversions in rules/TermRules.v and
  rules/BoxRules.v name one more branch. `konst_ty_sw`, `konst_ty_mono` and
  `konst_ty_pinst` have a case for it, with `fresh_outer_sw` and
  `fresh_outer_inst` moving the lower point.
- `fresh_lo`, `fresh_hi`, `fresh_ok`, `fresh_outer`, `ple`, `pn_root` and
  `pt_root` moved into types/Types.v, because `konst_ty` reads them. The worlds
  of the fresh constraint (`Wg`, `wext_fresh_between_gen`, `pfresh`) moved
  unchanged from rules/FreshRules.v into the new rules/FreshWorlds.v, which
  rules/TermRules.v imports.

## Part 2. ∀ apart from □

### The type formers

```
T ::= … | □T | ∀ι₀ … ιₙ₋₁. C. T
```

□T is the type of a box whose thunk lies in T. A box !e stands for its thunk
λ_. e[!e/x], so □ is a modality over any type and binds nothing. ∀ιs. C. T is the
type of a value that lies in T at every known instance of the ιs that meets C,
in every later world. The constructors are `TBoxM` and `TAll` in
types/Types.v. The boxes of the static system have type □(∀ιs. C. ∗ ⊸^u_⊤ U),
and `TBox n C T` is now a notation for `TBoxM (TAll n C T)`. Every example
builds its box types through that notation and compiles without an edit.

### The value clauses

```
V^W_n⟦Θ ⊢ □T⟧         = { !e | Θ = ∅, e has no channel, thunk(e) ∈ V^W_n⟦∅ ⊢ T⟧ }

V^W_n⟦Θ ⊢ ∀ιs. C. T⟧  = { v | Θ = ∅, v is a value with no channel, and
                              v ∈ V^{W′}_n⟦∅ ⊢ T[xs/ιs]⟧ for every W′ ⊒ W and
                              every xs known in W′ that meets C in W′ }
```

`Vrel_boxm_iff` and `Vrel_all_iff` in relation/LogicalRelation.v state them.
The V-Box of the bundled box is the composite of the two. `Vrel_box_iff`, the
lemma every box proof uses, keeps its statement word for word and is now a
consequence of `Vrel_boxm_iff` and `Vrel_all_iff`.

V-∀ asks the value to hold no channel and to be a value. Without these two
conjuncts a ∀ whose constraint no instance meets would admit every term, and
`Vrel_val`, `Vrel_fchans` and `Vrel_heads_above` would fail. With them
heads(∀ιs. C. T) = ∅, as for □.

### The rules

```
v a value     Δ unlimited
∅; Δ ⊢^F_{Γ, C} v : T        ιs not free in Δ, F
──────────────────────────────────────────────── E-Gen
∅; Δ ⊢^F_Γ v : ∀ιs. C. T


Θ; Δ ⊢^F_Γ t : ∀ιs. C. T     xs known in Γ     C[xs/ιs] holds in Γ
──────────────────────────────────────────────── E-Inst
Θ; Δ ⊢^F_Γ t : T[xs/ιs]
```

The constructors are `t_gen` and `t_inst` in static/Typing.v, and
`sem_typed_gen` and `sem_typed_inst` in rules/ExRules.v prove them good. E-Gen
binds the ιs like E-Exp and E-Open. The value restriction follows Flanagan and
Abadi (1999, Section 5.1), where the body of a polymorphic abstraction over lock
types must be a value. The premise "v is a value" is the syntactic `is_val v`, and λ, a box, a
constant, ∗, a channel and pairs and injections of values qualify. A variable
does not. The semantic proof reads the premise at index n + 1 of the step
index. At a value E there gives V, and at index 0 E holds of every term. The
environment is unlimited and the term environment is empty because a ∀ value
holds no channel.

E-Exp and the signature of force are unchanged in text. Through the notation
they read

```
E-Exp  : … ⊢ !e : □(∀ιs. C. ∗ ⊸^u_⊤ T)
force  : □(∀ιs. C. ∗ ⊸^u_⊤ T) ⊸^{u[xs/ιs]}_⊤ T[xs/ιs]        xs known, C[xs/ιs] holds
```

### What became derived and what did not

- V-Box of the bundled box (`Vrel_box_iff`) is derived from V-□ and V-∀. The
  semantic E-Exp (`sem_typed_box`) and the semantics of force go through it
  and did not change.
- E-Force stays the lemma `typed_force`, E-App at the signature of force, as
  before.
- E-Exp stays a primitive rule (sharp edges 102). It is the introduction of □
  at a type ∀ιs. C. ∗ ⊸^u_⊤ T, and it does not split into an introduction of □
  and E-Gen. Three things block the split. The body of a box names the box
  itself at its full type □(∀ιs. C. …), and the semantic proof is an induction
  on the step index that needs this name only at smaller indices. An
  introduction of □ over an arbitrary T, whose premise types the thunk, only
  knows the thunk at the same index. The ∀ then has to sit inside that
  induction, so it cannot be a separate E-Gen around it. Last, the thunk λ_. e
  ignores its argument of type ∗, and ∗ is linear, so E-Abs does not type the
  thunk.
- The restriction "∀ only directly under □" is gone. No proof needed it. A ∀
  elsewhere is a value with no channel, which V-∀ states and E-Gen guarantees.

### What broke and how it was fixed

- Every function on types has a case for □ and one for ∀ in place of the
  bundled box (`pinst_ty`, `heads`, `ty_roots`, `sren_ty`, `sflip_ty`,
  `sinst_ty`, `sclosed_ty`, `tysw`, `eqT`, `teqW`, `steq`, `pscoped`). The
  old box case moved to ∀, and the case for □ recurses on its body.
- `ty_ind_ex` gives the hypothesis for the body of □ directly and for the body
  of ∀ at every instance. The eight invariance inductions of part 1 now prove
  the □ case from the body and the ∀ case at the instance. The old box case
  becomes the ∀ case almost unchanged.
- Proofs whose bullets followed the order of the cases of the bundled box had
  their bullets reordered, because `naive_solver` now closes the □ case.
- Intro patterns over `ty` name eight branches.

