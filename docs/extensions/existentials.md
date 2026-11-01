# Existential points

Branch `exists`, built on `fresh-points`, sharp edges 97 to 112. Part 1 adds
existential points to the base order-based relation. Part 2 made ∀ a type
former of its own and □ a plain modality over it, and that split was undone
on 2026-11-01. Part 3 adds the lower bound ⊥
and deletes E-NewFresh as a rule. Part 4 lets the constraint of new hold one
alias ι ≡ x and moves every example to the existential signature. Part 5 makes
the constraint of new any acyclic and conservative set of facts and moves the
examples to the empty world. Part 6 starts every source program under a
creation constraint C₀ over top-level point variables. Each part sits in its own commits. The statements of `soundness`, `fundamental`, `fundamental_proc` and of
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
C when every fact of C[xs/ιs] holds. The lower bound ℓ is an outer point, ⊤ or
⊥ (part 3). Every channel the value holds lies at or above ℓ. ℓ = ⊤ means that
the value holds no channel, and ℓ = ⊥ says nothing about where its channels
lie. ℓ is what the frame of a surrounding term sees, because the points of the
value are bound and the frame cannot name them. The Rocq constructor is
`TEx (lb : lbound) (n : nat) (C : bcs) (T : ty)` in types/Types.v with
`lbound := LTop | LBot | LPt x`, ported from branch `cfst` without its session
variables and branch roots. heads(∃^ℓ ιs. C. T) is {ℓ} when ℓ is a point and ∅
otherwise, and ℓ = ⊥ sets the ⊥ flag of part 3.

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
```

The constructors are `t_pack` and `t_open` in static/Typing.v. E-Open binds the
ιs as the point variables 0, …, n-1 of the premise and shifts everything else
past them, as E-Exp does for the ιs of a box. C enters the premise as one more
box hypothesis with the ιs as its instance. E-Open opens a variable of Δ in
place and comes from `cfst`.

### Opening the result of a let pair

A first version had a rule E-OpenPair that opened the existential scrutinee of
a let pair, so that `let (x, y) = new ∗ in t` typed directly. It is gone,
because a let that binds the result of new reaches the same judgment with
E-Open (sharp edges 99). The program is

```
let p = new ∗ in let (x, y) = p in t
```

The calculus has no let of one variable, so the Rocq term `let_new` in
static/Typing.v binds p with a let pair on ⟨new ∗, ∗⟩ and drops the unit.

```
let_new e = let (p, w) = ⟨new ∗, ∗⟩ in let ∗ = w in let (x, y) = p in e
```

E-LetPair binds p at ∃^ℓ ι. C. S@ι ⊗ S̄@ι and w at ∗, E-Let* drops w, E-Open
opens p in place, and E-LetPair splits it. The body e sees x and y at 1 and 0
and the spent p and w as two empty slots at 3 and 2. `let_new_pair e` takes a
body e indexed as under one let pair and shifts its outer variables past the
two slots. The examples write this form.

Channel creation gets a second signature. The first one, at a known point x, is
unchanged.

```
new : ∗ ⊸^⊥_⊤ S@x ⊗ S̄@x                        x known
new : ∗ ⊸^⊥_⊤ ∃^⊥ ι. C. S@ι ⊗ S̄@ι               C fresh, betweenness
```

C is the constraint of the second stage of E-NewFresh (`fresh_ok`). Every fact
of C relates a point of ι to a known outer point, and betweenness asks Γ ⊢ u ≺ v
for every u ≺ p and q ≺ v of C with q at or after p in program order of one
name (sharp edges 94). The lower bound is ⊥ (part 3). Before part 3 it was the outer
point u of a fact u ≺ ι of C. The Rocq constructor is `KTNewEx` in `konst_ty`.

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

rules/ExRules.v proves the two rules good, `sem_typed_pack` and
`sem_typed_open`. E-Pack moves E along `Erel_Vsub`, which turns E at T into E
at T′ when every later value of T is a value of T′. E-Open reads the witness off
V-Ex and hands it to the premise, which is good at every instance that meets C
in every later world.

The existential signature of new is a second case of `Erel_app_new` in
rules/TermRules.v. At O-New the relation picks a fresh constant a. The case
builds the world of the fresh constraint with `wext_fresh_con`
(rules/FreshWorlds.v). That world is a fresh extension W ⊑ₒ W′ placing a, C
holds in it at the instance (a, 0), and every value meets the lower bound ⊥. The
pair of channel ends at (a, 0) then lies in V-Ex at the instance [(a, 0)].

### What became derived

E-NewFresh for the term `let_new e` follows from the existential signature of
new, E-LetPair, E-Let* and E-Open. Part 1 needed a fact u ≺ ι in C for the
lower point. With ℓ = ⊥ (part 3) the premises are those of the old rule.

```
t_newfresh_open    : premises of the old t_newfresh     ⟹  ⊢ let_new e
t_newfresh_lh_open : premises of the old t_newfresh_lh  ⟹  ⊢ let_new e, list form
```

Both are lemmas in static/Typing.v. The proof types ⟨new ∗, ∗⟩ by E-Pair, with
`new ∗` by E-App at the signature `KTNewEx`, and continues as in the section on
opening above. The body premise is the premise of the old rule with two empty
slots between the channel ends and the outer environment.

```
Θ; x : S̄@ι, y : S@ι, _, _, Δ ⊢^F_{Γ, C} e : T
```

### The fresh-points examples

Every fresh-points example compiles, and every fresh channel goes through the
derived lemmas. Each example types a copy of its program in which the fresh
channels are bound by `let_new_pair` (`sync_main_ex`, `tc_main_ex`,
`cycle_main_ex`, `sched_main_ex`, `rr_main_ex`, `rel_main_ex`, `fb_main_ex`,
`fm_main_ex`). The boxes `fb_box` and `fm_box` use `let_new_pair` in place, so
`fb_main` and `fm_main` contain them too.

| File | Fresh channel | Lemma |
|---|---|---|
| FreshBetween.v | d in the box, L = [ι] | `t_newfresh_lh_open` |
| FreshBetween.v | c at the top, L = [] | `t_newfresh_lh_open` |
| FreshBetween.v | e at the top, L = [γ] | `t_newfresh_lh_open` |
| FreshMany.v | d in the box, ι ≺ δ in C | `t_newfresh_open` |
| FreshMany.v | top-level c and e | as FreshBetween.v |
| CycleFresh.v | c, then d with L = [γ] | `t_newfresh_lh_open` twice |
| SchedulerFresh.v | r₀, then r₂ with L = [γ+1] | `t_newfresh_lh_open` twice |
| RequestReplyFresh.v | a, then b with γ ≺ ε in C | `t_newfresh_lh_open`, then `t_newfresh_open` |
| RelayFresh.v | d with (a,0) ≺ δ in C | `t_newfresh_open` |
| SyncFresh.v | c, L = [] | `t_newfresh_lh_open` |
| TailCallFresh.v | c with only facts above it | `t_newfresh_open` |

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

### Undone (2026-11-01)

The author decided to undo the split. No program uses E-Gen or E-Inst. Every
∀ of every example and translation enters by E-Exp and leaves by force, and
the fewest rules that keep the expressiveness are the goal. The type former
is again the bundled box □(∀ιs. C. T), the constructor `TBox n C T` in
types/Types.v. ∀ occurs only directly under □, and the syntax of types now
states this. `TBoxM`, `TAll`, `t_gen`, `t_inst`, `sr_gen`, `sr_inst`,
`sem_typed_gen`, `sem_typed_inst`, `Vrel_boxm_iff`, `Vrel_all_iff` and
`fchans_thunk` are deleted. V-Box has its bundled clause again, and
`Vrel_box_iff` keeps its statement. The statements of `soundness`,
`fundamental`, `fundamental_proc`, `adequacy`, the composition lemmas, the
examples and the translations did not change. The rest of this part records
the split as it was (sharp edges 109).

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

## Part 3. The lower bound ⊥

### The bound and the flag

The lower bound of ∃ has three cases, ⊤, ⊥ and a point. ⊥ is no point. It
occurs in the slot of `TEx` and nowhere else, so no name, fact, world,
substitution or channel position mentions it. Every value meets the bound ⊥
(`lbx_below` in relation/Worlds.v).

A frame of the static system holds a flag that says that the context holds an
unopened value with lower bound ⊥. The flag of a type, `hbot` in types/Types.v,
is set by ∃^⊥ and passes through ⊗ and ⊕. The flag of an environment is
`lenv_bot`. heads(T) keeps its type and returns the points, and the flag is the
rest. The frame is a pair of points and an `fslot`, where `FVar φ` is a frame
variable, `FBot o` is the flag with or without a frame variable, and `None` is
neither. `None` keeps the meaning it had, so the frame `(F, None)` of
`fundamental` reads as before. E-App, E-Pair, E-Let*, E-LetPair and E-Case
type their first premise under `sf_unionb F (heads of the context) (flag of the
context)`, and E-Pair types its second premise under the heads and the flag of
the first component.

A set of heads with the flag lies below no known point. Three comparisons read
that.

- The gate {u} ≺ F fails for every upper point u when F carries the flag. A
  call with upper bound ⊥ never blocks and passes (`ub_below_s`).
- E-Abs asks λ ≼ heads(Θ, Δ), which is false when Δ carries the flag
  (`lb_below_hb`). A closure does not capture an unopened ∃^⊥.
- send asks x ≺ heads(P[x]) of its payload, which is false when P carries the
  flag. A message does not carry an unopened ∃^⊥.

E-Pack at a lower bound ⊤ or a point asks the flag of the packed type to be
off (`lbx_below_h`), and at ⊥ asks nothing. The programs of the examples hold
∃^⊥ only between ⟨new ∗, ∗⟩ and E-Open in `let_new`, where the subterms under a
flagged frame are ∗ and a variable.

### Semantics

The logical relation keeps its frames as sets of points. The flag stands for
the point `pbot` (relation/Worlds.v), whose root is a variable. No world knows
a variable, so no point lies below `pbot` in a well-formed world
(`no_lt_pbot`). A term under a frame that holds `pbot` therefore offers no
entry when it is stable, unless it is at a link. The bind lemma `Erel_bind`
takes `heads_above_x`, which is `heads_above` or `pbot` in the frame of the
redex. In the second case readiness of the redex already rules out every
offered entry, so the context's channels need no bound. `pbot` is a device of
the proof and occurs in no type, world or static frame.

`Vrel_heads_above` and `grounding_heads` hold for a type or an environment
without the flag. The semantic E-App, E-Pair, E-Let*, E-LetPair and E-Case add
`bot_pts` of the flag to the frame of their first premise. The semantic E-Abs
asks the captured environment to carry no flag, and `Erel_app_send` reads the
flag of the payload off its signature.

### What got deleted

- `t_newfresh` (E-NewFresh), the rule of branch `fresh-points`, with its cases
  in `typed_term_wf_s`, `typed_sem_rules` and `typed_pinst`.
- `t_newfresh_lh`. Its term `let (x, y) = new ∗ in t` no longer types, and on
  `let_new` it says what `t_newfresh_lh_open` says.
- `sr_newfresh` in rules/SemanticRules.v and the file rules/FreshRules.v, whose
  only use was `sem_typed_newfresh`. `wext_fresh_between_gen` stays in
  rules/FreshWorlds.v, because `wext_fresh_con` uses it.
- `fresh_lo_var1` and the premises `fresh_lo C u ι` and `L ≠ []` of the derived
  lemmas.

### The rules beyond orders-lr

`typed` has 18 constructors, `orders-lr` has 16. The two beyond are E-Pack
and E-Open. E-Gen and E-Inst were two more until the split of part 2 was
undone. `konst_ty` has 8 signatures, `orders-lr` has 7, and
the one beyond is the existential signature of new. E-NewFresh and E-OpenPair
are lemmas.

### What broke and how it was fixed

- Every function on `TEx` maps the bound with `lb_map` and compares it with
  `lb_rel`. `lbx_below_sw`, `lbx_below_mono`, `lbx_below_conv` and
  `lbx_below_h_pinst` replace the `option` versions in the invariance proofs.
- The send signature reads its condition as
  `if hbot T then False else ∀ h ∈ heads(P[x]), x ≺ h`, so the examples that
  prove it by `cbn` keep their scripts.
- The wrappers `tv_app`, `tv_letu`, `tv_letp` and `tv_pair` of
  examples/ExampleTools.v fold the absence of the flag of the context into
  their boolean side condition, so their premises keep the frames
  `sf_union F …`. `tv_pair` types its second component under `sf_unionb`.
- The translations from PGV and from Padovani and Novara produce no ∃, so
  `hbot_tr`, `lenv_bot_tr`, `hbot_trz` and `erel_bot` clear the flag there.
  PNTranslate.v uses the tactics `bot_false`, `bclean` and `lbhb`.
- `Factory.v` states its helper `Hreq` for every frame, because the second
  component of a pair is typed under `sf_unionb`.

## Part 4. One signature for new, with an alias

### The decision

new keeps one signature, the existential one (decided 2026-11-01). Its
constraint C may hold one alias ι ≡ x, with x a known outer point, next to its
≺ facts. At C = {ι ≡ x}, E-Open on the result of new and E-Conv on the opened
pair move the channel from ι to x. That is the old signature at a known point.

```
new : ∗ ⊸^⊥_⊤ ∃^⊥ ι. C. S@ι ⊗ S̄@ι        C of the allowed form, outer points known,
                                          fresh_between
```

### The allowed form of C

`fresh_lt C` is the form of part 1. Every fact relates one point of ι to one
outer point by ≺. `fresh_eq C w` is the fact ι ≡ w with w an outer point. C is
allowed (`fresh_ok`) when it has the form `fresh_lt`, or when there is one w
with `fresh_eq C w` and every other fact of C is a ≺ fact of that form. The
disjunction says which case holds, so the semantic proof builds its world by
cases and needs no excluded middle. The alias is the plain point variable ι at
offset 0. An alias ι+1 ≡ x is not allowed.

### The condition on the context

`fresh_between plt C` has three parts.

- If C has the form `fresh_lt`, betweenness of sharp edges 94. Γ ⊢ u ≺ v for
  every u ≺ p and q ≺ v of C with q at or after p in program order of one name.
- For the alias ι ≡ w and every u ≺ p of C, Γ ⊢ u ≺ p[w/ι].
- For the alias ι ≡ w and every q ≺ v of C, Γ ⊢ q[w/ι] ≺ v.

p[w/ι] is `fresh_at C w p`. It puts the outer point w in place of ι, so ι+k
becomes w+k and ι.i becomes w.i. With the alias ι has every fact of w. A fresh
extension adds no fact between two known points, and every point of ι is
identified with a known point. So every ≺ fact of C has to hold already of w.
The two alias parts are therefore necessary in every world that holds the
alias, and they imply betweenness whenever the fact theory is transitive and
contains program order. That makes the condition the weakest one for the world
model. At C = {ι ≡ x} C has no ≺ fact, both alias parts are empty, and new asks
only that x is known, which `Forall pk (bc_env C)` says. That was the premise of
the old signature.

### The semantic proof

`wext_fresh_new` in rules/TermRules.v builds the world at the fresh constant a.
Without an alias it is the world of `wext_fresh_con` as before. With the alias
ι ≡ w it is the alias world of the old signature, `wjoin (W0' a x) W` with x the
point of w (`wext_fresh_alias`). In that world every point p[a/ι] is ≡ to
p[x/ι], by successor and slot congruence (`pt_inst_alias_eq`). A fact u ≺ p of C
holds because u ≺ p[x/ι] holds in W and W lies below the new world. The facts
q ≺ v follow the same way, and ι ≡ w is the alias itself. `Erel_app_new` calls
`wext_fresh_new` in place of `wext_fresh_con`, and the rest of its existential
case is unchanged. No closed form of a combined order was needed, because the
alias world already identifies the points of a with known points and C adds no
fact between known points.

### The old behaviour as a lemma

```
t_new_at : strict W → skn W Ψ x →
           Θ; x : S̄@x, y : S@x, _, _, Δ ⊢^F_Γ e : T  ⟹  Θ; Δ ⊢^F_Γ let_new e : T
```

The lemma is in static/Fundamental.v, because it uses `typed_pinst`. It types
⟨new ∗, ∗⟩ with `KTNewEx` at `alias_bcs x` = {ι ≡ x}, opens p with E-Open, reads
ι ≡ x off the new hypothesis and converts the scrutinee of the inner let pair
from S@ι ⊗ S̄@ι to S@x ⊗ S̄@x with E-Conv. The body is the old body shifted past
ι by `typed_pinst`, which asks a strict world. The body sees the spent p and
unit as two empty slots, as in part 1.

### The examples

Every base example creates its channels with `let_new_pair` and types them with
`t_new_at`. The programs changed text, the statements of the deadlock-freedom
theorems did not. The typing lemmas that call `t_new_at`, directly or through a
box, take `strict W` in place of `world_wf W`.

| File | Changed |
|---|---|
| Sync.v, Cycle.v, Delegation.v, Scheduler.v, RequestReply.v, TailCall.v | top-level news |
| Factory.v | the new in `fac`, at (a,0) and at the box variable ι in `faca` |
| Forwarder.v | `fprod` at ι.0, and the two top-level news |
| ReceivedChain.v | `sch` at its carried point, and the top-level new |
| Relay.v | `prod` at ι′, and the two top-level news |
| SchedulerFresh.v | r₁ at the fresh point of r₀ |
| RelayFresh.v, FreshBetween.v, FreshMany.v | the news at known points |
| Rejected.v | the program texts, no proof |

Ordered.v creates no channel. RelayFresh.v matches the environment of its body
by shape and gained the two empty slots of the outer new.

### The translations, and KTNew deleted

`KTNew` is deleted (decided 2026-11-01). `konst_ty` has one constructor for
new, `KTNewEx`, and `Erel_app_new` has one case. Its world comes from
`wext_fresh_new`, which covers the alias. `let_new` and `let_new_pair` moved to
lang/Syntax.v, because both translations produce them.

- PN. `pn_new` translates let a = new() in e to `let_new_pair e′`, and
  `pn_translate` types it by `t_new_at` at the known point B[RCh c] of the
  channel. The body skips the spent p and unit through two entries of `ins`.
  The simulation of PNSimulation.v has two rules for new. `tr_new` relates the
  source let to the encoded let, and `tr_newp` relates the let pair of the two
  ends on both sides. At the source step of new the target creates the channel
  inside ⟨new ∗, ∗⟩ and then takes two β steps, the let pair on ⟨⟨a, a⟩, ∗⟩ and
  the let ∗, to the let pair of the two ends. `post` at a new step admits β
  steps after the step, and `sim_step` takes them, so no intermediate state of
  the encoding enters the relation. `pn_deadlock_free_source`,
  `fibo_deadlock_free_src` and `pipe_deadlock_free_src` kept their statements.
- PGV. new is a constant of PGV and may stand unapplied, so `pgv_eta` maps it
  to `new_tr` = λz. let ∗ = z in let ⟨a, b⟩ = new ∗ in ⟨a, b⟩. `new_tr_typed`
  types it by `t_new_at` at the protocol point of S. No program with new is its
  own translation any more, so pgv/PGVSimulation.v proves
  `pgv_deadlock_free_source`, deadlock freedom of every typed closed program in
  our semantics, with no premise beyond typing. Its relation is the congruence
  generated by k ~ k and k ~ `kon_eta k` on constants. The forward simulation
  runs the administrative steps of λz. k z and of `new_tr` at once. When no
  thread takes a β, new or spawn step, β steps bring each thread of the
  translation to the action of its thread in the program, and a step of the
  translation is then a step of the program. `pgv_ex21_deadlock_free`,
  `pgv_deleg_deadlock_free` and `pgv_link_deadlock_free` use it and kept their
  statements. `pgv_deadlock_free_applied` kept its statement and covers the
  programs without new.

The thread tools that both simulations use (`bstar`, `ectx`, `mrel`, `msb`)
moved from PNSimulation.v to lang/ThreadSim.v.

### What broke and how it was fixed

- `fresh_ok` of part 1 is now `fresh_lt`, and `t_newfresh_open` takes
  `fresh_lt C`. `fresh_lt_no_eq` and `fresh_between_lt` turn its premises into
  those of `KTNewEx`, so the fresh examples kept their scripts.
- `fresh_lo_shape`, `fresh_hi_shape`, `fresh_eq_shape`, `fresh_lt_shape` and
  `fresh_ok_shape` in types/Types.v say that the form of C reads only its facts
  and the length of its environment. `fresh_ok_inst` and `fresh_ok_sw` are now
  one line each. `fresh_at_inst` and `fresh_at_sw` move the alias parts of the
  condition in `konst_ty_pinst` and `konst_ty_sw`, and `fresh_between_mono` does
  it in `konst_ty_mono`.
- With `KTNew` gone, the inversions of `konst_ty` in `Erel_app_new` and the
  other constant lemmas of rules/TermRules.v, in rules/BoxRules.v, in
  `konst_ty_pinst` (static/PointSubst.v) and in `konst_ty_sw`
  (invariance/PointRenaming.v) lost one branch. No statement changed.
- `pgv_translate` at an applied send, recv or close rewrites `comm k` in the
  new clause of `pgv_eta`, and `konst_tr` reads λz. k z off `kon_eta_comm`.

## Part 5. Creation constraints and the empty world

### The premise of new

new keeps its one signature (decided 2026-11-01, approved as an
experiment). Its constraint C is now any set of facts, finite or infinite,
that relate points of ι to each other and to outer points, by ≺ and by ≡.
The premise is the one of static-system.md §5.

```
new : ∗ ⊸^⊥_⊤ ∃^⊥ ι. C. S@ι ⊗ S̄@ι        cc_ok Γ C,  outer points of C known

cc_ok Γ C  =  acyclic      every cycle of Γ + C is a cycle of Γ
              conservative Γ + C ⊢ x ≺ y  implies  Γ ⊢ x ≺ y
                           Γ + C ⊢ x ≡ y  implies  Γ ⊢ x ≡ y
                           for all points x, y without root ι
```

The Rocq constructor is `KTNewEx S C : cc_ok peq plt C → Forall pk (bc_env C)`
in types/Types.v. `cc_ok`, `cc_acyclic` and `cc_conservative` read the facts
of Γ under the binder of ι (`cc_up`, the outer points shift past ι) and add
the facts of C at ι (`cc_eq`, `cc_lt`, which use `bcs_open 1 C`). Γ ⊢ is the
closure `geq`, `glt`, which contains program order and is closed under ≡.
`geq` and `glt` moved from relation/Worlds.v to types/Types.v for this.

Acyclicity is stated relative to Γ. Γ + C has a cycle only where Γ has one.
When Γ is acyclic this is the condition Γ + C ⊬ p ≺ p of static-system.md.
The relative form is the one that survives substitution, because a
substitution may make a hypothesis cyclic, and then the absolute form fails
in the image although nothing about C changed.

### Soundness

relation/Creation.v proves the premise sound. Three lemmas carry it.

- `interp` is the closed form of T + C for a theory T. Let K be a theory
  over the points of the body of new that contains C, agrees with T on the
  outer points through a map g, and has no cycle that T lacks. Then T plus
  the image of C adds no fact between outer points and no cycle. The order
  of T + C has four shapes (`V`), by whether each end is a point of the
  fresh name. A path visits the fresh name at most twice, because every
  piece of a path that leaves the fresh name and comes back closes into T by
  conservativity of K. Transitivity is one lemma over flags b, where b says
  whether a piece is ≺ or ≡ (`V_trans`).
- `wext_cc` is the run-time world. At O-New the relation picks a fresh
  constant a, and W′ is W with the facts of C at a. `interp` at T = W, with
  g reading ι as a, shows that W′ adds no fact between points of other
  names, which is W ⊑ₒ W′, and no cycle, so W′ is strict. `Erel_app_new` in
  rules/TermRules.v calls it in place of `wext_fresh_new`.
- `cc_ok_transfer` moves `cc_ok` along a map of the generators. Instances
  are `cc_ok_mono` (world extension, `konst_ty_mono`), the transposition of
  constants (`konst_ty_sw`) and the substitution of outer points
  (`cc_ok_pinst`, static/PointSubst.v, used by `konst_ty_pinst` in
  `typed_sem_rules` and `typed_pinst`).

The statements of `konst_ty_mono`, `konst_ty_pinst`, `konst_ty_sw`,
`soundness`, `fundamental` and `fundamental_proc` did not change.

### The earlier forms as lemmas

`cc_model` (relation/Creation.v) proves `cc_ok` from a model. A model reads
the points of ι through a map φ that may identify them with outer points,
orders the remaining points of ι by a strict order R that contains program
order, and lists the facts Lo that enter ι from below and Hi that leave it.
Betweenness of Lo and Hi through R is the one condition on Γ. The facts of C
must hold in the model. The model is a closed form of Γ + C, so the least
closure lies inside it.

- `cc_ok_fresh` (static/PointSubst.v). The two forms of part 4 are creation
  constraints. Without an alias φ is the identity and R is program order of
  one name, and the condition is the betweenness of sharp edges 94. With the
  alias ι ≡ w, φ reads every point of ι at w.
- `cc_ok_alias` (static/Fundamental.v). C = {ι ≡ x} is a creation constraint
  in every context. `t_new_at` uses it and keeps its statement.
- `t_new_open` (static/Typing.v) types `let_new e` from `cc_ok` and the outer
  points known. `t_newfresh_open` is its instance at the form of sharp edges
  93.
- `cc_ok_inner` (examples/ExampleTools.v). A constraint whose facts are ≺
  facts between points of ι is a creation constraint when some strict order
  contains program order and the facts.

### The examples in the empty world

Every example whose program creates its channels in main now types in the
empty world `Wpo []`. The facts that were in the world are the creation
constraints of the news. The deadlock theorems kept their statements.

| Example | Creation constraints |
|---|---|
| Sync.v | c with no fact |
| Cycle.v | c with no fact, d with γ ≺ ε |
| Scheduler.v | r₀ with no fact, r₁ by the alias at γ, r₂ with γ+1 ≺ ε |
| RequestReply.v | a with no fact, b with {γ+k ≺ ε+k, ε+k ≺ γ+k+1} |
| Delegation.v | c with {ι ≺ ι[0], ι[0]+1 ≺ ι+1}, d by the alias at ι[0] |
| ReceivedChain.v | c with the box constraint {ι[0]ⁿ+1 ≺ ι[0]ⁿ⁺¹} itself |
| TailCall.v | c with {ι+k ≺ ι[0]}, the ceiling is the carried point ι[0] |
| Relay.v | c with the facts of its own rounds, d with the four facts of round 0 that mention it |
| Forwarder.v | a with the producer constraint, b with {γ+k ≺ ε+k, ε+k ≺ γ+k+1, ε+k ≺ (ε+k)[0], (γ+k)[0] ≡ (ε+k)[0], (ε+k)[0] ≺ ε+k+1} |
| FreshBetween.v, FreshMany.v | as before, and `fb_deadlock_free`, `fm_deadlock_free` now use the typing of the copy |
| SyncFresh.v, CycleFresh.v, SchedulerFresh.v, RequestReplyFresh.v, RelayFresh.v, TailCallFresh.v | the copy of the program reuses the typing of its base file |

Three constraints need what part 4 did not allow. Delegation, received chain
and relay state facts between ι and its own carried points. Tail call takes
its ceiling inside ι, because a world constant is no longer available. Sb
carries no channel, so ι[0] is a point that no channel occupies. Forwarder
needs the infinite family of aliases (γ+k)[0] ≡ (ε+k)[0] between the payload
slots of the new channel and of the older one. Its model reads (ε+k)[0] as
(γ+k)[0].

One example resisted here. Factory.v kept its worlds until part 6 gave it
top-level variables.

- `fac_main`. main creates no channel and so knows no point. The box fac
  returns its session at a point that its type names, and main passes the
  result of force straight to recv. No variable binds that result, so no
  E-Open can hide the point behind ∃, and in the empty world no point can
  be named.
- `fa_main`. The two sessions come from two calls of the box. Neither exists
  when the other is created, and main needs (a,0) ≺ (b,0) and
  (a,1) ≺ (b,0) between them. No creation constraint can state a fact
  between two channels of which neither is in scope at the other's
  creation.

### The factory with an existential result

examples/FactoryEx.v types the factory pattern in the empty world (sharp
edges 120). The box mk is the term `fac` of Factory.v. It creates a channel,
spawns a worker that sends ∗ on one end and closes it, and returns the other
end. The result type hides the point of the handle behind ∃, and E-Pack
introduces it. No other example uses E-Pack.

```
mk : □(∗ ⊸^⊥_⊤ ∃^⊥ ι. {}. (?∗.Close)@ι)                        Tmk0
mk : □(∀ζ. ∗ ⊸^⊥_⊤ ∃^⊥ ι. {ζ ≺ ι, ζ+1 ≺ ι}. (?∗.Close)@ι)      Tmk1

main = let (g, f) = ⟨mk, mk⟩ in
       let p = (force g) ∗ in
       let q = (force f) ∗ in
       let () = recvclose p in recvclose q
```

The two types share one term. At each type new creates the channel with the
constraint of the existential as its creation constraint, {} at Tmk0 and
{ζ ≺ ι, ζ+1 ≺ ι} at Tmk1, both in the list form of `t_newfresh_lh_open`. The
body packs c′ at ⊥ with the opened fresh point as the witness, and the
hypothesis of new proves the constraint at that witness (`hyp_in_fact`).

The let of one variable is the let pair on ⟨e, ∗⟩ and a let ∗, as in
`let_new`. main opens each handle with E-Open right after its let pair, so no
unopened ∃^⊥ sits in a later context. The first call needs no point, because
Tmk0 has no ∀. The second call instantiates ζ with the point of p, which the
hypothesis of the first E-Open makes known. Opening q gives p ≺ q and
p+1 ≺ q, the two facts that recv and close on p need while main holds q.
`fx_deadlock_free` applies `soundness` in `Wpo []`.

The existential is what makes this work. Without it the result type names the
point of the handle. At the type of `faca` that point is the box variable, and
the first call needs a known instance at the start of main, where the empty
world knows no point and no hypothesis exists (`fx_no_first_call`). At the
type of `fac` the point is a constant, which the empty world does not know
either. Factory.v keeps its programs and worlds. The pattern itself no longer
needs W.

### The translations

Neither translation can produce creation constraints in place of its world
without a change that the task forbids.

- PGV. The point of a channel is a function of its session type,
  `tr_ty (PSess s) = TSess (tr_sty s) (ppt s)` (pgv/PGVWorld.v), and the
  bounds of a function type are global priorities,
  `tr_ty (PLolli p q T U) = TLolli (ubp q) (lbp p) …`. PGV's new is a value
  `new_tr` whose type `∗ ⊸ S@ppt S ⊗ S̄@ppt S` names the point outside any
  binder (`new_tr_typed`, pgv/PGVTranslate.v). A function typed where no
  channel exists, such as the argument of (λf. let ⟨a,a′⟩ = new ∗ in … f a …)
  (λx. close x), carries a bound that the gate of E-App later compares with
  the point of a channel created inside the other λ. Neither is in scope at
  the other's creation, so the fact must come from a world. Giving functions
  and payloads ∀ or ∃ types would change `tr_ty` and the statement of
  `pgv_translate`, and E-Gen does not generalize closures that capture
  channels.
- PN. The translation is relative to an anchor point (`good Ψ B`,
  pn/PNWorld.v), and inside a box the anchor is the box variable under the
  hypothesis `Crel`. At the top level the anchor is the root constant of
  `Wpn` (`good_root`). Both examples start with a polymorphic application,
  T-App-Poly, before their first new (`pn_poly'` in `fibo_main` and
  `pipe_main`, pn/PNExamples.v). It forces a box at the root anchor, which
  `typed_force` asks known, and in the empty world no point is known there.
  Supplying the anchor from a prelude new would change the translated term
  and the statement of `pn_deadlock_free`.

### W stays

Part 6 moved Factory and PN to a constraint at program start, and only PGV
keeps a world. W is not removed from `typed` and `ptyped`. The PGV translation needs the
global points of priorities, the PN translation needs one root anchor, and
Factory needs a point that main does not create. `soundness` keeps its
premise `strict W`.

### What broke and how it was fixed

- `KTNewEx` lost `fresh_ok` and `fresh_between` and gained `cc_ok`. The
  inversions name one hypothesis less. `fresh_ok`, `fresh_between` and their
  shape lemmas stay as the forms that `cc_ok_fresh` accepts.
- `konst_ty_mono` and `konst_ty_sw` prove the new case with
  `cc_ok_transfer`, and `konst_ty_pinst` with `cc_ok_pinst`.
- `wext_fresh_new`, `wext_fresh_alias`, the alias world of rules/TermRules.v
  and rules/FreshWorlds.v are gone. `wext_cc` builds the world for every
  creation constraint.
- The helpers of examples/FreshTools.v (`fresh_clean`, `skn_inst`,
  `sf_pinst_none`, `fhyps_pinst_empty`) moved to examples/ExampleTools.v,
  because the base examples use them.
- The typing lemmas of the examples lost their premises on W. They keep
  `strict W` or `world_wf W`, because `t_new_at` and the tactics read it.

## Part 6. A creation constraint at program start

### The decision

A source program starts with top-level point variables ā = 0, …, n-1 under
one constraint C₀ over them (decided 2026-11-01). C₀ states the facts that a
world W stated before, over variables in place of constants. The program is
typed in the empty world `wnil` (static/Fundamental.v) with the hypothesis
(C₀, ā) in Ψ, so a point is known only when its root is a variable of a
hypothesis. Source typing names no constant.

### The theorem

```
soundness_source :  c0_acyclic n C₀  →  prim T  →
                    typed wnil ∅ [(C₀, ids n)] ∅ [] (∅, None) t T  →
                    deadlock_free (∅, {[+ t +]})
```

`c0_acyclic n C₀` says two things. C₀ has no outer points (`bc_env C₀ = []`),
and the closure of its facts with program order, `glt (c0_eq n C₀)
(c0_lt n C₀)`, relates no point to itself. C₀ against the empty context has
nothing to be conservative over, so acyclicity is the whole creation
condition. `prim T` is the premise that P-Term already asks of a closed
thread (`ptyped_closed`). `soundness` keeps its statement and is the
theorem for configurations.

The proof starts the run in the world `wc0 n C₀`. Its names are the constants
0, …, n-1, and its facts are the facts of C₀ with the variable j read as the
constant j. This is the construction of `wext_cc` against the empty world.
`wc0_strict` reads a cycle of `wc0 n C₀` back to a cycle of C₀ through the map
that sends the constant j to the variable j (`gen_map`). `wc0_holds` shows
that C₀ holds at the constants, and `wc0_ext` that `wnil` lies below
`wc0 n C₀`. `typed_sem_rules` then instantiates the variables by the
constants, and `sem_rules_fundamental`, `Prel_term` and `adequacy` finish.

### The programs that needed a world

| Program | n | C₀ | Anchor or session points |
|---|---|---|---|
| `fac_main` (Factory.v) | 1 | no fact (`Cfac`) | the session of every call at a |
| `fa_main` (Factory.v) | 2 | a ≺ b, a+1 ≺ b (`Cfa`) | force at a and at b |
| PN translation (PNTranslate.v) | 1 | `Crel` | the anchor B = a |

`fac_deadlock_free`, `fa_deadlock_free` and `pn_deadlock_free` apply
`soundness_source`. Their statements did not change. The acyclicity proofs
are ranks. `c0_acyclic_rank` (examples/ExampleTools.v) takes a rank into ℕ
that rises along program order and along every ≺ fact, and `vrank w` gives
the variable j the weight w·j. `Crel_acyclic` (pn/PNWorld.v) uses
`c0_acyclic_den` with the denotation and rank that `Wpn_strict` used.

PN needed no new argument. `pn_translate` holds at every anchor B with
`good Ψ B`, and the variable of a box is good under (`Crel`, ids 1)
(`good_box`). The top-level variable starts under the same hypothesis, so
`pn_deadlock_free` calls `pn_translate` at B = a, Ψ = [(Crel, ids 1)]. The
world `Wpn`, its strictness and `good_root` are deleted. `pn_translate`
reads `wnil` in place of `Wpn` and is otherwise unchanged. The constant
`proot` stays as the anchor of unlimited types, whose translation names no
point (`trz_un`).

### PGV stays at its world

The PGV translation cannot move to C₀ without a change to the translation of
types. PGV puts global points into payloads. A payload of send or recv may
name only its own bound slots and constants, because point instantiation does
not enter session types (`kscoped`, `pscoped m P` in static/Typing.v). The
payload of a delegation is `tr_ty (PSess s) = S@ppt s`, and the payload of a
function carries the bounds `upt n` and `lpt n`. With the protocol points
rooted at a top-level variable these payloads would hold a free variable
inside a session type, and `t_konst` rejects them. Relativizing every global
point of a payload to a slot of the carrier, with C₀ aliasing the slot to the
global point, changes `tr_sty` and the payload lemmas of PGVWorld.v and
PGVTranslate.v. That is a redesign of the translation, not a move of facts,
so it waits for the author (sharp edges 111). `pgv_translate` keeps `typed
Wpgv Φ []`, and `pgv_deadlock_free` keeps `soundness Wpgv`. No statement of
PGV changed.

### W stays in `typed`

The world parameter stays in `typed` and `ptyped` (sharp edges 112). P-Term
types a running thread whose environment holds channels at constants. Its
premise `tenv_dual (w_eq W)` and the premise Γ ⊢ k ≡ y of `t_chan` read the
facts of these constants from W. A source judgment without W
would need a second judgment for configurations or a reading of their points
as variables, and `typed` with its world occurs about 460 times in 36 files,
`fundamental_proc` among them. Every source theorem fixes W to the empty world
(`wnil`, or `Wpo []` in the examples, which also has no names and no facts), except the
PGV translation. Knownness of points at source level comes only from
hypotheses.

### What broke and how it was fixed

- Factory.v. `Tfac_body` names the top-level variable `pv 0 0` in place of
  the constant `pc 0 0`. `fac_typed` and `fa_typed` take no world and no
  premise. `faca_typed` holds under every Ψ and reads the knownness of its
  box variable from the last hypothesis. The facts a ≺ b and a+1 ≺ b come
  from the hypothesis through `sl_hyp0`. `Wfa` and `Wfa_strict` are deleted.
- PNWorld.v. `good` reads `wnil`. PNTranslate.v replaces `Wpn` by `wnil` and
  `Wpn_strict` by `wnil_strict`.
- static/Fundamental.v gained `wnil`, `wnil_strict`, `c0_eq`, `c0_lt`,
  `c0_acyclic`, the section `c0_world` and `prim_pinst`.
