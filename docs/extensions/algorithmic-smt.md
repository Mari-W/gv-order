# SMT strictness certificates, an experiment

`docs/extensions/algorithmic.md` line 26 proposes

> SMT. Linear arithmetic over offsets. Strictness by a ranking certificate
> (linear or lexicographic) that the solver finds and Rocq checks.

This ran it. The claim that linear arithmetic over offsets cannot state `ult`
dissolves. A second integer measure for the depth is enough, and the solver
both checks and synthesises certificates for every chain example. The
obstruction moves one step. `pt_slot x i = Pt (NSlot (pt_name x) (pt_off x) i) 0`
stores the base offset inside the name, and an abstraction that keeps only the
depth collapses `(ι+3).0` and `(ι+7).0` into one point. Four examples break
there, and the fix is a rank per name family rather than a rank over a pair.

## What was run

z3 5.3.3, 64 bit, installed as the `z3-solver` 5.3.3.0 wheel into a uv venv at
`/tmp/claude-1000/-home-mari-proglang-research-rocq-gvsharp-lr-df/7dd62bf0-d2cb-4552-a789-fb0ae5b5d0a4/scratchpad/smtenv`.
Neither z3 nor cvc5 was on the machine before.

cvc5 1.4.2 (git 282d5e0, built 2026-10-08), the Linux x86-64 static release
binary, downloaded to
`/tmp/claude-1000/-home-mari-proglang-research-rocq-gvsharp-lr-df/7dd62bf0-d2cb-4552-a789-fb0ae5b5d0a4/scratchpad/dl/cvc5-Linux-x86_64-static/bin/cvc5`.
The `cvc5` pip wheel ships no command line binary, only the Python API.

The Rocq Prover 9.2, for the independent check of the synthesised ranks.

63 queries under z3, 63 under cvc5. Driver and queries.

- `/tmp/claude-1000/-home-mari-proglang-research-rocq-gvsharp-lr-df/7dd62bf0-d2cb-4552-a789-fb0ae5b5d0a4/scratchpad/strictness_smt.py`
  writes every query, runs both solvers and prints the table.
- `/tmp/claude-1000/-home-mari-proglang-research-rocq-gvsharp-lr-df/7dd62bf0-d2cb-4552-a789-fb0ae5b5d0a4/scratchpad/queries/`
  holds the 63 `.smt2` files, plus a `.cvc5.smt2` copy of each driver query
  with `(get-model)` stripped. 62 of the 63 come from the driver.
  `B_TailCall_affine_universal.smt2` is hand-written, because the driver emits
  no nonlinear query.
- `/tmp/claude-1000/-home-mari-proglang-research-rocq-gvsharp-lr-df/7dd62bf0-d2cb-4552-a789-fb0ae5b5d0a4/scratchpad/run2.txt`
  is the full transcript, 612 lines, with every solver answer and model.
- `/tmp/claude-1000/-home-mari-proglang-research-rocq-gvsharp-lr-df/7dd62bf0-d2cb-4552-a789-fb0ae5b5d0a4/scratchpad/CheckRanks.v`
  re-checks every synthesised rank by `lia` with no dependency on the
  development. `rocq compile CheckRanks.v` exits 0.

## The obligation

`cc_ok_inner` in `theories/examples/ExampleTools.v` line 650 asks for a
relation `R` on points that is

1. transitive,
2. irreflexive,
3. contains program order, `R x (pt_shift 1 x)` for every `x` whose root is
   the point variable,
4. contains every fact `x ≺ y` of the constraint.

Well-foundedness is not asked for, which matters below. `cc_ok_inner`
discharges no `FEq` fact. It `discriminate`s on them, so the two constraints
with an alias fall outside it and go through `cc_model` directly.

## The two encodings

**A+.** A point is `(v, d, o)`, the point variable, the `NSlot` nesting depth
and the offset.

```
pt_slot x i   ->  (v, d+1, 0)
pt_shift k x  ->  (v, d,   o+k)
```

This is the proposed encoding, with the point variable added so the
two-variable constraints can be stated at all. Without it `ι+k` and `ι′+k`
are the same triple and the fact `ι+k ≺ ι′+k` of `fw_P` is `R x x`.

A+ forgets the base offset. `Pt (NSlot (NVar a) k i) o` is `(a, 1, o)` for
every `k` and every `i`.

**B.** A point is a name family plus the family's `nat` parameters plus the
offset. `Pt (NVar 0) o` is the family `A` at `o`, and
`Pt (NSlot (NVar 0) k 0) o` is the family `S` at `(k, o)`. The rank of a
family is affine in its parameters and its offset, optionally under an integer
level, which makes the rank lexicographic. B keeps the base offset.

Encoding B synthesis runs in two phases, because an unknown coefficient times
a quantified parameter is nonlinear.

- Phase 1 instantiates every parameter over `0..5`, which is LIA, and reads a
  model.
- Phase 2 substitutes that model, so the fully quantified query is LIA again,
  and checks that its negation is unsat.

Phase 1 unsat proves the universal query unsat, because phase 1 asserts
instances. Phase 2 is what turns a phase 1 model into a certificate. The split
earns its keep twice. On TailCall and on the Forwarder box, phase 1 returned a
model that phase 2 rejected.

## The schemas, read out of the source

From `git show exists:theories/examples/<file>` on the `exists` worktree.
`slotv n` and `chv n` are the `n`-fold first carried root of the point
variable, so a point of the chain is `(depth, offset) = (n, o)`.

| file | predicate | facts | certificate written by hand | lemma |
|---|---|---|---|---|
| ReceivedChain.v | `ch_P` | `ι.0ⁿ+1 ≺ ι.0ⁿ⁺¹` | `ch_rank = 2·depth + off` | `ch_ok` |
| Stream.v | `st_P` | `ι.0ⁿ+1 ≺ ι.0ⁿ⁺¹` | `ult` | `st_ok` |
| FactServer.v | `fc_P` | `ι.0ⁿ⁺¹ ≺ ι.0ⁿ`, `ι.0ⁿ⁺¹+1 ≺ ι.0ⁿ` | `dlt` | `fc_ok` |
| KobForwarder.v | `fw_P` | same as `fc_P` | `dlt` | `fw_ok` |
| TailCall.v | `tcc_P` | `ι+k ≺ ι.0` | `lexlt` on `(slot flag, off)` | `tcc_ok` |
| Forwarder.v | `fp_P` | `ι+k ≺ (ι+k).0`, `(ι+k).0 ≺ ι+k+1` | `fwa_rank`, case on the name | `fwa_ok` |
| Forwarder.v | `fwb_P` | 5 families, one alias | `cc_model` with an explicit `φ` | `fwb_ok` |
| Forwarder.v | `fw_P` | 4 families, one alias | none, see below | none |
| Relay.v | `relc_P` | 2 facts plus 6 per `k` | `relv_rank = base(name) + step(name)·off` | `relc_ok` |
| Congruence.v | `cgc_P` | 2 facts | `cg_rank` | `cgc_ok` |
| Delegation.v | `dl_P` | 2 facts | `dl_rank` | `dl_ok` |

Two corrections to the transcription I was given. ReceivedChain does not use
`ult`, it uses the `ℕ` rank `2·depth + off`, which contradicts the note in
`LitTools.v` lines 88 and 89 that neither order has a rank in `ℕ`. The claim
holds of `ult` as a relation and fails for the job `ult` is used for.
Forwarder's `fw_C`, the box constraint of `fwd` with two point variables and
the alias, has no `cc_ok` anywhere in the development. Only `fp_C` and `fwb_C`
do, and `fwb_ok` goes through `cc_model`, not through a rank.

`relc_P` also expands differently from what a reading of the file header
suggests. `c0 x y` emits six facts, so `relc_P` is

```
ι ≺ ι.0,  ι.0 ≺ ι+1,
ι+k+1 ≺ (ι+k).0+1,  ι+k+1 ≺ (ι+k+1).0,  (ι+k+1).0 ≺ ι+k+2,
(ι+k+1).0 ≺ (ι+k).0+1,  (ι+k).0+1 ≺ ι+k+2,  (ι+k).0+1 ≺ (ι+k+1).0+1
```

for every `k`. The last fact is the one that kills encoding A+.

## Verdict per example

`check` is "given the hand-written certificate, does the solver verify every
obligation". `synth` is "without the certificate, does the solver find one".
Both solvers agree on every entry of this table.

| example | A+ check | A+ synth linear | B synth affine | verdict |
|---|---|---|---|---|
| ReceivedChain | `ult` yes, `dlt` no | `2·d + o` | `2n + o` | both encodings work |
| Stream | `ult` yes, `dlt` no | `2·d + o` | `2n + o` | both encodings work |
| FactServer | `dlt` yes, `ult` no | `-2·d + o` | `-2n + o` | both work, linear is enough |
| KobForwarder | `dlt` yes, `ult` no | `-2·d + o` | `-2n + o` | both work, linear is enough |
| TailCall | `ult` yes, `dlt` no | spurious | affine no, lex yes | A+ works, B needs a level |
| Forwarder `fp_P` | neither | unsat | `rA(o) = -1+2o`, `rS(k,o) = 2k+o` | A+ too coarse, B works |
| Relay `relc_P` | neither | unsat | `rA(o) = -1+3o`, `rS(k,o) = 3k+4o` | A+ too coarse, B works |
| Forwarder `fw_P` | neither | spurious | four ranks, alias as equal rank | A+ too coarse, B gives the necessary condition |
| Forwarder `fwb_P` | neither | unsat | four ranks, alias as equal rank | A+ too coarse, B gives the necessary condition |
| Congruence `cgc_P` | n/a, finite | n/a | two ranks | B works |
| Delegation `dl_P` | n/a, finite | n/a | two ranks | B works |

### Checking succeeds wherever the certificate is the right one

`A_Stream_check_ult.smt2` asserts the negation of the conjunction of
transitivity, irreflexivity, program order and the schema fact, with `ult`
inlined as a `define-fun`. Quantified LIA, two lines of certificate.

```
$ z3 queries/A_Stream_check_ult.smt2
unsat
$ cvc5 queries/A_Stream_check_ult.cvc5.smt2
unsat
```

The same for `A_FactServer_check_dlt.smt2` and `A_KobForwarder_check_dlt.smt2`.
Swapping the certificate gives `sat`, the countermodel, as it should.
`A_Stream_check_dlt.smt2` and `A_FactServer_check_ult.smt2` are both `sat`.
Checking the hand-written certificates is the easy half and the solver does it
in milliseconds, including the transitivity and irreflexivity side conditions
that `lia` discharges in the development.

### Synthesis finds the hand-written rank, and a cheaper one

`A_ReceivedChain_synth_linear_p1.smt2` declares `a`, `b`, `c`, sets
`rank(v,d,o) = a·d + b·o + c·v`, asserts `b > 0` for program order and
instantiates the schema fact over `n ∈ 0..5`.

```
$ z3 queries/A_ReceivedChain_synth_linear_p1.smt2
sat
(
  (define-fun b () Int 1)
  (define-fun a () Int 2)
  (define-fun c () Int 0)
)
$ z3 queries/A_ReceivedChain_synth_linear_p2.smt2
unsat
```

`2·depth + off` is `ch_rank` of `ReceivedChain.v` line 156, recovered without
being told. Phase 2 verifies it under the full universal quantifier.

FactServer and KobForwarder are the interesting ones.

```
$ z3 queries/A_FactServer_synth_linear_p1.smt2
sat
(
  (define-fun b () Int 1)
  (define-fun a () Int (- 2))
  (define-fun c () Int 0)
)
$ z3 queries/A_FactServer_synth_linear_p2.smt2
unsat
```

`-2·depth + off`. The development orders these two examples with the
lexicographic `dlt`, on the stated grounds that the descending depth has no
rank in `ℕ`. That is true of `ℕ` and irrelevant, because `cc_ok_inner` asks
only for transitivity and irreflexivity, and `R x y := rank x < rank y` with
`rank : point → ℤ` has both. An integer linear rank replaces `dlt`, and
`CheckRanks.v` proves the three obligations by `lia`.

Synthesis comes back with the depth ascending for ReceivedChain and Stream,
`a = 2`, and descending for FactServer and KobForwarder, `a = -2`, which is
the behaviour asked for.

### Encoding A+ fails on Relay for one line

`A_Relay_any_order.smt2` leaves `R` uninterpreted, asserts only that it is a
strict order containing program order, and adds the eight fact families. The
last one is

```
(assert (forall ((k Int)) (=> (>= k 0) (R 0 1 1 0 1 1))))
```

which is `R x x`. `(ι+k).0+1 ≺ (ι+k+1).0+1` is a fact between two points that
A+ cannot tell apart, because A+ throws away the base offsets `k` and `k+1`.

```
$ z3 queries/A_Relay_any_order.smt2
unsat
$ cvc5 queries/A_Relay_any_order.cvc5.smt2
unsat
```

Unsat with `R` uninterpreted means no certificate of any shape rescues A+
here. The obstruction is the encoding, not the certificate language.

### Encoding A+ fails on the Forwarder, for a cycle rather than a loop

`fp_P` has `ι+k ≺ (ι+k).0` and `(ι+k).0 ≺ ι+k+1`. In A+ both slot points are
`(0,1,0)`, so the pair reads `R (0,0,k) (0,1,0)` and `R (0,1,0) (0,0,k+1)` for
every `k`. Take `k = 5` on the first and `k = 0` on the second. Transitivity
gives `R (0,0,5) (0,0,1)`, and program order gives `R (0,0,1) (0,0,5)`.

```
$ z3 queries/A_ForwarderProd_any_order.smt2
unsat
$ cvc5 queries/A_ForwarderProd_any_order.cvc5.smt2
unknown
```

z3 proves it, cvc5 returns `unknown` on the same file. The shaped query agrees
on both solvers. `A_ForwarderProd_synth_linear_p1.smt2` is `unsat` under z3 and
cvc5 alike, so the instantiation over `k ∈ 0..5` already contradicts. `fwb_P`
behaves the same way, because it contains `ε+k ≺ (ε+k).0` and
`(ε+k).0 ≺ ε+k+1`.

### Encoding B works for all of them

The fix is to keep the base offset. `B_ForwarderProd_p1.smt2` gives one rank
per name family, `r_A(o) = c_A1 + c_Aoff·o` and
`r_S(k,o) = c_S1 + c_Sk·k + c_Soff·o`, with program order as `c_off > 0` per
family.

```
$ z3 queries/B_ForwarderProd_p1.smt2
sat
(
  (define-fun c_A_1 () Int (- 1))
  (define-fun c_A_off () Int 2)
  (define-fun c_S_1 () Int 0)
  (define-fun c_S_k () Int 2)
  (define-fun c_S_off () Int 1)
)
$ z3 queries/B_ForwarderProd_p2.smt2
unsat
```

`ι+o` at `-1+2o` and `(ι+k)+o` at `2k+o`. `fwa_rank` of `Forwarder.v` line 233
is `2·off` and `2k+1+2·off`, the same shape with different constants.

Relay comes out as `ι+o` at `-1+3o` and `(ι+k)+o` at `3k+4o`, against
`relv_rank`'s `3+3o` and `3k+4+4o`. All eight fact families plus the two
program orders verify in phase 2.

### TailCall needs a level, and the solver cannot prove that it needs one

`tcc_P = {ι+k ≺ ζ ∣ k ∈ ℕ}` with `ζ = ι.0`. Under A+ the ceiling has depth 1
and every `ι+k` has depth 0, so `ult` discharges it and
`A_TailCall_check_ult.smt2` is `unsat`. The development's `lexlt` on the pair
`(slot flag, offset)` is that same order restricted to the two families.

Under B the affine rank cannot do it. `r_A(k)` grows without bound in `k`
while `r_S(0)` is one number. Phase 1 is `sat` for every finite
instantiation depth, with a constant large enough to clear `0..5`, and phase 2
rejects the model.

```
$ z3 queries/B_TailCall_affine_p1.smt2
sat
...
$ z3 queries/B_TailCall_affine_p2.smt2
sat
```

`sat` in phase 2 is the negation holding, so the candidate is not a
certificate. Asking the existence question directly puts the unknown
coefficient against a quantified `k`, which is nonlinear, and both solvers
give up.

```
$ z3 queries/B_TailCall_affine_universal.smt2
unknown
$ cvc5 queries/B_TailCall_affine_universal.smt2
cvc5 interrupted by SIGTERM.      (60 s timeout)
```

`CheckRanks.v` proves it in three lines with `nia`, by instantiating `k` at
`s - c`. Raising the level to a lexicographic rank is `sat`, with level 0 for
the points of `ι` and level 1 for `ζ`, and phase 2 verifies it.

```
$ z3 queries/B_TailCall_lex_p1.smt2
sat
(
  (define-fun lv_A () Int 0)
  (define-fun c_A_1 () Int (- 6))
  (define-fun c_A_off () Int 1)
  (define-fun lv_S () Int 1)
  (define-fun c_S_1 () Int 0)
  (define-fun c_S_off () Int 1)
)
$ z3 queries/B_TailCall_lex_p2.smt2
unsat
```

### The alias, honestly

`fw_P` of `Forwarder.v` has `(ι+k).0 ≡ (ι′+k).0`, and `fwb_P` has
`(γ+k).0 ≡ (ε+k).0`. A rank-based certificate can state one consequence of an
alias, that the rank is constant on equivalence classes, which is what
`B_ForwarderBox_p1.smt2` and `B_ForwarderB_p1.smt2` assert. Both are `sat`
and both phase 2 checks are `unsat`.

```
$ z3 queries/B_ForwarderB_p1.smt2
sat
(
  (define-fun c_G_1 () Int (- 2))   (define-fun c_G_off () Int 3)
  (define-fun c_E_1 () Int (- 1))   (define-fun c_E_off () Int 3)
  (define-fun c_SG_1 () Int 0)      (define-fun c_SG_k () Int 3)
  (define-fun c_SG_off () Int 1)
  (define-fun c_SE_1 () Int 0)      (define-fun c_SE_k () Int 3)
  (define-fun c_SE_off () Int 1)
)
$ z3 queries/B_ForwarderB_p2.smt2
unsat
```

`γ+o` at `-2+3o`, `ε+o` at `-1+3o`, and both slot families at `3k+o`, which is
the alias. The `fp_C` facts at `γ` are asserted as hypotheses, so the model
accounts for the ambient order the constraint sits in.

This is a necessary condition and not a certificate. `cc_ok` for a constraint
with an `FEq` fact goes through `cc_model` in
`theories/relation/Creation.v` line 593, which wants a map `φ` on points with
`Hφs`, `Hφl`, `Hφr`, the congruences for `pt_shift` and `pt_slot`, and `HCe`,
which sends each alias into the *ambient* equivalence `TE`. Equal ranks do not
give `HCe`. `fwb_ok` builds `fwb_phi` by hand to rename `(ε+k).0` to
`(γ+k).0`, and that renaming is the content of the proof. The solver can tell
you no rank obstruction exists. It cannot produce `φ`.

Dropping the alias changes nothing in the arithmetic.
`B_ForwarderB_noalias_p1.smt2` is `sat` and its phase 2 is `unsat`. So the
alias is not what makes `fwb_P` hard. The quotient is.

## Where the two solvers part

Of the 62 driver queries run under both, 60 agree. The two disagreements are
`A_ForwarderProd_any_order` and `A_ForwarderB_any_order`, where z3 answers
`unsat` and cvc5 answers `unknown`. Both are UFLIA with an uninterpreted `R`
and three universally quantified axioms. The shaped versions of the same
questions agree on `unsat` under both solvers, so nothing rests on the
disagreement.

## What the solver proved and what I concluded

Proved by z3 and cvc5, with the obligation written out in full and the
negation checked.

- `ult` discharges `st_P` and `tcc_P`. `dlt` discharges `fc_P` and `fw_P` of
  KobForwarder. `ult` and `dlt` are strict orders on `(depth, offset)`.
- `2·depth + off` discharges `ch_P` and `st_P`. `-2·depth + off` discharges
  `fc_P` and KobForwarder's `fw_P`. Both were found from the facts alone.
- No strict order on `(variable, depth, offset)` contains program order and
  `relc_P`, and the same for `fp_P` under z3.
- A rank per name family, affine in the family's parameters and the offset,
  discharges `fp_P`, `relc_P`, `cgc_P` and `dl_P`, and satisfies the
  rank-equality consequence of the aliases in `fw_P` and `fwb_P`.
- A lexicographic rank per family discharges `tcc_P`.

Concluded by me, not by the solver.

- The proposed theory is the right one. "Linear arithmetic over offsets" is
  too narrow by one integer, and the fix is to add a second measure. Which
  second measure is the whole question, and the depth is the wrong answer
  for four of eleven constraints.
- The right abstraction of a point for this purpose is the word of base
  offsets along the name, not the length of that word. A+ keeps the length,
  B keeps the word in the cases where the word is bounded. A constraint whose
  depth and base offsets both grow would need the word itself, and nothing in
  the examples does that.
- `LitTools.v` lines 77 to 80 should be weakened. The depth of `dlt`
  descends, which rules out a rank in `ℕ`, and an integer rank exists and is
  simpler than `dlt`. `fc_ok` and `fw_ok` can each become three `lia` calls
  on `-2·depth + off`.
- The gap between the solver and the development is not arithmetic. It is
  the quotient. Every rank obligation in the examples is within reach of
  quantified LIA plus a two-phase synthesis loop. The `FEq` facts are not,
  and `cc_model`'s `φ` is where a mechanised pipeline would still need a
  human or a separate search.
- Synthesis needs the two phases. A one-shot query with unknown coefficients
  against quantified parameters is NIA, and both solvers return `unknown` on
  it. A finite instantiation followed by a universal check is LIA on both
  sides and decided in milliseconds, at the cost of a spurious candidate now
  and then, which the second phase catches.
