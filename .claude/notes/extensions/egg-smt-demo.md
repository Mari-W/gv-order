# A congruence-closure stage and an SMT stage, run over the whole example set

This runs the two-stage pipeline `docs/extensions/algorithmic.md` proposes,
over every order obligation the examples state, over the five rejections of
`theories/examples/Rejected.v`, and over the two cases `algorithmic.md` leaves
open. It is not a type checker. It discharges the obligations the development
already writes down.

Three Rocq files come out of it and all three compile against the development
on disk. One of them, `FwbCert.v`, proves
`cc_ok (seqs W Ψ) (slt W Ψ) fwb_C` from the pipeline's output alone, which is
the statement of `fwb_ok` word for word. Another, `RejectCert.v`, proves
`rlo_call_underivable`, a theorem `Rejected.v` line 101 states in a comment
and does not prove.

`docs/extensions/algorithmic-smt.md` is the earlier run this answers. It built
the SMT half and picked the family partition by hand. Stage 1 now reads the
partition off the e-graph, and the two alias constraints it called out as
needing a human do not need one.

## The two obligations

A constraint carries two, not one.

Strictness. `cc_ok` asks that Γ + C be acyclic and conservative, and
`cc_model` (`theories/relation/Creation.v:454`) reduces that to a map `φ` on
points, an order `R` inside the fresh point, and two boundary relations `Lo`
and `Hi`.

Entailment. Each action's premise is a fact `Γ ⊢ x ≺ y`. After stage 1
normalises through `φ`, that is reachability over the normalised `≺` facts
together with the program-order edges, which join two points of one name at a
greater offset. A rejection is a failure of one of the two, and the pipeline
has to say which.

## The table

`hand` names what the development does. `new` says whether the verdict
reproduces an existing hand proof or is not in the development at all.

### The five rejections of `Rejected.v`, which carry theorems

| obligation | stage 1 | stage 2 | Rocq | hand proof | new |
|---|---|---|---|---|---|
| `rr_call` (`Rejected.v:57`) | φ = id, 2 families | countermodel `r_ι = 2o`, `r_ι′ = o+1`, p2 unsat both solvers | `rr_rank'` + obligations by `lia`, accepted | `rr_call_underivable`, `fl_map` into `rr_R` with `10(k+1)` and `15+k` | reproduction, smaller rank |
| `ord_no_constraint` (`Rejected.v:254`) | φ = id, 0 facts | countermodel `r_ι = r_ι′ = o`, p2 unsat both | `ord_rank_goal` by `lia`, accepted | `ord_no_constraint`, `fl_map` into `ord_R` | reproduction |
| `sched_rev` (`Rejected.v:184`) | **merges `z` with `x`**, 2 families | no rank: p1 unsat both, affine and lexicographic | `cert_sched_rev`, accepted | `sched_rev_underivable`, the three facts give `z ≺ z` | reproduction |
| `ms_rev` (`Rejected.v:196`) | φ = id, 3 families | no rank: p1 unsat both | `cert_ms_rev`, accepted | `ms_rev_underivable` | reproduction |
| `badlink` (`Rejected.v:209`) | **merges `x` with `y`**, 2 families | no rank: p1 unsat both | `cert_badlink`, accepted | `badlink_underivable` | reproduction |

The split is clean. Two of the five fail entailment and three fail
strictness, and the pipeline reports the two failures by different routes. On
`sched_rev` and `badlink` stage 1 does the work: the `FEq` fact is what closes
the cycle, and the cycle appears only after the merge.

### The two rejections of `Rejected.v` that carry a comment and no theorem

| obligation | stage 1 | stage 2 | Rocq | hand proof | new |
|---|---|---|---|---|---|
| `relay_one_round` (`Rejected.v:101`) | φ = id, 3 families | countermodel `r_ι = 2o`, `r_ι′ = o+1`, `r_{(ι+_).0} = 2o`, p2 unsat both | **`rlo_call_underivable`, accepted** | comment only | **new theorem** |
| `blocked` (`Rejected.v:119`) | φ = id, 2 families | no rank: p1 unsat both; cycle `x → y → x` | `cert_blocked`, accepted | comment only | new, trivial |

`rlo_call_underivable` is the one worth having. The comment says the rank of
`rr_call_underivable` adapts. It does, and the pipeline found which
adaptation: put `(ι+_).0` on the same rank as `ι`, which makes `ι+1` and
`ι[0]+1` tie and the premise fail.

### The accepted counterpart of each rejection, asked the same question

| obligation | reachability | countermodel | hand proof | new |
|---|---|---|---|---|
| `rq_C` (`RequestReply.v:30`) vs `rr_call` | path `ι+1 → ι′+1`, one fact edge | none, p1 unsat both | `rq_call` by `bcs_hold_self` with `rq_step` | reproduction |
| `rel_C` (`Relay.v:45`) vs `relay_one_round` | path `ι+1 → (ι).0+1`, one fact edge | none, p1 unsat both | `rel_call` by `bcs_hold_self` with `rel_sub` | reproduction |
| `ord_C` (`Ordered.v:21`) vs `ord_no_constraint` | path `ι → ι′`, one fact edge | none, p1 unsat both | the premise is a fact of `ord_C` | reproduction |

The accepted and the rejected version of each program differ in the pipeline
exactly where they differ in the development. The rejected one has no path and
a countermodel; the accepted one has a path and no countermodel.

### The two cases `algorithmic.md` leaves open

| obligation | stage 1 | stage 2 | Rocq | hand proof | new |
|---|---|---|---|---|---|
| the relay of §9.2 | φ = id, 3 families `c`, `c.1`, `z` | affine p2 **sat**, so rejected; lexicographic p1 sat, p2 unsat both | **`relay_M_ok` by `lia`, accepted** | §9.2 Claim, rank `3k+6−1/j` and `ω+j`, not in Rocq | **new certificate** |
| ground G with a delegation round trip, §8.2 | **merges `(c,2).1` with `(c,7).1` at potential −2**; `Hφo` refuses a `φ`, so the alias is ambient | affine p1 **unsat** both, lexicographic p1 **unsat** both; a piecewise rank with one break works, p2 unsat both | **`deleg_rt_ok` by `lia`, accepted** | none, §8.2 calls the criterion open | **new boundary** |

### The eleven `cc_ok` obligations of the examples

Every one is a reproduction. A human chose each constraint so the hand proof
would close.

| obligation | stage 1 | stage 2 rank | hand proof |
|---|---|---|---|
| `ch_C` (`ReceivedChain.v:36`) | 1 family `ι.0^[n]` | `2n + o`, p2 unsat both | `ch_ok`, `ch_rank = 2·depth + off` |
| `st_C` (`Stream.v:58`) | 1 family | `2n + o`, p2 unsat both | `st_ok`, `cc_ok_ult` |
| `fc_C` (`FactServer.v:59`) | 1 family | `−2n + o`, p2 unsat both | `fc_ok`, `cc_ok_dlt` |
| `fw_C` (`KobForwarder.v:60`) | 1 family | `−2n + o`, p2 unsat both | `fw_ok`, `cc_ok_dlt` |
| `tcc_C` (`TailCall.v:99`) | 2 families | affine p2 sat, lexicographic `(0, o)` and `(1, o+6)`, p2 unsat both | `tcc_ok`, `lexlt` on `(slot flag, off)` |
| `cgc_C` (`Congruence.v:90`) | 2 families | `2o−1`, `o`, p2 unsat both | `cgc_ok`, `cg_rank` |
| `dl_C` (`Delegation.v:48`) | 2 families | `3o`, `o+1`, p2 unsat both | `dl_ok`, `dl_rank` |
| `fp_C` (`Forwarder.v:49`) | 2 families | `2o−1`, `2k+o`, p2 unsat both | `fwa_ok`, `fwa_rank` |
| `relc_C` (`Relay.v:184`) | 2 families | `3o`, `3k+4o+1`, p2 unsat both | `relc_ok`, `relv_rank` |
| `fw_C` (`Forwarder.v:44`) | **1 merge**, 4 families down to 3 | `2o−1`, `2o`, `2k+o+1`, p2 unsat both | none: `fw_C` is a box constraint, never the constraint of a `new` |
| `fwb_C` (`Forwarder.v:227`) | **1 merge**, 4 families down to 3, φ matches `fwb_phi` | all four facts cross the boundary, so `R` carries program order only, `r = o` | `fwb_ok`, `cc_model` with `fwb_phi`, `R = pofs`, explicit `Lo`/`Hi` |

### The fresh route

`cc_ok_fresh` (`theories/static/PointSubst.v:559`) is `cc_model` with `φ = id`,
`R = pofs` and `Lo`/`Hi` read off the facts by the root test. Stage 1
reproduces that reading, and stage 2 has nothing to do, because no fact stays
inside `ι`.

| obligation | stage 1 | facts inside `ι` after φ | hand proof |
|---|---|---|---|
| `reld_C` (`Relay.v:191`) | φ = id, 3 families | 0 | `t_newfresh_open`, `fresh_ok` and `fresh_between` by hand |
| `fresh_bcs L H` (`PointSubst.v:1051`) | φ = id | 0 | `cc_ok_fresh`, used at 14 `t_newfresh_lh_open` sites |
| `alias_bcs x` (`Fundamental.v:728`) | 1 merge, `x` is the representative | 0 | `cc_ok_alias` → `cc_ok_fresh` |

The 14 sites are `Cycle.v:32,34`, `FactoryEx.v:99,109`,
`FreshBetween.v:49,213,218`, `FreshMany.v:146,151`, `MilnerSched.v:117`,
`RequestReply.v:144`, `Scheduler.v:51,55`, `Sync.v:32`. The `t_new_at` sites
carry no constraint and state no obligation.

## Stage 1

### The equivalence lives on names

Points carry an unbounded offset and `x+k` does not enumerate, so the e-graph
is built over the name algebra of `theories/types/Types.v:24` and the offset is
carried as an integer potential on each union-find edge. A class says

```
Pt(p, o) ~ Pt(rep(p), o + pot(p))   for every o
```

which is exactly what `Hφs : φ (pt_shift 1 x) = pt_shift 1 (φ x)` buys.
`Types.v:65` stores the parent's offset inside the name,
`pt_slot x i = Pt (NSlot (pt_name x) (pt_off x) i) 0`, so the congruence rule
is: two slot names `S(Pt(p,e),i)` and `S(Pt(q,f),i)` merge when `p` and `q`
have one class and `e + pot(p) = f + pot(q)`. That is `Hφr`. The structural
law `Hφl` canonicalises every slot name before the class is looked up.

`Hφo` orients the representative. A name not rooted at `NVar 0` is its own
image, so it wins its class, and a class holding two distinct such names
admits no `φ` at all. That last case is not an implementation limit. It is the
correct answer, and §8.2's delegation G hits it.

### Representing a family rather than a ground term

The fact sets are schemas over counters. `fwb_P`'s alias is
`(γ+k).0 ≡ (ε+k).0` for every `k ∈ ℕ`, and an e-graph saturates a finite set.
The pipeline builds the e-graph over *name patterns*, where a base offset is a
linear form over the counters, and admits a merge only when the two patterns
carry the same counters and their offsets differ by a constant. A merge then
holds for every value of the counter, because the fact schema holds for every
value with the same counter on both sides.

That answers the question the brief asked. The two recursive alias families
are not an obstacle. The partition is read off a finite pattern set, and the
counter rides along in the pattern. It would be an obstacle to a general
decision procedure, where the two sides of an alias may carry different
counters, and nothing here decides that case.

Depth is a pattern too. `ch_P` and `st_P` live on `slotv n`, the n-fold
carried root, which the pipeline carries as one pattern `I(ι, n)` with the
depth as its counter. Those four constraints have no `≡` fact, so stage 1
returns `φ = id` and only the partition.

### What stage 1 produced

`φ` is nontrivial on four obligations out of twenty-seven. On `fw_C` and
`fwb_C` it merges the two slot families, cutting four families to three. On
`sched_rev` and `badlink` it merges two point constants, which is what turns
the premise set into a cycle. On `alias_bcs x` it merges `ι` with `x`. On
§8.2's delegation G it merges two slot families at potential `−2`, and on
everything else it is the identity.

For `fwb_C` the emitted `φ` is

```
Fixpoint cert_name (p : pname) : pname :=
  match p with
  | NSlot (NVar 0) k 0 => NSlot (NVar 1) k 0
  | NSlot q k i => NSlot (cert_name q) k i
  | _ => p
  end.
```

and `cert_name = fwb_name` is proved in `FwbCert.v` by `done`, because the two
fixpoints are convertible. The hand-written map of `Forwarder.v:237` is the
one the e-graph computes.

### The five conditions

The pipeline checks `Hφo`, `Hφs`, `Hφl` and `Hφr` on the seeded skeleton and
`HCe` by `φ a = φ b`, which is `geq_refl` in Rocq. `Hφs` holds by
construction, because `φ` acts on the name and shifts the offset. Each check
passes on every obligation where `φ` exists, and `Hφo` is the one that fails,
once, on §8.2's G.

### The tool

Two engines, run against each other.

The closure that produces `φ` is 196 lines of union-find with potentials
(`ccsmt/cc.py`). egglog does not choose representatives by the `Hφo`
orientation and does not carry an offset potential, so writing it was cheaper
than bending egglog's extraction cost into that shape.

egglog 14.0.0 then cross-checks the closure. The same points and the same
`FEq` facts go in, with the shift congruence as an egglog rule, and every pair
the hand-rolled closure calls equal is asked with `(check (= …))` and every
pair it calls distinct is asked the same way and expected to fail. Over 23
obligations that is 212 pairs, and egglog agrees on 212 of 212.

```
(datatype Off (OC i64) (OP String) (OAdd Off Off))
(datatype* (Nm (NVar i64) (NConst i64) (NSlot Pt i64) (NIter Nm Off))
           (Pt (P Nm Off)))
;; the shift congruence, Hphi_s: equal points stay equal after +d
(rule ((= (P p a) (P q c)) (= x (P p (OAdd a d))) (= y (P q (OAdd c d))))
      ((union x y)))
```

`NSlot` takes a point, not a name, which is what makes egglog's own
congruence rule do `Hφr`.

## Stage 2

The template is one rank per family, affine in the family's base offsets and
in the point's own offset, optionally under an integer level, which makes the
rank lexicographic. The family partition is stage 1's output, so the rank
indexes what the e-graph says and not what a reader guessed.

Two phases, as the earlier run established. Phase 1 instantiates every counter
over `0..5`, which is `QF_LIA`, and reads a model. Phase 2 substitutes the
model, which makes the universally quantified statement `LIA` again, and
checks that its negation is unsat. One shot synthesis puts an unknown
coefficient against a quantified counter, which is nonlinear, and both solvers
answer unknown, so it is not attempted.

Phase 1 unsat is a result in its own right. It asserts instances, so unsat
there proves no coefficients satisfy the universal statement, which is how the
three cycle rejections and §8.2's G are refuted.

For entailment the same query adds one clause, the negation of the goal. A
model is a countermodel, which is the shape of `rr_R` and `ord_R` in
`Rejected.v`. Phase 1 unsat means no countermodel of this template exists,
which is not a proof of entailment. The proof of entailment is the path.

70 queries under z3 5.3.3 and the same 70 under cvc5 1.4.2. The two solvers
agree on all 70, with no `unknown` and no timeout.

## The relay of §9.2, closed with an integer certificate

§9.2 claims `W_G` is strict and proves it with the rank `3k` on `c_k`, `3k+1`
on `d_k^0`, `3k+6−1/j` on `d_k^j` for `j ≥ 1`, and `ω+j` on `(z,j)`. That rank
leaves linear integer arithmetic twice, at the `1/j` and at the `ω`, and the
variant is not in Rocq.

Stage 2 rejects the affine template and finds a lexicographic one.

```
$ z3 queries/relay_M_affine_p2.smt2
sat
$ z3 queries/relay_M_lex_p1.smt2
sat
(
  (define-fun lv_F0 () Int 0)  (define-fun c_F0_1 () Int 0)
  (define-fun c_F0_off () Int 2)
  (define-fun lv_F1 () Int 0)  (define-fun c_F1_1 () Int 0)
  (define-fun c_F1_b0 () Int 2)  (define-fun c_F1_off () Int 3)
  (define-fun lv_F2 () Int 1)  (define-fun c_F2_1 () Int 14)
  (define-fun c_F2_off () Int 1)
)
$ z3 queries/relay_M_lex_p2.smt2
unsat
$ cvc5 queries/relay_M_lex_p2.cvc5.smt2
unsat
```

Phase 2 sat on the affine query means the candidate is not a certificate. The
level is what the ceiling needs: `(c,κ)` grows without bound in `κ` while
`(z,0)` is one point, so no affine rank clears it. That is the `tcc_C`
situation and the same fix.

So `(c,o)` ranks at level 0 by `2o`, `(c,k).1+j` at level 0 by `2k+3j`, and
`(z,j)` at level 1 by `j+14`. `RanksCert.v` proves all eight schemas, the
ground fact of `t₀` and program order inside each family by `lia`. Both
coefficients are smaller than the doc's and both live in `ℤ`.

This closes the certificate question for that one `G`. It does not close
§10.1. The open question there is a decision procedure for non-monotone
boundary roles, and the pipeline decides nothing. `(M)` still rejects this `G`,
and the right reading of that is now sharper: `(M)` rejects a `G` whose
strictness has a two-component integer certificate.

## The delegation round trip of §8.2, where it breaks

§8.2's `G` is ground, with the payload alias `(c,2).1 + 2 ≡ (c,7).1`. The
section shows `(M)` fails and calls the criterion open. The fact set is not
written out there, so the pipeline runs the four order facts that the shape of
`dl_P` (`Delegation.v:48`) gives, once for the receive at instant 2 and once
for the send at instant 7, plus the alias.

```
(c,2) ≺ (c,2).1      (c,2).1+1 ≺ (c,3)
(c,7) ≺ (c,7).1      (c,7).1+1 ≺ (c,8)
(c,2).1 + 2 ≡ (c,7).1
```

Three things come out, and the second is the one worth having.

Stage 1 refuses a `φ`. Both sides of the alias are rooted at the point
constant `c`, so `Hφo` fixes both, and no `φ` can merge them.

```
NO PHI: Hphi_o blocks: (a@2).1 and (a@7).1 are both outside the fresh
variable, so phi fixes both, yet FEq (a@2).1@2 = (a@7).1@0 forces them equal
```

That is the right answer and not a failure. `cc_ok` governs a fresh extension,
and a ground alias is a world fact, checked by `strict W` instead. Run as a
world equivalence the merge goes through at potential `−2`, which is §8.2's
negative shift, and the two slot families collapse to one chain indexed by `j`.

```
a@2 < (a@2).1@0 ; (a@2).1@1 < a@3 ; a@7 < (a@2).1@2 ; (a@2).1@3 < a@8
```

Stage 2 proves no rank of the template exists.

```
$ z3 queries/deleg_rt_affine_p1.smt2
unsat
$ cvc5 queries/deleg_rt_affine_p1.cvc5.smt2
unsat
$ z3 queries/deleg_rt_lex_p1.smt2
unsat
```

Unsat already on the instances, so no affine rank per family and no
lexicographic one. The reason is readable off the four facts. They force
`r_c(2) < r_S(0)` and `r_S(1) < r_c(3)`, so `r_S(0)` and `r_S(1)` sit inside
the gap between `r_c(2)` and `r_c(3)`, and they force `r_S(2)` and `r_S(3)`
inside the gap between `r_c(7)` and `r_c(8)`. A rank affine in `j` takes equal
steps, so it cannot jump from one gap to the other and then stay put.

`W_G` is strict all the same. The fact graph over the mentioned points is
acyclic, and a rank with one break discharges it. The break is read off the
ground facts: the offsets of the slot family that any fact mentions are
`0,1,2,3`, so the break ranges over `1..3`.

```
$ z3 queries/deleg_rt_piecewise_p1.smt2
sat
(  (define-fun ca1 () Int (- 7))  (define-fun cao () Int 3)
   (define-fun cs1 () Int 0)      (define-fun cso () Int 1)
   (define-fun jump () Int 13)    (define-fun B () Int 2)  )
$ z3 queries/deleg_rt_piecewise_p2.smt2
unsat
$ cvc5 queries/deleg_rt_piecewise_p2.cvc5.smt2
unsat
```

`r_c(o) = 3o − 7` and `r_S(j) = j + 13·[j ≥ 2]`, verified under the quantifier
and proved by `lia` in `RanksCert.v`.

The boundary this draws is narrow and stateable. The obstruction is not
realizability of the negative cycle, which is where §8.2 leaves it. The
obstruction is that an affine rank cannot interleave two ground blocks of one
alias class. The certificate language has to allow a case split on a counter,
and the piece count is bounded by the number of ground facts that touch the
class. That hypothesis is mine, not a theorem: the pipeline checked one `G`,
and the queries are hand-written for the piecewise template because the
pipeline's own templates are both unsat.

## The Rocq certificates

Three files, compiled with Rocq 9.2 against
`/home/mari/proglang/research/rocq/gvsharp-lr-df/.claude/worktrees/exists/theories`
as it stands on disk. Nothing under `theories/` was touched.

```
### emitted Rocq blocks against the files on disk
FwbCert.v        emitted block matches the file
RejectCert.v     emitted block matches the file
RanksCert.v      zrank (c_depth, c_off): (-2, 1) matches the file
RanksCert.v      relay_M (level, c_base, c_off, c_1) for a: (0, 0, 2, 0) matches the file
RanksCert.v      relay_M for (a+_).1: (0, 2, 3, 0) matches the file
RanksCert.v      relay_M for z: (1, 0, 1, 14) matches the file

### Rocq certificates
FwbCert.v       accepted
RejectCert.v    accepted
RanksCert.v     accepted
```

Each file marks its emitted block with `BEGIN emitted` and `END emitted`, and
`ccsmt/rocq.py` regenerates the block from the pipeline and compares it with
what is on disk. The proof scripts outside the markers are fixed skeletons.
The pipeline emits every definition a skeleton instantiates and none of the
tactics.

### `FwbCert.v`, the one that discharges a real goal

```
Lemma cert_fwb_ok W Ψ :
  world_wf W → (fp_C, [pvar 0]) ∈ Ψ → cc_ok (seqs W Ψ) (slt W Ψ) fwb_C.
```

Same statement as `fwb_ok` (`Forwarder.v:278`). It is proved from four emitted
definitions.

`cert_phi`, stage 1's `φ`, convertible with `fwb_phi`.

`cert_rank x := pt_off x` and `cert_R x y := cert_rank x < cert_rank y`, stage
2's rank. Every one of the four `≺` facts crosses the `ι` boundary after `φ`,
so `R` carries no fact and only program order, and the synthesised
coefficients are `c_off = 1` and `c_1 = 0`. `fwb_ok` uses `pofs` here, which
asks for one name as well; the rank is weaker and still enough.

`cert_Lo` and `cert_Hi`, read off the normalised facts by the root test. A
fact from an outer point into `ι` is a `Lo` pair, a fact out of `ι` is a `Hi`
pair. Two of each. `cc_ok_fresh` reads them the same way, so this part of the
pipeline is the development's own rule, mechanised.

What is not emitted is `HB`, the condition that every `Lo` below every `Hi`
closes in the ambient order. The pipeline computes the four chains by
reachability over the facts of `fp_C` at `γ` plus program order, and the proof
script walks them. Those four chains are the content of `fwb_ok`'s hardest
case, and they are reachability output, not a rank.

So the answer to the brief's question: yes, the pipeline's output typechecks
against the development's actual `cc_ok`, for the one constraint where the
hand proof needed a real `φ`.

### `RejectCert.v`

`rlo_call_underivable` is the new one. `rlo_rank` and `rlo_C1` are emitted;
the `fl_map` plumbing is the fixed skeleton of `rr_call_underivable`, with the
`Q` relation, the `isvar` blob for constant-rooted points and the fourteen
side conditions unchanged. The pipeline synthesises the rank and nothing else.
`rr_rank'` and `ord_rank` are stage 2's countermodels for the two existing
entailment rejections, checked on the arithmetic obligations only.

### `RanksCert.v`

`fc_ok'` and `fwkob_ok'` are real `cc_ok` proofs. The development orders
`fc_C` and KobForwarder's `fw_C` by the lexicographic `dlt`, on the stated
grounds that a descending depth has no rank in `ℕ` (`LitTools.v:88`). Stage 2
synthesised the integer rank `off − 2·depth`, and `cc_ok_inner` asks only for
transitivity, irreflexivity and program order, which an integer rank has. Each
lemma is four lines.

```
Definition zrank (x : point) : Z :=
  Z.of_nat (pt_off x) - 2 * Z.of_nat (sdepth (pt_name x)).
```

`relay_M_ok` and `deleg_rt_ok` are arithmetic. Neither `G` is in the
development, so there is no `cc_ok` to discharge.

## What a tool proved and what I concluded

Proved by z3 and cvc5, with the obligation written out and the negation
checked.

- A rank per family, affine in the family's base offsets and the point's own
  offset, discharges nine of the eleven `cc_ok` obligations. `tcc_C` needs a
  level. `fwb_C` needs no fact rank at all once `φ` is applied.
- `off − 2·depth` discharges `fc_C` and KobForwarder's `fw_C`, recovered from
  the facts alone.
- No rank of the template refutes `rq_C`, `rel_C` or `ord_C` at the goal their
  accepted programs ask.
- A rank countermodel refutes `rr_call`, `ord_no_constraint` and
  `relay_one_round` at their goals, and phase 2 verifies each under the
  quantifier.
- No rank of the template satisfies the premise sets of `sched_rev`, `ms_rev`,
  `badlink` or `blocked`.
- A lexicographic integer rank discharges every schema of §9.2's relay.
- No affine and no lexicographic rank discharges §8.2's ground delegation `G`,
  and a rank with one break does.

Proved by egglog: every one of 212 equality and disequality claims the
hand-rolled closure makes, over 23 obligations.

Proved by Rocq 9.2, against the development: `cert_fwb_ok`,
`rlo_call_underivable`, `fc_ok'`, `fwkob_ok'`, and the arithmetic of every
emitted rank.

Concluded by me, not by a tool.

- Stage 1 before stage 2 is the right order, and the gain is small on the
  examples and sharp where it lands. Nine obligations get `φ = id` and only a
  partition. Four get a real merge, and on two of those, `sched_rev` and
  `badlink`, the merge is what makes the rejection a rejection.
- The earlier run's conclusion that the alias cases need a human is wrong.
  `fwb_ok`'s `φ` is the e-graph's representative choice under `Hφo`, and
  `FwbCert.v` compiles. What the earlier run could not do was read `Lo` and
  `Hi` off the root test, which is the other half of `cc_model` and is purely
  syntactic.
- The infinite alias families are not an obstacle to this demonstration. They
  are an obstacle to a general procedure, and the line is exactly whether the
  two sides of an alias carry the same counter. Every alias in the examples
  does. §8.2's does not carry a counter at all and still breaks, by the
  potential.
- `Hφo` is the real frontier, not the counters. It forbids a `φ` that merges
  two outer names, so an alias between ground points can never be discharged
  by stage 1. It has to be a world fact, and then strictness of the world is
  the question, with a certificate language that needs case splits.
- The certificate language wants three features, in this order of
  cost: a rank per family affine in the counters, an integer level, and a case
  split on a counter with breakpoints read off the ground facts. The first two
  cover everything in the development. The third is what §8.2 needs.
- `LitTools.v:77-80` should be weakened. The note says neither `dlt` nor `ult`
  has a rank in `ℕ`, which is true and beside the point, because `cc_ok_inner`
  asks for no well-foundedness and an integer rank exists. `fc_ok'` and
  `fwkob_ok'` are the replacements.
- `Rejected.v:101` and `Rejected.v:119` can become theorems. `RejectCert.v`
  has both.

## Files

Everything is in one directory and nothing was added to the repository.

| path | what |
|---|---|
| `/tmp/claude-1000/-home-mari-proglang-research-rocq-gvsharp-lr-df/7dd62bf0-d2cb-4552-a789-fb0ae5b5d0a4/scratchpad/ccsmt/run_all.sh` | the one command: both stages, the emitter check, the three Rocq compiles |
| `.../ccsmt/terms.py` | the point and name algebra of `Types.v:24` as patterns over counters |
| `.../ccsmt/constraints.py` | every constraint, every rejection, every open case, each with its file and line |
| `.../ccsmt/cc.py` | stage 1: union-find with offset potentials, congruence saturation, the `Hφo` orientation, the five checks |
| `.../ccsmt/stage1.py` | seeding, normalisation through `φ`, the egglog cross-check |
| `.../ccsmt/smt.py` | stage 2: the family decomposition, the rank template, the two phases, both solvers |
| `.../ccsmt/entail.py` | the entailment side: the ground graph, reachability, cycle search |
| `.../ccsmt/run.py` | the driver, writes `results.json` |
| `.../ccsmt/rocq.py` | emits the Rocq blocks and compares them with the files on disk |
| `.../ccsmt/queries/` | 70 `.smt2` files, plus a `.cvc5.smt2` copy of each with `(get-model)` stripped |
| `.../ccsmt/rocq/FwbCert.v` | `cc_ok` for `fwb_C` from the pipeline's `φ`, rank, `Lo` and `Hi` |
| `.../ccsmt/rocq/RejectCert.v` | `rlo_call_underivable` and the other rejection certificates |
| `.../ccsmt/rocq/RanksCert.v` | `fc_ok'`, `fwkob_ok'`, `relay_M_ok`, `deleg_rt_ok` |
| `.../ccsmt/runall.txt` | the full transcript of one `run_all.sh` |
| `.../ccsmt/results.json` | every stage's output per obligation, machine readable |

`run_all.sh` takes `DEV` for the development's `theories` directory and `PY`
for the Python with egglog and z3. The defaults are the worktree and
`../smtenv/bin/python`.

Versions. z3 5.3.3 64 bit, as the `z3-solver` wheel. cvc5 1.4.2, git 282d5e0,
the Linux x86-64 static release. egglog 14.0.0, the Python wheel over the Rust
library. CPython 3.14.10. The Rocq Prover 9.2.

Sources were read with
`git show exists:theories/<file>` on the worktree, because another agent is
committing to `payload-self` there. The order constraints, `Creation.v` and
`Rejected.v` are identical on both branches; the diff between them touches
session types only.
