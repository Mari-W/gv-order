# No equality constraints (branch no-eq)

State of 2026-11-06. Branch `no-eq` from main cba4a2b. Step 1 (surface) is
done for the core calculus and every core and cfst example (§2, §3). Step 2
(metatheory) is done for the core (§7): facts have no ≡, worlds have no ≡,
Γ ⊢ ≡ is equality, `new@x` is a primitive typing of `new`, and O-New places a
channel at a fresh constant or at a known point. The PGV, Padovani–Novara and
MP translations still rely on ≡ and are out of the build (§7.4). The whole
remaining development builds from clean, and every remaining CheckAll entry
(192 of 301) is closed under the global context.

## 1. What ≡ did, verified

The survey in the task was right on four counts and incomplete on three.

1. `new` pinned to an existing point. In Rocq this is `t_new_at`
   (static/Fundamental.v), a derived rule. Its statement has no ≡. The
   program is the plain `let_new e`. The alias {ι ≡ x} (`alias_bcs`) is
   chosen inside its derivation and moved away by E-Open and E-Conv. Every
   example that "creates at a payload point" (Delegation, ChoiceTranslate,
   KobForwarder, ExPayload, MilnerSched at ι+2k, the PGV and MP translations)
   uses this rule. So `new@p` already exists at the surface, and it is
   `t_new_at`. Step 1 needs no change there. ChoiceTranslateEx.v holds a
   source-level copy of the same derivation (`f_new_at`).
2. Milner scheduler: `t_new_at` at ι+2k, as above.
3. `link`: the signature asked x ≡ x̄′ ([KSLink], Types.v). Changed (§2).
4. The forwarder's box constraint held (ι+k)[0] ≡ (ι′+k)[0]. Changed (§3).
5. Metatheory: as listed, plus §5.

Uses the survey missed.

- The forwarder's creation constraint `fwb_C` (main of Forwarder.v) held
  (γ+k)[0] ≡ (ε+k)[0], an alias between a payload point of the fresh
  channel ε and a payload point of the existing channel γ. This is not of
  the form "fresh name ≡ existing point", so `new@p` does not cover it.
- examples/Congruence.v: a box constraint {ι ≡ ι′, …}, written to exercise
  the congruence rules of ≡.
- examples/cfst/FirstAction.v: a box constraint {ι ≡ κ[0], …}.
- The subsumption translations put ≡ facts into constraints and worlds by
  denotation. pn/PNWorld.v `crel_fact` holds x ≡ y whenever `den x = den y`,
  and PNTranslate uses it to move a received channel from the payload point
  to its canonical point (`pay_eq`). mp/MP*World.v `crel_fact` does the
  same, and `pex_fact` holds x ≡ x̄ for every point of a segment existential.
  pgv/PGVWorld.v builds `Wpgv` with aliases by denotation (`pgv_eq`), used by
  E-Conv in PGVTranslate.v.
- examples/Rejected.v stated the bad-link and reversed-scheduler rejections
  with an alias premise.
- algorithmic/Algorithmic.v emitted an `AEq` atom for link, and `tmatch`
  emits `AEq` for every session type comparison (E-Conv up to ≡).

### 1.1 Creation constraints and conservativity

The claim "conservativity forbids a creation constraint from identifying two
existing points" holds. `cc_conservative_at` (Types.v) asks that Γ + C
derive x ≡ y between two points without root ι only when Γ derives it.

The second claim "so every ≡ in a creation constraint pins the fresh name to an
existing point" does not hold for `cc_ok`, the premise of `KTNewEx`. `cc_ok`
also admits aliases between a derived point of ι and an outer point
(ι[0] ≡ w, (ι+k)[0] ≡ (γ+k)[0] as in the old `fwb_C`) and aliases between
two points of ι (ι+1 ≡ ι[0]). The narrower `fresh_ok` admits only ι ≡ w,
and `cc_ok_fresh` makes it a sufficient condition. Only `fwb_C` used the
wider form, and §3 replaces it by order facts. A pinned payload point
ι[0] ≡ w is what an existential payload expresses without ≡ (§3).

### 1.2 Does `new_ι′ {ι′ ≡ p}` transfer to `new@p`?

Statically yes, and it already has (`t_new_at`). Semantically the present
proof (`Erel_app_new`, rules/TermRules.v) creates the channel at a fresh
constant a, extends the world by a ≡ p (`wext_cc`), and E-Conv moves the
types from a to p. Without ≡ the channel has to sit at p itself. The
relation's O-New clause (relation/LogicalRelation.v) asks the entries at
`pconst a` for a fresh a and a fresh extension of the world. `new@p` needs a
second disjunct: entries at a point p known to W, and W unchanged. This is a
change of the relation, and it is part of Step 2 (§5).

Two channels at one point are possible today. Two `t_new_at` at the same x
give two channels whose entries sit at ≡ points, and the relation never
asks points of distinct channels to differ. Every overlap condition reads
≡_W (sharp edges 40), so equal points behave as aliased ones. The deadlock
argument picks a blocked end with a least point. Two ends at one point u
are then both blocked at u, and each owes u ≺ the partner of the other's
held end, so the argument goes through unchanged. Harmless.

## 2. Changes, Step 1

All on branch `no-eq`. Every file below builds, and the whole development
builds (§4).

| Where | Before | After |
|---|---|---|
| Types.v `KSLink`, `KTLink`, `konst_ty_case` | `link : S@x ⊗ dual S@x′ ⊸ ∗` with x ≡ x̄′ | `link : S@x ⊗ dual S@x̄ ⊸ ∗`, no fact |
| rules/TermRules.v `Erel_app_link` | read x ≡ x̄′ from the signature | x ≡ x̄̄ by reflexivity |
| static/PointSubst.v, invariance/PointRenaming.v | link case read the alias | link case is the signature at the image point |
| algorithmic | link emitted `AEq x ȳ` | link checks y = x̄ syntactically, no atom |
| examples/Scheduler.v | link proved x ≡ x̄̄ | link at x and x̄ directly |
| pgv/PGVTranslate.v | link at ppt S and ppt S, alias x ≡ x̄ by denotation | the same alias, now read by E-Conv on the arrow type (still ≡, K8) |
| examples/Rejected.v | rejections with an alias premise | the same rejections with equal points |
| examples/Forwarder.v | alias in Cf and in the creation constraint of b | existential payload, order facts only (§3) |
| examples/Congruence.v | box over ι, ι′ with ι ≡ ι′ | box over ι |
| examples/cfst/FirstAction.v | box takes d at ι with ι ≡ κ[0] | box takes d at κ[0]; ι unused |

### 2.1 Each example before and after

Rejected.v, bad link.

    before  link ⟨c₁, d₁⟩ asks x̄ ≡ y; x̄ ≺ z̄ ≺ y ≡ x̄
            badlink_underivable : ¬ (x ≡ y ∧ x ≺ z ∧ z ≺ y)
    after   link ⟨c₁, d₁⟩ types only with d₁ at x̄, i.e. d = new@x̄
            badlink_underivable : ¬ (x ≺ z ∧ z ≺ x)

Rejected.v, reversed scheduler.

    before  sched_rev_underivable : ¬ (y ≺ x ∧ z ≺ y ∧ z ≡ x)
    after   sched_rev_underivable : ¬ (y ≺ x ∧ x ≺ y)

Congruence.v.

    before  cg : □(∀ι ι′. {ι ≡ ι′, ι′ ≺ (ι′[0])‾, ι̅′ ≺ (ι′[0])‾}. ∗ ⊸
                    ((Scg@ι ⊗ Close@ι′[0]) ⊗ Close@(ι′+2) ⊸^{ι′+2}_{ῑ} ∗))
            forced at [γ; γ]
    after   cg : □(∀ι. {ι ≺ (ι[0])‾, ῑ ≺ (ι[0])‾}. ∗ ⊸
                    ((Scg@ι ⊗ Close@ι[0]) ⊗ Close@(ι+2) ⊸^{ι+2}_{ῑ} ∗))
            forced at [γ]

The example existed to use the congruence rules of ≡. Without ≡ a box whose
variables are always instantiated alike takes fewer variables.

cfst/FirstAction.v.

    before  fa : □(∀κ ι ζ a. {ι ≡ κ[0]} ∪ walk. ∗ ⊸ ((!(Close);XformD;a)@κ ⊗ Close@ι ⊸^ζ …))
    after   fa : □(∀κ ι ζ a. walk. ∗ ⊸ ((!(Close);XformD;a)@κ ⊗ Close@κ[0] ⊸^ζ …))

ι is kept unused so that ζ keeps its index. Cleanup item: drop ι and renumber.

link everywhere.

    before  link : S@ι ⊗ dual S@ι′ ⊸ ∗      {ι ≡ (ι′)‾}
    after   link : ∀a. S@a ⊗ dual S@ā ⊸ ∗

## 3. The forwarder

    Si = μX. ?(Close@σ).X                         σ = x[0] for the action at x
    So = μX. !(∃^{σ̄} κ. {κ ≺ σ}. Close@κ).X
    Cf = {ι+k ≺ ι′+k,  ι+k ≺ ι̅′+k,  ι′+k ≺ ι̅+k+1,  ι′+k ≺ σ̄ₖ,
          ρₖ ≺ σₖ,  σ̄ₖ ≺ ρ̄ₖ  ∣  k ∈ ℕ}             ρₖ = (ι+k)[0],  σₖ = (ι′+k)[0]
    Cp = {ι+k ≺ ι[0], ι[0]‾,  ι[0], ι[0]‾ ≺ ι̅+k+1  ∣  k ∈ ℕ}      unchanged

The payload binds σ (the payload variable, x[0] at the send) and packs κ.
Its lower bound is σ̄ and its constraint is {κ ≺ σ}. In Rocq `Pfo`,
`Cfo_P`, `fw_P` (examples/Forwarder.v).

The gates, one round.

- Forwarder, recv on a at ι+k while holding b. ι+k ≺ ι̅′+k and, for the
  upper point ι′, ι+k ≺ ι′+k. Unchanged.
- Forwarder, send on b at ι′+k. It packs d : Close@ρₖ at κ = ρₖ. E-Pack
  asks the constraint ρₖ ≺ σₖ and the bound σ̄ₖ ≼ ρ̄ₖ (the head of d is its
  partner point ρ̄ₖ). The send asks ι′+k ≺ σ̄ₖ (the head of the packed value
  is its bound) and ι′+k ≺ ι̅+k+1 for a. All four are facts of Cf.
- Producer, unchanged. It creates e at ρₖ with `new@(ρₖ)`, sends e, closes e′
  at ρ̄ₖ.
- Consumer at θ (forced at ι̅′), recv at θ+k with upper point σₖ: θ+k ≺ σₖ
  from Cp. E-Open gives d at a fresh κ with κ ≺ σₖ. close d at κ while it
  holds c at θ+k+1 asks κ ≺ θ̄+k+1, which is κ ≺ σₖ ≺ θ̄+k+1 by Cp, and the
  upper point σₖ is witnessed by κ ≺ σₖ.
- Recursive calls, one round later. Cf[ι+1, ι′+1] ⊆ Cf and Cp[θ+1] ⊆ Cp
  (`fw_sub`, `fp_sub`). The consumer's recursive call sits under the open,
  where its hypothesis is Cp at the shifted variable, and is proved fact by
  fact.

The alias σ ≡ ρ splits into two facts in opposite directions, ρ ≺ σ for the
receiver and σ̄ ≺ ρ̄ for the sender. No fact relates σ to σ̄ or ρ to ρ̄, and
≺ is not closed under x ↦ x̄, so they are consistent. The sketch
{σ̂ ≺ κ̂, κ̂⁺ ≺ σ̂⁺} does not close the consumer's gate. The consumer needs
an upper bound κ ≺ σ, and the lower bound of the existential is what the
sender needs, so one fact κ ≺ σ in C and the bound σ̄ suffice.

main. a is created with `fpa_C` (unchanged), b with

    Cb = {γ+k ≺ ε+k, ε̄+k,  ε+k ≺ (ε+k)[0]‾, γ̄+k+1,
          (γ+k)[0] ≺ (ε+k)[0],  (ε+k)[0]‾ ≺ (γ+k)[0]‾,
          ε̄+k ≺ (ε+k)[0], (ε+k)[0]‾,  (ε+k)[0], (ε+k)[0]‾ ≺ ε+k+1  ∣  k ∈ ℕ}

an order-only creation constraint (`fwb_ok` by `cc_ok_out`). Inside ε its
facts follow the rank 3k for ε+k and 3k+1 for (ε+k)[0] at either polarity.
Every entering fact u ≺ p and leaving fact q ≺ v with p ≼ q close through
program order and `fpa_C`. The pair (γ+k)[0] ≺ (ε+k)[0] ≺ ... ≺ (γ+k)[0]‾
would need (γ+k)[0] ≺ (γ+k)[0]‾, which `fpa_C` lacks, but (ε+k)[0] and its
dual have the same rank, so the pair is never chained. The old proof needed a
model that mapped ε's payload points onto γ's.

`fw_deadlock_free` is closed (§4).

## 4. Theorems

`make` builds the whole development. CheckAll.v (regenerated, 301 theorems,
the same names as on main) reports every one closed under the global context.
That includes `soundness`, `soundness_source`, `fundamental`,
`fundamental_proc`, `adequacy`, `sem_rules_fundamental`, and for the changed
examples `fwd_typed`, `fprod_typed`, `fcons_typed`, `fw_typed`,
`fw_deadlock_free`, `cgbox_typed`, `cg_typed`, `cg_deadlock_free`, the
FirstAction theorems, `sched_rev_underivable`, `badlink_underivable`,
`sched_deadlock_free` and the PGV, PN and MP theorems.

The paper (2-calculus.tex link signature, 7-appendix.tex forwarder and Milner
scheduler, rejection theorems) still describes main and is not edited on this
branch.

## 5. Step 2 inventory

Counts over `theories/**/*.v` on this branch (grep, one match per
occurrence): `w_eq` 372 in 30 files, `seqs` 397 in 33, `heqs` 89 in 9, `geq`
156 in 17, `FEq` 49 in 17, `pteqW`/`teqW` 297 in 12, `steq`/`hsteq` 341 in
25, `wf_eq_*` 263 in 21, `se_*`/`he_*` (aliasing rules) 593 in 61,
`tenv_comp` 257 in 23 (its first argument is ≡). The per-file table is
below. The uses fall into nine kinds.

| Kind | What | Files (main ones) | Occurrences | Removal |
|---|---|---|---|---|
| K1 fact syntax | `FEq`, `fact_map`, `fact_holds`, `bcs_hold peq plt`, `konst_ty peq` | types/Types.v, static/PointSubst.v | ~60 | mechanical: drop the constructor, drop the peq argument |
| K2 world ≡ | `w_eq` field, `wf_eq_*` axioms, `geq` closure, `wgen E`, `wjoin`, `wrestrict` | relation/Worlds.v, Creation.v, BranchWorlds.v | ~350 | replace by `=`; most axioms become trivial; Amalgamation and Fresh extension simplify |
| K3 static fact theory | `seqs`, `heqs`, rules A-* (`se_*`, `he_*`), `sl_eql/sl_eqr` | static/FactTheory.v, Source.v, Typing.v | ~250 | delete rules, `seqs` becomes `=` |
| K4 conversion | `pteqW`, `teqW`, `steq`, `hsteq`, E-Conv, Type point conversion | invariance/PointConversion.v (1424 lines, 207 hits), LogicalRelation.v, TermRules.v | ~650 | E-Conv keeps only ≈ of sessions; PointConversion.v mostly goes |
| K5 cut and overlap conditions | `tenv_comp (w_eq W)`, `w_eq e.2 (pt_dual e'.2)` in P-Connect/P-Join, O-Link, Q-Link | composition/*.v, rules/Bind.v, TermRules.v | ~300 | the statements keep their shape with `=`; proofs that rewrite along ≡ simplify |
| K6 creation | `fresh_eq`, the alias branch of `fresh_ok`, `cc_eq_at`, `t_new_at` via `alias_bcs` | Types.v, PointSubst.v, Fundamental.v, Creation.v | ~60 | needs `new@p` as a primitive typing of `new` and a second disjunct in O-New (§1.2) |
| K7 examples | `bcs_hold (seqs W Ψ) …` signatures, conversions in proofs | examples/** | ~120 | mechanical once K1/K3 are gone |
| K8 translations | ≡ by denotation in constraints and worlds | pn/*, mp/*, pgv/* | ~450 | redesign (below) |
| K9 semantic examples | `w_eq W` in direct relation proofs | examples/SemFlag.v, SemRounds.v, DataBranch.v | ~60 | mechanical with K2 |

### Decision: w_eq becomes syntactic equality

Worlds are (names, ≺) and every former w_eq reads as equality, not as a field
that is propositionally equality. Reasons. (1) Every world the semantics builds
from an alias-free start is alias-free when no constraint holds ≡: `wgen` with
equality generators has `geq = eq` (`geq_eq`, relation/Worlds.v), and the join
of alias-free worlds is alias-free. (2) A field equal to `=` would keep every
`wf_eq_*` obligation. (3) The relation's quantification over W′ ⊒ W ranges over
alias-free worlds, and monotonicity is unaffected because the order part is
unchanged. Done in §7. (relation/NoAlias.v of the first session is gone, the
lemma `geq_eq` moved into Worlds.v.)

### The central changes and whether they hold

- O-New with a second disjunct (entries at a known point, world unchanged).
  The semantic content is the same as today's alias case, which the relation
  already proves sound. No lemma is expected to become false. Bind.v,
  PTerm.v, Internalize.v and ConnectSteps.v destruct O-New and gain a case.
- Cut conditions of P-Connect, P-Join, `Prel_connect`: the statements keep
  their form with ≡ read as `=`. The user's constraint (no change beyond
  dropping ≡) is met.
- E-Conv: up to ≈ of session types only. Type point conversion
  (`Vrel_tconv` with `teqW`) collapses to `=`.
- Translations. The PN, MP, MP2, MP3 translations name every point by its
  denotation and identify points with equal denotation by ≡. The essential
  use is delegation: a received channel arrives at the payload point x[0]
  and the translation needs it at its canonical point (`pay_eq`). Without ≡
  the translated payload has to be an existential whose constraint states
  all facts of the canonical point (an infinite constraint, which boxes and
  existentials allow), and every later use of the received channel happens
  at the opened variable instead of the canonical point. That breaks the
  invariant "a channel of source type t sits at den(t)" that the
  translation lemmas are stated with. MP's `pex_fact` additionally holds
  x ≡ x̄ for segment points, which has no order-only counterpart: the two
  ends of a segment channel are the same point in the MP encoding. PGV's
  world aliases two points with one denotation, which the translation can
  avoid by choosing one syntactic name per denotation (likely easy).

### Effort

- K1–K5, K7, K9 (core metatheory, ~1900 occurrences counted above, ~25
  files): two to four days of mechanical work with a full build (~12 min)
  per round. PointConversion.v and most of FactTheory.v's ≡ half disappear.
- K6 (new@p primitive, O-New disjunct): one day.
- K8: PGV one day. PN about a week. MP, MP2, MP3 one to two weeks, with an
  open design question for `pex_fact` (x ≡ x̄).

The core part took one session (§7). The translations are not ported.

### Per-file counts

Columns: w_eq FEq seqs heqs geq teqW steq wf_eq se/he tenv_comp lines.

```
theories/algorithmic/Algorithmic.v               0    0    0    2    0    0    1    0    0    0    455
theories/algorithmic/Soundness.v                 0    0    0    3    0    0    4    0    6    0    356
theories/composition/ConnectCut.v                1    0    0    0    0    0    0    3    0    0    729
theories/composition/ConnectSteps.v              1    0    0    0    0    0    0   17    0    0    952
theories/composition/Internalize.v               6    0    0    0    0    3    0   22    0    0   1904
theories/composition/PConnectN.v                 6    0    0    0    0    0    0    0    0    0    429
theories/composition/PConnect.v                  1    0    0    0    0    0    0    0    0    0    217
theories/composition/PTerm.v                    29    0    0    0    0    0    0    8    0    5   1026
theories/composition/ReadyChain.v               13    0    0    0    0    0    0    4    0    0    958
theories/examples/cfst/ArithServer.v             0    0    0    0    0    0    9    0    0    0    455
theories/examples/cfst/BranchOrder.v             0    0    1    0    0    0    0    0    0    0    198
theories/examples/cfst/CfstScheduler.v           0    0    6    0    0    0    0    0    0    0    718
theories/examples/cfst/CfstTools.v               0    1    1    0    0    0    0    0    0    0    439
theories/examples/cfst/FirstAction.v             0    0    0    0    0    0   16    0    0    0    556
theories/examples/cfst/MuVar.v                   0    0    0    0    0    0    3    0    0    0    273
theories/examples/cfst/SegmentDeleg.v            0    0    0    0    0    0    8    0    0    0    223
theories/examples/cfst/SegmentInterleave.v       0    0    1    0    0    0    8    0    0    0    280
theories/examples/cfst/Stream.v                  0    0    3    0    0    0    0    0    0    0    215
theories/examples/cfst/TreeCopy.v                0    0    4    0    0    0   12    0    0    0    933
theories/examples/cfst/TreeSum.v                 0    0    0    0    0    0   11    0    0    0    431
theories/examples/ChoiceEnc.v                    0    0    2    0    0    0    0    0    0    0    671
theories/examples/ChoiceNegative.v               0    0    0   20    1    0   36    0   15    0    611
theories/examples/ChoiceTranslateEx.v            0    2    0    1    0    0    0    0    3    0    328
theories/examples/ChoiceTranslate.v              0    0    0    8    0    0   19    0    0    0    577
theories/examples/Congruence.v                   0    0    1    0    0    0    0    0    0    0    226
theories/examples/DataAlternate.v                0    0    3    0    0    0    0    0    0    0    479
theories/examples/DataBranch.v                   6    0    0    0    0    0    0    7    0   14   1278
theories/examples/EndPoints.v                    0    1    0    0    1    0    0    0    0    0    190
theories/examples/ExampleTools.v                 0    2    3    0    3    0    1    0    2    2    775
theories/examples/ExPayload.v                    0    0    0    1    0    0    0    0    0    0    281
theories/examples/FactoryEx.v                    0    0    1    0    0    0    0    0    0    0    207
theories/examples/FactServer.v                   0    0    2    0    0    0    0    0    0    0    214
theories/examples/Forwarder.v                    0    0    7    0    0    0    0    0    0    0    480
theories/examples/FreshBetween.v                 0    0    0    0    0    0    0    1    0    0    298
theories/examples/KobForwarder.v                 0    0    2    0    0    0    0    0    0    0    221
theories/examples/LitTools.v                     0    0    0    0    0    0    0    0    1    0    151
theories/examples/Ordered.v                      0    0    0    0    0    0    0    0    5    4     83
theories/examples/ReceivedChain.v                0    0    4    0    0    0    0    0    0    0    275
theories/examples/Rejected.v                     0    0    0    0    0    0    0    4    0    0    299
theories/examples/Relay.v                        0    0    5    0    0    0    0    0    1    0    380
theories/examples/RequestReply.v                 0    0    3    0    0    0    0    0    0    0    220
theories/examples/SemFlag.v                      1    0    0    3    0    0   14    4    9    5    578
theories/examples/SemRounds.v                   11    0    0    0    0    1    0   18    2    9    552
theories/examples/Stream.v                       0    0    3    0    0    0    0    0    0    0    272
theories/examples/TailCall.v                     0    0    2    0    0    0    0    0    0    0    159
theories/invariance/EquivInvariance.v            1    0    0    0    0    8    0    0    0    0    180
theories/invariance/JunkRenaming.v              12    0    0    0    0    0    0    9    0    7   2860
theories/invariance/Monotonicity.v               0    0    0    0    0    1    0    0    0    3    265
theories/invariance/PointConversion.v           41    0    0    0    0  207    0   59    0    4   1424
theories/invariance/PointRenaming.v             31    0    0    0    0   34    0    5    0   11   1821
theories/mp/MP2Translate.v                       0    4   76    0    0    0   48    0   38    0   2138
theories/mp/MP2World.v                           0    2    1    0    1    0    0    0    2    0    563
theories/mp/MP3Translate.v                       0    4   94    0    0    0   52    0   54    0   2506
theories/mp/MP3World.v                           0    2    1    0    1    0    0    0    2    0    608
theories/mp/MPTranslate.v                        0    0   21    0    0    0   37    0   37    0   1160
theories/mp/MPWorld.v                            0    1    2    0    1    0    0    0    2    0    560
theories/pgv/PGVTranslate.v                      0    0    0    0    0    0    2    0    5    0    406
theories/pgv/PGVWorld.v                          1    0    0    0    1    0    0    0    0    0    381
theories/pn/PNTranslate.v                        0    0    8    0    0    0   10    0   12    0   1042
theories/pn/PNWorld.v                            0    1    5    0    0    0    2    0    7    0    655
theories/relation/BranchWorlds.v                37    0    0    0    1    0    0    0    0    0    690
theories/relation/Creation.v                    11    8    0    0   24    0    0   10    0    0    966
theories/relation/LogicalRelation.v             27    0    0    0    0   22    0    0    0   16   1287
theories/relation/Worlds.v                      47    0    0    0   11    0    0   44    0    0    805
theories/rules/Bind.v                           10    0    0    0    0    0    0    5    0   27    549
theories/rules/BoxRules.v                        4    0    0    0    0    0    0    0    0    9    179
theories/rules/ExRules.v                         3    0    0    0    0    0    0    0    0    0    124
theories/rules/SemanticRules.v                  11    0    0    0    0    1    0    0    0    6    158
theories/rules/TermRules.v                      23    0    0    0    0   11    0   17    0   62   1132
theories/static/FactTheory.v                     6    2   37    0    0    1   13   14   12    0    390
theories/static/Fundamental.v                    7    4   24    0    3    1    2    8    4   15   1218
theories/static/Mixed.v                          3    0    0    0    0    0    0    0    0    2    115
theories/static/PointSubst.v                    16    1   36    0    0    7    5    2    8   11   1204
theories/static/SourceRules.v                    0    0    2    7    0    0    6    0    0   10    269
theories/static/Source.v                         3    1   24   44    1    0   21    2   18   12    432
theories/static/Typing.v                         3    3   12    0    0    0    1    0    9   11    323
theories/types/Types.v                           0   10    0    0   23    0    0    0    0    0   1934
```

## 6. Decisions taken

D1. `new@p` is `t_new_at`, unchanged in Step 1. Its alias stays internal to
the derivation until Step 2 makes `new@p` a primitive typing of `new`.

D2. `link : ∀a. S@a ⊗ dual S@ā ⊸ ∗`. The algorithmic checker compares the
points syntactically.

D3. The forwarder's payload is ∃^{σ̄} κ. {κ ≺ σ}. Close@κ, and Cf replaces
the alias by ρ ≺ σ and σ̄ ≺ ρ̄ (§3).

D4. Congruence.v keeps its name and becomes the one-variable box. Its
purpose (exercise the congruences of ≡) is void without ≡.

D5. FirstAction.v keeps the unused binder ι, to avoid renumbering ζ.

D6. Rejected.v states the two link-based rejections with equal points.

D7. In Step 2 w_eq becomes syntactic equality, not a field equal to `=` (§5).

D8. The translations stay on ≡ in this branch. They are the main obstacle to
Step 2 and are reported, not ported.

D9 (Step 2). `new@x` is a primitive typing `KTNewAt` of `new` (Types.v), and
O-New has a second case: the channel sits at a point the world knows and the
world stays (`new_place`, relation/LogicalRelation.v).

D10 (Step 2). `w_eq W`, `seqs W Ψ` and `heqs Ψ` stay as names for equality
(an abbreviation for `w_eq`, definitions for `seqs` and `heqs`). The ≡ laws
that were record fields or constructors are lemmas over equality under their
old names. Statements keep their text while their content is syntactic
equality. Inlining the names is mechanical and not done.

D11 (Step 2). counterexamples/DropCounter.v leaves the build. Its witness world
aliases (μ,1) with (b,0). The counterexample transfers without ≡ (a fresh point
strictly between (b,0) and (b,1), which no point of W witnesses), but the file
is not rewritten. It has no CheckAll entry.

## 7. Step 2, done

### 7.1 What was removed

- `FEq` (types/Types.v). `fact` has one constructor `FLt`. `fact_holds`,
  `fact_map`, `fact_rel`, `fact_scoped` lost their ≡ branch.
- The alias form of creation constraints: `fresh_eq`, `fresh_at`, the alias
  branch of `fresh_ok` (now `fresh_lt`) and of `fresh_between`, the ≡ part of
  `cc_eq_at`, and the model premise `HCe` of `cc_model` (relation/Creation.v).
  `wext_cc` creates no aliases.
- `alias_bcs`, `cc_ok_alias` and the alias derivation of `t_new_at`
  (static/Fundamental.v), and the alias in `fv_new_open`
  (examples/ChoiceTranslateEx.v).
- `se_h`, `he_h` (≡ facts read from hypotheses) and `se_hyp0`
  (static/Typing.v).
- The `w_eq` field of `world` and the world_wf laws `wf_eq_refl`,
  `wf_eq_sym`, `wf_eq_trans`, `wf_eq_shift`, `wf_eq_payload`, `wf_lt_eq`,
  `wf_eq_supp`, `wf_eq_dual` (relation/Worlds.v). They are lemmas about
  equality now. `wgen N E L` keeps only the order, and `wrestrict` and `wsw`
  (invariance/PointRenaming.v) lost their ≡ component.
- The aliasing rules A-* as constructors. `seqs` (static/FactTheory.v) and
  `heqs` (static/Source.v) are equality.
- Proof steps that converted along ≡, in JunkRenaming, PointConversion,
  Internalize, ConnectSteps, ReadyChain, Bind, TermRules, BranchWorlds,
  Monotonicity, PTerm, PConnect, Fundamental, Mixed.

Line counts over theories/, diff from main cba4a2b: 64 files, 940
insertions, 1152 deletions (Step 1 and Step 2). Step 2 alone, from 7a11f08:
59 files, 662 insertions, 847 deletions. The excluded translations are not
counted as removed.

Remaining occurrences in the built files: `FEq` 0, `w_eq` 393 (abbreviation
for equality), `seqs` 139, `heqs` 65, `pteqW` 148, `teqW` 295,
`steq`/`hsteq` 111, `wf_eq_*` 207 (lemmas over equality), `geq` 69 (closure
of equality generators inside `glt`).

### 7.2 Statements that changed

- `konst_ty` gains `KTNewAt S x : pk x → konst_ty KNew (∗ ⊸ S@x ⊗ dual S@x̄)`,
  and `konst_ty_case` its case. `t_new_at` keeps its statement.
- O-New (`Eobl`, relation/LogicalRelation.v) reads
  `∃ x s s' W', new_place W N x W' ∧ sdual s s' ∧ …` with the entries at x and
  x̄, in place of `∃ a s s' W', NConst a ∉ N ∧ sdual s s' ∧ wext_fresh W
  {[NConst a]} W' ∧ …` with the entries at `pconst a`. `new_place W N x W'` is
  `(∃ a, x = pconst a ∧ NConst a ∉ N ∧ wext_fresh W {[NConst a]} W') ∨
  (pt_known W x ∧ W' = W)`. The step owes less, and the condition is semantic.
  Later (sharp edge 172, constant world, branch lock-freedom) the fresh
  disjunct left as well. O-New reads `∃ x s s', pt_known W x ∧ sdual s s' ∧ …`
  at W, `new_place` is deleted, and Q-Admin and `Ptau_case` keep the world.
- `fresh_ok C := fresh_lt C`. `fresh_between plt C` is the betweenness
  implication alone.
- `cc_model` loses the ≡ premise `HCe`. `cc_ok_out`
  (examples/cfst/CfstTools.v), `c0_acyclic_den`, `c0_acyclic_rank`
  (examples/ExampleTools.v) and `c0_acyclic_prank` (examples/EndPoints.v) lose
  their "no ≡ fact" premise. `fl_map` loses its ≡-hypothesis premise.
- `link : ∀a. S@a ⊗ dual S@ā ⊸ ∗` (Step 1).
- Composition (P-Connect, P-Join, `Prel_connect`, `fundamental_join`): the
  statements are unchanged in text. Their cut conditions read
  `w_eq W e.2 (pt_dual e'.2)`, which is now `e.2 = pt_dual e'.2`. No premise
  was added. `join_jpath` lost its unused well-formedness argument for W₂.

### 7.3 Theorems

Clean build of everything in _CoqProject. CheckAll.v regenerated: 192 entries
built and checked, all closed under the global context, among them
`soundness`, `soundness_source`, `fundamental`, `fundamental_proc`,
`adequacy`, `sem_rules_fundamental`, every core and cfst example, the
forwarder, Milner, Kobayashi, delegation, the choice translation, SemFlag,
SemRounds, DataBranch.

### 7.4 Excluded from the build (NO-EQ: translation pending)

These files left _CoqProject. Their CheckAll entries are commented out with
the marker `NO-EQ: translation pending` (109 entries; scripts/gen-checkall.py
reads _CoqProject).

- pgv: PGVWorld, PGVTranslate, PGVSimulation, PGVExamples, PGVFalling. PGV
  puts both ends of a channel at one point and reads x ≡ x̄ from its world
  (`pgv_eq`).
- pn: PNWorld, PNTranslate, PNExamples, PNSimulation. `crel_fact` holds x ≡ y
  for points with one denotation, and delegation needs the received channel at
  its canonical point (`pay_eq`).
- mp: MPWorld, MPTranslate, MPExamples, MP2World, MP2Typing, MP2Translate,
  MP2Examples, MP2Simulation, MPRounds, MP3World, MP3Typing, MP3Translate,
  MP3Examples, MP3Simulation. The same denotational ≡, and `pex_fact` holds
  x ≡ x̄ for segment points.
- counterexamples/DropCounter.v (D11, no CheckAll entry).

PGVTypes, PGVTyping, PNTypes, PNTyping, PNSemantics, MPTypes, MPTyping,
MP2Types, MP2Semantics and MP3Types stay in the build. They do not depend on
worlds.

### 7.5 What did not work without ≡

- No core lemma became false. The deadlock argument, amalgamation, fresh
  extension, monotonicity, renaming invariance and composition go through with
  ≡ read as equality.
- The translations (§7.4) need the redesign estimated in §5.
- DropCounter's witness needs a new world (D11).
- Not done: inlining the names `w_eq`, `seqs`, `heqs` and `pteqW` (pteqW W x y
  is x = y ∨ (ground ∧ ground ∧ x = y)), removing `geq` and the E parameter of
  `wgen` and `glt`, and deleting the rewriting rules `fl_eql` and `fl_eqr`,
  which close ≺ under equality and are admissible. Each is mechanical.
