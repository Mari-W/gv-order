# End points

Every end of a channel has its own point. The two ends of one channel sit at
dual points x and x̄, and the gate compares the blocking point with the partner
points of the held ends. A thread blocked at u that holds an end at v owes
u ≺ v̄. Branch `end-points` implements this on the whole development. The
program of `theories/examples/EndPoints.v` types under it and has no typing in
the collapsed system.

## Why

PGV gives both ends of a channel one priority, and so did this system. It
collapses Kobayashi's pair of obligation and capability into one point. A
thread that receives a bit and then closes c before d or d before c needs
γ ≺ δ in one branch and δ ≺ γ in the other, a cycle on two points. The program
is deadlock free, because the partners of c and d close at once.

With end points the two branches owe γ ≺ δ̄ and δ ≺ γ̄. These four points carry
no cycle. In synchronous rendezvous the obligation of an end is the capability
of its partner, so one transitive strict order still suffices.

The deadlock argument reads as follows. Take a blocked end whose point u is
least. Its partner holds ū. If the partner is blocked at w, its gate gives
w ≺ dual(ū) = u, against minimality. Otherwise the partner offers the dual
action and the two step. `theories/composition/ReadyChain.v` carries this
argument out for two components over a cut (`step_l`, `step_r`, `descent`).

## Definitions as implemented

Points (`types/Types.v`). `Record point := MkPt { pt_name; pt_pol : bool; pt_off }`
and `Pt p o := MkPt p true o`. The dual `pt_dual x` flips the polarity. The
shift `pt_shift` keeps it. The payload point `pt_payload x i` ignores the
polarity of x and is positive, so x̄[i] = x[i] holds by computation. An
instance `pt_inst σ x` reads the variable at the polarity of the occurrence
(`pt_polar`). The identities are `pt_dual_dual`, `pt_dual_shift`,
`pt_payload_dual` and `tpt_inst_dual`.

Heads. `heads (S@x) = {x̄}` and `ends_heads` gives the partner points of the
entries of Θ. Lower bounds of arrows and of ∃ live among these partner points.
Upper bounds stay at the end's own point.

Program order. `ppo` gains `ppo_dpo x : ppo x (x̄+1)`. An end acts before the
next action of its partner. `geq` gains `geq_dual`, `glt` gains `glt_dpo`.

Worlds (`relation/Worlds.v`). `world_wf` gains `wf_eq_dual` (x ≡ y gives
x̄ ≡ ȳ) and `wf_lt_dpo` (x ≺ x̄+1). Support stays a set of names, so both
polarities of a name come with it.

Readiness (`relation/Readiness.v`). `below_rest` asks the offered head below
`pt_dual` of the head of each held entry that is not offered, and below the
future F. `above_offered` asks some offered head below the partner point of
each held entry. The gate {u} ≺ F of E-App is unchanged in text, because F
collects heads, which are now partner points.

Duality of two ends. Everywhere the relation and the static system asked
x ≡ y for the two ends of a channel they now ask x ≡ ȳ: `tenv_dual`,
`tenv_comp`, `senv_dual_on` (types/SessionEquiv.v), `send_split`, O-Link and
Q-Link (relation/LogicalRelation.v), the cut of P-Connect (`cut_ok`,
`Prel_connect`, `ptyped`), `tenv_move` (invariance/JunkRenaming.v). The
composition lemmas take the symmetry `rdsym R` (rules/Bind.v), which worlds
give by `wf_rdsym` and the fact theory by `se_dsym`.

Constants.

```
new     : ∗ ⊸ ∃^⊥ ι. C. S@ι ⊗ dual S@ῑ
selectᵢ : ⊕(S₁, S₂)@ι ⊸^ι Sᵢ@(ι[i])‾          {ι ≺ ι[i]}
branch  : &(S₁, S₂)@ι ⊸^ι S₁@ι[0] + S₂@ι[1]    {ι ≺ (ι[0])‾, ι ≺ (ι[1])‾}
link    : S@ι ⊗ dual S@ι′ ⊸ ∗                   {ι ≡ (ι′)‾}
send    : (P[ι] ⊗ (!P;S)@ι) ⊸^ι S@(ι+1)        {ι ≺ h ∣ h ∈ heads(P[ι])}
```

The selecting end continues at `sel_pt x i = (x[i])‾` and the branching end at
`bra_pt x i = x[i]`, so the two ends stay at dual points. Select keeps its
constraint ι ≺ ι[i]. The payload heads of send are now partner points of the
payload ends. O-Select, O-Branch, Q-Select and Q-Branch move the entry to
`sel_pt` and `bra_pt` (`Pchoice_case` takes the target).

Fact theory (`static/FactTheory.v`, `static/Source.v`). `seqs` gains `se_dual`,
`fl` gains `fl_dpo x : x ≺ x̄+1`, and the hypothesis-only theory gains `he_dual`
and `hl_dpo`. `fl_map` asks the two matching closure conditions.

Creation constraints (`relation/Creation.v`). The model lemma `cc_model` asks
the map φ to commute with the dual and the order inside ι to contain
x ≺ x̄+1. `gen_map` and `cc_ok_transfer` ask the map to commute with the dual.

## The channel fact shorthand

x̂ stands for both ends of x. A fact that mentions x̂ abbreviates the facts for
every end it names.

```
x̂ ≺ ŷ  :=  x ≺ y, x ≺ ȳ, x̄ ≺ y, x̄ ≺ ȳ
x ≺ ŷ  :=  x ≺ y, x ≺ ȳ
x̂ ≡ ŷ  :=  x ≡ y        (x̄ ≡ ȳ follows by se_dual)
```

Hats commute with offsets and payload points, because x̄[j] = x[j]. The ports
of the translations and of most examples state each old fact between all
polarities of its two points, written `pt_polar c x ≺ pt_polar c' y`. The
algorithmic example `cycle_a` creates its second channel under `hat_lo x`,
the constraint x̂ ≺ ι̂ (`theories/algorithmic/Examples.v`, `cc_ok_hat_lo`).

Delegation shows both ways. The old constraint {ι ≺ ι[0], ι[0]+1 ≺ ι+1}
hatted expands to eight facts. The port keeps the end-precise constraint
`dl_C` of five facts, which the eight facts contain.

Only examples whose point is the new expressiveness use unhatted facts. In
`EndPoints.v` the hatted constraint would contain γ ≺ δ and δ ≺ γ, a cycle,
which is the old rejection.

The PGV, PN and MP translations go further. Their worlds read every point
through a denotation that ignores the polarity, so they relate x ≡ x̄ for every
point they mention. Such a world is strict and well formed (x ≺ x̄+1 becomes
x ≺ x+1), and the gate u ≺ v̄ reduces to u ≺ v there. The MP versions 2 and 3
state the same alias as a fact of their segment and existential constraints,
`mwalk κ u ≡ (mwalk κ u)‾`.

## Conservativity (paper argument, not mechanized)

Hatting every fact of the creation and box constraints of a derivation of the
collapsed system gives a derivation of the end-points system. First, the map
x, x̄ ↦ x sends the hatted facts onto the old facts and x ≺ x̄+1 onto x ≺ x+1,
so the hatted constraint is acyclic exactly when the old one is. Second, each
new gate fact u ≺ v̄ is one of the four expanded facts of the old u ≺ v. Adding
ι ≡ ῑ to each creation constraint alone does not suffice, because a carried end
also needs x[j] ≡ (x[j])‾ and A-Payload does not derive it from ι ≡ ῑ. No Rocq
theorem states this argument.

## The examples

`theories/examples/EndPoints.v` holds the bit program.

```
bit = let (e, e′) = new ε in let (c, c′) = new γ in let (d, d′) = new δ in
      spawn (λ_. close (send ⟨inj₁ ∗, e′⟩));
      spawn (λ_. close c′); spawn (λ_. close d′);
      let (v, e) = recv e in let () = close e in
      case v { inj₁ u ⇒ u; close c; close d
             | inj₂ u ⇒ u; close d; close c }
```

It types under the top-level constraint
C₀ = {ε+1 ≺ γ̄, ε+1 ≺ δ̄, γ ≺ δ̄, δ ≺ γ̄} (`bit_typed`, a `styped` derivation).
`bit_C0_acyclic` shows C₀ acyclic with a rank that reads the polarity, and
`bit_deadlock_free` follows from `soundness_source`. `c0_acyclic_prank` is the
acyclicity lemma for such ranks. `bit_collapsed_cyclic` records that the two
branch facts read on one point per channel admit no strict order.

The classic deadlock stays rejected. `dl_untypable_source`
(examples/cfst/CfstDeadlock.v) shows for every acyclic C₀ that the classic
deadlock of Mordido and Pérez has no `styped` derivation, and its proof did not
change. GrowDeadlock still needs x ≺ ȳ ≺ x.

The proxy (receive a channel, then order it against the carrier by a received
value) is not written.

## Theorems whose truth changed

These theorems relied on the collapse. The inversion of a derivation now yields
x ≺ ȳ and y ≺ x̄, or δ ≺ (x[0])‾ and x[0] ≺ δ̄, instead of a two-point cycle.
That pair is consistent with x ≺ x̄+1. Each theorem is commented out in place
with the mark `END POINTS: open`. None of them is proved false in Rocq.

- `examples/ChoiceNegative.v`: `t2i_underivable`, `t2_underivable`,
  `bodyg_underivable`, `body0_underivable`, `body0_underivable_top`,
  `negative_new_at`. The program with both arms at one payload point now
  appears typable and deadlock free. A derivation needs a top-level constraint
  with a[0] ≺ δ̄ and δ ≺ (a[0])‾, which `c0_acyclic_prank` can order. It is not
  written.
- `examples/DataBranch.v`: `db_component_unrealizable`, `db_component_sides`,
  `db_component_untyped_top`, `db_rnode_unrealizable`, `db_rnode_untyped_top`.
  The hypotheses {x ≺ ȳ, y ≺ x̄} are realizable and appear to type both
  branches.
- `examples/SemFlag.v`: `sf_underivable`, `sf_underivable_top`. The open term
  appears typable for the same reason. The closed configuration still has no
  static derivation, because the dead arm needs y ≺ x̄ and the partner needs
  x̄ ≺ y. `sf_deadlock_free` and `sf_mixed` hold, the latter with the extra
  hypothesis x̄ ≺ y. The semantic running example of the paper therefore has to
  be restated at the level of the configuration.

The underivability theorems of `examples/Rejected.v`, `examples/lit/LitRejected.v`,
`examples/FreshBetween.v` (`fb_between_underivable`) and `pgv/PGVExamples.v`
(`cx1_rejected`, `cx2_rejected`) still hold. `rr_call_underivable` now states
¬ ι+1 ≺ (ι′+1)‾, the same claim at partner points.

The documents docs/extensions/choice-encoding.md, SMALL-THEOREMS-REPORT.md,
DATA-DEPENDENT-REPORT.md, semantic-examples.md, data-dependent.md and
data-dependent-worlds.md still cite the commented-out theorems.

## Statements that changed and still hold

No deadlock-freedom statement and no source-level statement of PGV, PN or MP
changed. Constraints of the positive examples grew, mostly by hatting. Helper
lemmas changed where they mention a choice continuation or a head, among them
`sel_typed`, `sel1_typed`, `sel2_typed` and `branch_typed` (ChoiceEnc.v, which
now return Sᵢ@(x[i])‾), the fragment `fstyped` of ChoiceTranslate.v, `cc2_ready`,
`db_case_lt` and `db_rnode_lt` (DataBranch.v), and the hypotheses of the SemFlag
and SemRounds lemmas. `t_new_at` (static/Fundamental.v) types the body with the
second end at x̄.

## Things to look at

E-NewFresh admits ι ≺ δ̄ together with δ ≺ κ without ι ≺ κ. The betweenness
check of `fresh_between` compares a lower fact at p with an upper fact at q
only when p is at or before q in program order (`ple`), and δ̄ is not before δ.
`cc_ok_fresh` is proved, so the rule stays sound, but it is a new freedom.

The choice encoding of `ChoiceEnc.v` needed two payload points per sum to avoid
a cycle. With end points one shared point no longer produces a cycle.
