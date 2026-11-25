# Report on the algorithmic system (2026-11-04)

Branch `algorithmic`, from `algorithmic-notes` (main plus the two working
notes). The head is the commit that adds this file. Earlier commits on the
branch add docs/extensions/algorithmic-bidir.md,
docs/extensions/algorithmic-decidable.md, theories/algorithmic/ and prototype/.
Nothing under paper/ or docs/TOUR.md changed. No existing theories file
changed. _CoqProject gained three lines and docs/extensions/README.md one
paragraph.

## 1  What was asked and what is delivered

| question | deliverable | status |
|---|---|---|
| 1 bidirectional formulation with effects | docs/extensions/algorithmic-bidir.md, rules in full for the core and choice, CFST sketched | designed |
| 2 soundness for `styped`, mechanized | theories/algorithmic/Algorithmic.v, Soundness.v, Examples.v | mechanized, axiom free, full build passes |
| 3 decidable fragment | docs/extensions/algorithmic-decidable.md, three fragments with procedures and proofs, coverage table, undecidable extension | paper proofs, not mechanized |
| 4 prototype | prototype/checker.py, prototype/examples.py | runs on sync, cycle, blocked (rejected), delegation, request and reply |

## 2  Design (algorithmic-bidir.md)

Two judgments, synthesis Φ ; Δ ⊢_F t ⇒ T ⊣ 𝒞 and checking
Φ ; Δ ⊢_F t ⇐ T ⊣ 𝒞, both with the fact context as output. The three effects
and their modes.

- The future F is inherited in both modes, extended by the heads the context
  still holds exactly as the declarative rules do.
- The upper point u of an arrow is synthesized with the arrow and checked at
  every application by the gate u ≺ F, resolved at generation time against Φ
  into u ≺ P and u ≼ u′ for the one hypothesis u′ ≺ φ of the frame variable.
- The lower point ℓ is checked at the λ against the heads of the captured
  environment.

Constants are instantiated by matching their scheme against the synthesized
argument type after the head normal form unr is taken. This is the only
conversion the algorithm performs. All other agreement between types is
matching up to points, which emits ≡ atoms. Linear environments split by
occurrence. The constraint language has atoms x ≺ y, x ≡ y, x ≼ y, u ≺ P,
ℓ ≼_b H, known x, cc(C) and false, conjunction, and a binder ∃ι:C. 𝒞 for the
fresh point of a new.

Annotations stay at boxes (points, session variables and constraint), at
pack (the existential type), at λ and inj in synthesis position, and at new
unless the program has no boxes, where Section 7 of the document infers the
creation constraints by generating, saturating, checking acyclicity and
slicing the closure by the innermost root. The slicing is what sharp edges 144
did by hand. [derived] on paper.

Standard versus specific is Section 5 of the document. Standard are the mode
discipline, the occurrence split, latent and ambient effects, and the
coeffect-like capture rule. Specific are effects as points of a program-defined
partial order compared by entailment rather than joined in a lattice, the frame
variable as its own sort resolved against one hypothesis, ≡ atoms solved by
congruence closure with integer potentials rather than unification, the ⊥ flag
as a third value of a future, and new with a whole constraint as its unknown.

## 3  Proved on paper

- Soundness of the checking mode by ⇐Sub and ⇐Abs [derived], not mechanized.
- The inference of creation constraints by slicing produces constraints that
  are acyclic and conservative whenever the global closure is acyclic
  [derived], Section 7 of algorithmic-bidir.md.
- algorithmic-decidable.md, Lemma 1 (aliases with thresholds), Lemma 2 (one
  segment), Theorem 1 (𝔇₁ strictness and entailment), Theorem 2 (creation
  constraints of shape A, both directions), Theorem 3 (uniform one-counter
  schemas, zero-weight closed walks by signs of simple cycles), Theorem 4
  (monotone one-counter schemas with constants, bounded abstraction). All
  [derived] with proofs in the file.
- Theorem 5 (regular walks) rests on the decidability of the monadic
  second-order theory of prefix-recognizable graphs, [known, uncited, verify].
- General one-counter schemas with negative shifts and constants rest on
  reachability in one-counter automata, [known, uncited, verify].

## 4  Mechanized

Files, all new, registered in _CoqProject.

- theories/algorithmic/Algorithmic.v. Atoms, constraints, `csat`, the
  annotated terms `aexpr` with `erase`, decidable type equality `ty_eqb`,
  matching `tmatch`, the constant rules `konst_app`, and the checker
  `synth : nat → fhyps → lenv → sframe → aexpr → option (ty * constr)`, a
  Fixpoint.
- theories/algorithmic/Soundness.v. `synth_sound`:
  `fv_below n Φ → synth n Φ Δ F a = Some (T, c) → csat Ψ c → styped Φ Ψ Δ F (erase a) T`.
  `synth_deadlock_free` says that a closed program accepted under C₀, whose
  constraint holds in [(C₀, ids m)] and whose C₀ is a creation constraint
  against the empty context, is deadlock free. `st_new_open` is `t_new_open` in `styped`.
- theories/algorithmic/Examples.v. `sync_a` and `cycle_a` are the annotated
  sync and cycle, `sync_a_erase` and `cycle_a_erase` show the erasure is the
  term of Sync.v and Cycle.v, `sync_a_type` and `cycle_a_type` run the checker
  by `vm_compute`, and `sync_a_deadlock_free`, `cycle_a_deadlock_free` are
  deadlock freedom through `synth_deadlock_free` with the constraint
  discharged by hand in the context of the creation constraints.

`Print Assumptions` on `synth_sound`, `synth_deadlock_free`,
`sync_a_deadlock_free` and `cycle_a_deadlock_free` says "Closed under the
global context" for each.

Build. Rocq 9.2.0 with rocq-stdlib 9.2.0 and rocq-stdpp 1.13.0 (pinned from
the gitlab checkout of tag stdpp-1.13.0, because the release tarball was not
reachable from the container). `make -j4` over the whole _CoqProject, the
three new files included, finishes with no error.

The mechanized fragment is the synthesis judgment on annotated terms. λ
carries its bounds and argument type, inj carries the other arm, new carries
its session type and creation constraint. No box, no force, no pack beyond new,
no bare constant, no session variables. Session types compare syntactically
after `hd`. What stays on paper is listed in Section 9 of
algorithmic-bidir.md.

## 5  The decidable fragments (algorithmic-decidable.md)

| fragment | constraints | questions decided | procedure | cost |
|---|---|---|---|---|
| 𝔇₁ | finite ground facts ≺ and ≡ | strictness, entailment, cc of shape A (order facts) and shape B (one alias) | union-find on names with integer potentials and thresholds, payload congruence to a fixpoint, one weak segment per pair, cycle through a strict edge | polynomial |
| 𝔇₂ᵘ | shift schemas ∀k. (p, k+a) ≺ (q, k+b) | strictness, ground and schema entailment | signs of simple cycles per strongly connected component, Bellman–Ford | polynomial |
| 𝔇₂ᵐ | shifts with δ ≥ 0, fan-down, fan-up, ground | strictness, entailment | abstraction of offsets to {0..B, ⊤} plus 𝔇₂ᵘ on the ⊤ part | polynomial in \|N\|·(B+2) |
| 𝔇₂ | negative shifts with constants | strictness | one-counter automaton reachability | decidable, [uncited] |
| 𝔇₃ | ∀w ∈ L. (r, w u) ≺ (r′, w u′), ceilings, floors, root aliases | strictness, entailment of regular schema sets | prefix-recognizable graph of the words r·wᴿ, monadic second-order logic | decidable, nonelementary by that route, [guess] polynomial for acyclicity |

Alias schemas with a shared counter are the same theory as one ground alias,
so 𝔇₂ adds no ≡ structure over 𝔇₁. Every box constraint and creation
constraint of theories/examples and theories/examples/cfst lies in 𝔇₁, 𝔇₂ᵘ,
𝔇₂ᵐ or 𝔇₃ as written, with the one exception of the rank-defined constraints
of CfstScheduler.v, which generate a 𝔇₂ᵐ theory after residue splitting
[guess, not checked in detail]. The coverage table is Section 4 of the
document. The translations pgv, pn and mp type at rank-defined worlds and are
certificate checked, not fragment checked.

The natural extension that becomes undecidable is a schema that rewrites the
middle of a word with counters on both sides, which is the two-counter
encoding of algorithmic.md Theorem 5 read on words. Between 𝔇₃ and that lie
two counters per word, the relay with one more level, which is open.

Where SMT takes over. Outside the fragments and inside them when the exact
procedure is not implemented, the ranking certificates of algorithmic-smt.md
and egg-smt-demo.md are the route, checked by `lia`. The fragments are complete
for their questions, the certificates are not.

## 6  Prototype

`python3 -I prototype/examples.py` prints

```
sync           accepted  type TUnit  6 atoms  ok
cycle          accepted  type TUnit  13 atoms  ok
blocked        rejected  type TUnit  13 atoms  missing fact ι0 ≼ ι1
delegation     accepted  type TUnit  19 atoms  ok
rq_C strict    True
rq_C[σ] ⊆ C    True
rq body atoms  True
rr_call ι+1≺ι′ False  (rejected in Rejected.v)
rq_rejected    False  (a zero cycle, not strict)
all checks passed
```

The prototype implements synthesis for the core and choice, the 𝔇₁ procedure
with thresholds and payload congruence, creation constraints of shapes A and
B, and the 𝔇₂ᵘ sign test. Boxes are not terms of the prototype. Request and
reply is checked at the level of its constraint, which is what a force asks.
TreeSum was not run. Its constraints are in 𝔇₃ and the prototype has no 𝔇₃
procedure.

## 7  Open problems

- Checking mode and boxes in the mechanization. The soundness proof of ⇐Sub
  and ⇐Abs is a few lines on paper. Boxes need `synth` to handle hypotheses Ψ
  and `bcs_hold` atoms, and the body under the box's hypothesis.
- Bisimilarity of session types in `tmatch`. The algorithm compares session
  types syntactically after `hd`, so a channel returned at α;Skip against
  (α;Skip);β fails. The declarative system allows it by E-Conv.
- Creation constraints with several aliases. Theorem 2 covers order facts and
  Shape B the single alias ι ≡ w. The general case is decidable in principle
  by Theorem 1 on Γ + C, but the finite set of outer points to check for
  conservativity is only conjectured.
- A self-contained proof for general one-counter schemas, and for 𝔇₃ a direct
  pushdown argument in place of monadic second-order logic, with a complexity
  bound.
- Mechanization of the decision procedures. Nothing of Section 5 is in Rocq.
- The bounds of a spawned thunk. Section 7 of algorithmic-bidir.md picks the
  upper point of a spawned thunk among its blocking points or introduces a
  fresh top-level variable above them. Whether this loses programs is a
  conjecture.
- Inference of box constraints. The invariant C = ⋃ₖ C₀[σᵏ] of
  algorithmic.md is not run or checked here.

## 8  Proposals for the declarative system

Neither was applied. Both come with a concrete program.

P1. A set-valued lower bound. A spawned thunk that captures two channels at
unrelated points γ and ε has no lower point. E-Abs needs {ℓ} ≼ heads(Δ), so
the program must order γ and ε by a creation constraint that nothing else
asks for. In cycle this is harmless, because the closes order them anyway.
The program `let (c, c′) = new in let (d, d′) = new in spawn (λ(). let () = close c′ in close d′); let () = close d in close c`
has one thread closing c′ before d′ and the other d before c, so no order of
γ and ε serves both λ-bounds. The future is already a set. An arrow
T ⊸^u_L U with L a finite set of points and heads(T ⊸^u_L U) = L would let
E-Abs ask L ⊆ heads(Δ) up to ≡ and E-App run the argument under F ∪ L. E-Pair
already runs the second component under F ∪ heads(T). The semantic clause
V-Abs would change {ℓ} ≼_W heads(Σ) to L ≼_W heads(Σ) pointwise. Not checked
against the relation.

P2. A top upper point for spawned thunks. The thunk of spawn needs an upper
point u although spawn never blocks and the thunk is never applied. In sync
the annotation is ι+1, the last action of the thunk, and the algorithm has to
find it. An upper point ∞ above every point and below no frame variable would
make V-Abs quantify over F = ∅ only, which is the future a spawned thread runs
under, and E-App at ∞ would require F = ∅. spawn's scheme already takes any
u. The change is a new constant point in the fact theory with ∞ ≺ nothing and
x ≺ ∞ for every point x. Not checked against the relation.

## 9  Reproduction

```
eval $(opam env)                       # rocq 9.2.0, rocq-stdpp 1.13.0
ulimit -s 1000000; make -j4            # whole development, the three new files included
python3 -I prototype/examples.py       # the prototype on the examples
```

`Print Assumptions synth_sound.` after `From LRGV Require Import algorithmic.Soundness.`
answers "Closed under the global context".
