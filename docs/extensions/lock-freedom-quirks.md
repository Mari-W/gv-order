# Lock freedom: quirks, weak justifications, and what could be lifted

State of branch `lock-freedom` on 2026-11-16, after L5 and the link redesign,
with L6 (`lf_fundamental`) running. Each entry says what is odd, why it is
there, and what would lift it. Entries marked *artefact* exist for the proof
and not for the idea.

## A. The relations

**A1. Value-level syntactic conditions.** A closure's environment holds
exactly the ends it mentions, a channel value is `Chan c b` with exactly
that entry, a box mentions no channel, and the payload of a send owns
exactly `fchans w ∩ p.1`. They mirror the semantics, which extrudes scope by
syntax (`sentc` removes `fchans v` from C at an external send). Justified,
but it is the one place where the relation reads terms. Lift: no scoping in
the semantics (drop C), scope only in the relation through Σ and Θ, and
ownership validated by use. That changes every process rule and the paper's
calculus.

**A2. The polarity bit `Chan c b`.** *Artefact.* Both ends of a channel share
the name c, so the bit says which end a value is, and it has to agree with
the polarity of the end's point (`pt_pol k = b`). Lift: distinct names for
the two ends (c and c̄). The bit and the agreement disappear, and so does
`tenv_bipol`.

**A3. Two kinds of waiting.** `waits` (Fair.v) reads which ends a term
names. Adequacy cannot use it, because a thread like `(λ_. ()) (λ_. close c)`
names c without owning it. So adequacy runs `lf_run_criterion` with
`hwaits`, waiting by ownership, and `lf_criterion` survives only as the
instance at `waits`. The definitions are allowed to read syntax (author,
2026-11-16), yet the proof needs the semantic one. Lift: define `waits` by
ownership in the first place, if the property can be stated over an
ownership annotation of runs.

**A4. Base and live relation are two copies.** *Artefact of Rocq.* The live
relation copies the base clauses and changes one rule (internal steps
inductive at the same index). Every change to the base relation is redone
in the live one, as L2 and L3a showed. Lift: one relation with a switch.

**A5. Links cost 0.** A link is an internal step (author, 2026-11-08), so a
link loop is τ-divergence. Fine, but it makes link a primitive with its own
cost rule in liveness, in fuel (A10) and in the fragment (B5).

**A6. `LFP` is two conjuncts.** `(∀ n, LPrel n …) ∧ ∃ q P F, ∀ n, LFsoup …`.
Every thread of the soup is already in the live relation, so the first
conjunct may be redundant. Composition uses it (`LPrel_connect`), so it
stays until someone checks.

**A7. The soup fixes q, P and F before the index.** *Artefact.* q is an
instrumented configuration with thread identifiers, P the point map per
thread, F the counters per thread. P and F are determined by the run
(syntactic points, value conditions), so a determinism lemma would make them
derived. They are existential because extracting one function from "for
every n there is an environment" needs that lemma or a choice principle.
Thread identifiers are an artefact of the instrumented semantics. Lift: the
determinism lemma, then P and F are read off the environments.

**A8. `prim T` and `lf_sig`, `lf_own` in the soup.** `prim T` excludes a main
thread that ends as a value while holding an end. `lf_sig` and `lf_own` tie
the environments to Σ and are trivial for closed programs. Both are honest
side conditions, yet they make the definition longer than its idea.

**A9. Index loss.** A soup step goes from index n + 2 to n, and the
replacement clause costs one more level. Harmless for `∀ n`, ugly to state.

**A10. Fuel sits on ends, not on obligations.** The idea is that a counter
belongs to an obligation ("someone waits for this end"), and every hand-over
(send, spawn, link) costs one. The mechanization keeps counters per held
end, so a link *overwrites* the peer's counter, and every end at point k has
to tolerate such an overwrite down to `w_pay W k` (`frep`). Lift: make
obligations explicit in the soup (waiter, serving end, counter), with the
per-thread predicate reading them.

**A11. Two budget maps, one keyed oddly.** The world has `w_bud` (cap and
refill) and `w_pay` (floor of a delegated end). The floor is read at the
*sender's* point, because sender and receiver sit at dual points. The link
minimum reuses it at u's point. Lift: key the floor on the carrier channel's
identity rather than on a point, if the world can speak about it, or fold
both maps into one budget per root.

**A12. Budget ∞ and `ftravel`.** Ends nobody waits on get ∞, which replaces
"fuel ticks only while the partner offers" (§7). Only ends with a finite
partner budget may travel in a message (`ftravel`). The restriction is
sound (acting on an ∞ end can starve) but excludes delegating idle ends.
Lift: let ∞ ends travel and forbid only *acting* on them, if F-Wait alone
carries the argument.

**A13. Kripke closure needs name inclusion.** `FuelE` is closed under
`wbext W W'`, which asks W′ to know W's names and agree on their budgets.
Bare budget agreement is not transitive. Composition then asks `wbud_agree
W1 W2` on *every shared name*, not only at the cut. Lift: if FuelE only ever
reads budgets at points the world knows, agreement at the cut suffices.

**A13b. Replacement minimum against the send floor (open, 2026-11-16).**
The replacement clause lets another thread's link lower a counter to the
floor at the end's *own* point, while a send asks counter − 1 ≥ the floor
at the *carrier's* point. A delegated end sits at a payload point of its
carrier, so with floors keyed on roots both floors are equal and the send
fails. The Forwarder is in the fragment and fails the fuel predicate at
every world `with_budgets` builds (`fw_not_fsem`, `lf_fuel_fundamental_fails`
in LFFuelTyped.v). Two candidate repairs. Exempt from replacement every end
whose partner the same thread holds, because no other thread can link it
(environment-level). Let floors grow along payload fields, so a payload's
own floor exceeds its carrier's (fragment budgets). Not decided.

**A14. `well_founded (w_lt W)` beside `world_wf W`.** Two premises about the
world, one structural and one for rank. Could be one record field of a
"lock-free world".

## B. The static fragment

**B1. A pile of syntactic checks.** The guard, R1 (recursion in tail
position), R2-recv (ends passed to a call were acted on in the round or
are fed slots), the hand-off graph (forwards and links), the root graph,
`wf_world (cworld Ψ)`, and the annotation `ann` backed by typing
derivations. Each closes a counterexample. Together they are a sufficient
condition, not a characterisation. Lift: semantic premises wherever the
proof allows. The controller already types only by a direct semantic proof.

**B2. The root graph and its restrictions.** Floors are keyed on the *root*
of a point because the term records roots (syntactic points) and nothing
else about types. A box that forwards must keep its slots stable from round
to round (`stab`) and must not be called from inside a box (`foreign`). A
received end passed into a call leaves the program without a root graph
(`troots`, `bleak`). No example is affected, but the rules exist only to
make the root graph computable.

**B3. The stretch bound.** L = 2 · `seg_len`, with `scost` charging one unit
for a channel step, a spawn and a link, inlining forced non-recursive boxes,
and ending a segment at any other force. The factor 2 ("a stretch spans at
most two segments") was only argued when written and is being proved in L6.
Budgets are uniform, (d + 2)·L for every end, and floors fall by L per level
of the root graph.

**B4. Leading point parameters.** A box's leading λs count as fresh point
parameters only when its annotated type says `TPt`. The checks read the
annotation, and the annotation needs a typing derivation (`r2h_ok`). A
syntactic check leaning on a semantic certificate.

**B5. Links inside boxes are rejected.** The type hand-off graph gives every
link inside a box a self-loop. That was the old way to close C3. With links
accounted like sends (option 2), fuel closes C3 itself, so the self-loop
rule may now reject more than needed. Lift: drop it and let the link
accounting do the work.

**B6. Recursion with a point argument needs a primitive first.** The guard
asks the first argument of a forced self to perform a primitive, and a point
value performs none. C1 and C3 had to be rewritten so the chatter comes
before the call. GuardCex could not take a point parameter at all.

## C. Syntactic points and the constant world (calculus level)

**C1. Points in terms.** `new` takes a point value, boxes take points as
λ-arguments of type `TPt ι`, and `KPay`, `KSucc` build points at runtime.
Needed so that O-New does not choose a point inside each index (§14). The
runtime never uses the points. They exist for the proof.

**C2. Source soundness says nothing about channel creation.** A program over
the point variables of C₀ cannot name a ground point, so it cannot create a
channel. `soundness_source` and `synth_deadlock_free` stay true but say
little, and the old rejection theorems became weak. Every creating program
goes through creation hypotheses (`soundness_created`).

**C3. Choice is no longer derivable syntactically.** ChoiceTranslate creates
a channel at the carrier's point, which the source term does not name.

**C4. TreeSum's result has no point.** SegmentInterleave and SegmentDeleg
need TreeSum's box result to carry a `TPt`. Author's decision, open.

**C5. The constant world must hold every point a run uses,** infinitely many
under recursion (ι + k, ι[k]). Four box types got stronger (FreshBetween,
FreshMany, FactoryEx, GuardCex) because a channel can no longer be squeezed
between two points at runtime.

## D. Scope

**D1.** No select and no mixed choice, so weak fairness suffices.
**D2.** No termination. Fair termination (Padovani and Zavattaro 2025) is out.
**D3.** Data-dependent postponement and non-tail recursion (TreeSum, fact,
fibo, mergesort) are outside the fragment. R1′ would admit TreeSum.
**D4.** The translations PGV, PN and MP are out of the build.
**D5.** SemFlag's underivability has been open since the end-points port, so
"semantic typing types more" is proved only on the semantic side.

## E. Is it nice?

The idea is small. The order on points rules out circular waiting and, being
well founded, endless chains of waiting. Fuel per obligation rules out
endless postponement and endless hand-over. Ownership and points fixed for
the run make both survive step-indexing. The mechanization carries many
artefacts around that idea (A2, A7, A9, A10, A11, B1 to B6, C1). For the
paper, present the idea with three definitions (the gate, fuel per
obligation, ownership per run) and keep the artefacts in the appendix or the
artifact description.
