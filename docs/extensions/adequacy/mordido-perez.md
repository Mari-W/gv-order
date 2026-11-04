# D.3 Adequacy for Mordido and Pérez (2026)

Notation: this file up to the section "Ported to the exists core" predates 2026-11-04 and writes p.j for the point now written p[j]; 'slot' and 'carried root' mean that point.

Status. Stage 1 done on 2026-10-31, research and design. Stage 2 mechanized on
2026-10-31 in theories/mp/ on branch cfst, first for fragment v1 and then as
version 2, which covers context-free session types, session type variables and
functions over unbounded segments (section 12, restriction log in section 13).
Version 3 on 2026-11-01 adds n-ary choices and channels created after a segment
call, and program 8 shows that a recursive body must type at every round
(section 15). Same procedure as for PGV (pgv-adequacy.md) and Padovani and
Novara (padovani-novara.md).

Source. A. Mordido and J. A. Pérez, Deadlock-Free Context-Free Session Types,
LNCS 2026, DOI 10.1007/978-3-032-28187-6_11. Indexed as mordido2026deadlockfree
with the full text of arXiv 2506.20356v4. Page numbers are pdf pages of that
copy, which match its printed numbers. The main text states the rules in
excerpts (Figs. 6, 8) and the appendix completes them (Figs. 9 to 15, pp. 22 to
30). Every claim about the paper below is recorded in the store with its page.

## What the system is

A call-by-value GV with fork, new, send, receive, select, match, close and wait,
and context-free session types in the style of Thiemann and Vasconcelos (p. 2,
p. 8). Every synchronization carries a priority, and Skip and ; carry none
(p. 7). Arrows T →^{ρ₁,ρ₂}_m U carry the lower bound of the closure and the latent
effect, as in Padovani and Novara (p. 6). The judgment
Δ | Γ | Θ | Ψ ⊢ e : T ⋄ π̄ ⋄ ρ has a priority map Ψ from channel variables to
priority sequences, a sequence π̄ that new emits, and an effect ρ (p. 11).
Configurations are GV's, with a main thread and child threads (p. 14).
Communication is synchronous (R-Com, R-Ch, R-Close, p. 30). Theorem 1 is
preservation, Theorem 3 deadlock freedom for closed configurations (pp. 15, 16).
The examples are the classic deadlock (p. 3), two streams in a cycle (p. 4), the
tree channel (p. 5, p. 21) and Milner's scheduler (pp. 37 to 39).

## Stage 1 results

Five closed programs type and get stuck (section 6 and
mordido-perez-counterexamples.txt). Two come from the type of a partial send,
one from priority sets in the payload check, two from the semantics of fix and of
inst. Each has a local repair. Beyond them the rules leave the use of Ψ in
function bodies underspecified (section 7). For the translation, one new obstacle
matters most. Our choice puts both branches at the same instant, while their
branches may order a channel differently against others. Section 9.5 gives a
deadlock-free program that they type and we reject.

### 1  Priorities, sequences and the priority map

Priorities are ρ ::= ⊥ | n | ⊤ | ι | ρ + n with ⊥ + n = ⊥ and ⊤ + n = ⊤ (p. 6,
p. 7). Intervals φ are open or closed at either end. Session types are

```
S ::= Skip | !^ρ T | ?^ρ T | ⊕^ρ{ℓ: Sℓ} | &^ρ{ℓ: Sℓ} | S;S | Close^ρ | Wait^ρ | β | µβ.S | ∀^S ι^φ.S
T ::= Unit | T →^{ρ₁,ρ₂}_m U | T × U | α | µα.T | ∀α^ρ.T | ∀^F ι^φ.T | S             (Fig. 1, p. 6)
```

No sums and no base type besides Unit. Int, Tree and data declarations appear
only in the FreeST examples. Duality keeps priorities (p. 8, p. 23).

A priority sequence belongs to a channel, not to a type. new S^∀ n₁ n₂ takes a
session type with a priority binder ∀^S and emits π̄ = [n₁ + k·n₂ ∣ k ∈ ℕ] with
n₂ ≥ 1 (T-NewPoly, p. 12, n ::= 1 | 2 | … on p. 8). T-LetPair maps both new ends
to π̄ in Ψ (p. 12). inst x takes the head of Ψ(x) and instantiates the binder
(T-Inst, p. 12), and T-Let pops that head for the continuation (p. 13). next x
names the head of Ψ(x) and instantiates function priorities, as in
client{next c1} (p. 4). ∀^S occurs at most once in a well-formed type, under an
empty Θ (F-PAbsS, p. 7). Each recursive unfolding of µβ.∀^S ι.S₀ consumes one
element of the sequence.

The priority of a type is a set of integers (Fig. 4, p. 11). For an action head it
is the action's priority, for an arrow the lower bound, for a product the
minimum. For a polymorphic session type it is the union of the instances over
every variable of that type in Ψ and every element of its sequence. "ρ < |T|"
asks ρ below every element, while T-TApp asks ρ ∈ |T| (p. 10, p. 12).

Ψ is no linear resource. T-App and T-Let hand all of Ψ to the first premise,
T-Let and T-LetPair hand the popped Ψ₂ to the second (p. 13). T-AbsLin and
T-AbsUn pass Ψ to the body unchanged (p. 25).

### 2  Priority polymorphism over intervals

∀^F ι^φ.T abstracts a priority in a functional type (F-PAbsF, p. 7). T-PAbs
types Λι.e with an unrestricted context, and T-PApp instantiates at any ρ ∈ φ
(p. 12). Interval bounds may mention enclosing priority variables, which is how
the constants order their priorities. send asks ι₂ ∈ (⊥, ι₁) for the action
against the payload ι₁ and ι₃ ∈ (ι₂, ⊤] for the continuation (Fig. 5, p. 11).
Type variables carry a priority, ∀α^ρ.T, and T-TApp instantiates α at T when
ρ ∈ |T| (p. 12). receiveTree uses both, ∀p ∈ (⊥,⊤). ∀a :: p (p. 21).

The examples instantiate a function's priority with next c, the head of the
sequence of the channel the call acts on next (p. 4, p. 21, p. 38).

### 3  Skip and ;

Skip and ; carry no priority (p. 7). Fig. 4 has no case for Skip, so |Skip| = ⊤.
unr strips Skip, and unr((∀^S ι.S₁);S₂) = ∀^S ι.(S₁;S₂) when ι does not occur in
S₂ (p. 9). So inst on a channel of type TreeChannel;a instantiates the binder of
the tree and leaves a untouched. F-Seq orders nothing (p. 22). The order between
S₁ and S₂ comes from T-Let and T-LetPair, which check the effect of e₁ against
the context of e₂ (p. 13). T-Eq compares types only with equal priorities
(p. 27), so equivalence is bisimilarity on priority-annotated types.

A call that consumes a segment of unbounded length has latent effect ⊤.
receiveTree is typed →[top, top] (p. 21). T-Let then forbids every channel in
the context of the continuation, and only the channel that the call returns
continues (T-LetPair does not check the bound variables, p. 25).

### 4  fix

fix is a constant (Fig. 3, p. 8) of type
∀ι.∀α^ι.((α → α) → (α → α)) → (α → α), every arrow unrestricted with latent
effect ⊥ (Fig. 5, p. 11). Fig. 15, which the paper calls complete, has no
reduction rule for fix, and fix{σ} is no value (p. 8, p. 30). The type admits
only pure endofunctions. client has the effectful type
Stream →^{⊤,⊥}_un dual Stream →^{p,⊤}_lin Unit (p. 4), so none of the recursive
examples is a use of fix as printed. The examples are FreeST source with
top-level recursive definitions. Their derivations check a function body at the
call site (p. 28, p. 39).

### 5  The semantics is synchronous

R-Com pairs a send with a receive in one step, and R-Ch and R-Close do the same
for choice and close (p. 30). There are no buffers. A.5 says that the scheduler
is "based on" the asynchronous version of van den Heuvel and Pérez (p. 37), and
the paper runs it in its own synchronous semantics.

Our documents say otherwise. context-free.md (stage D, simplifications),
SHARP-EDGES 74 and the header of theories/examples/cfst/CfstScheduler.v call
the paper's semantics asynchronous. They need a correction (decision D5).

### 6  Soundness

Theorem 3 assumes ε ⊢^•_ε C, a closed configuration typed with an empty priority
map (p. 16). Definition 1 counts every irreducible configuration other than
•⟨v⟩ with v of priority ⊤ as a deadlock (p. 16). The proof follows Kokke and
Dardha (p. 15, p. 36).

Five programs type and get stuck. mordido-perez-counterexamples.txt gives each
with its derivation and run.

1. A partial send drops its payload. send{…}v is a value whose type
   !^ι₂ T;S →^{⊤,ι₂}_lin S has lower bound ⊤ (Fig. 5 and text, p. 11). Context
   split treats every type of priority ⊤ as unrestricted (Fig. 12, p. 24), so
   the closure, and the channel inside it, can be discarded. The partner waits
   forever. Lemma 6, |Γ| = |T| for values (p. 32), fails at this value.
2. The same closure hides its payload from the order. A thread holds x at 1
   inside f and receives at 5, and T-LetPair compares 5 with |f| = ⊤. The partner
   of x acts at 1 before releasing the 5. This is the PGV defect of a held value
   that the order cannot see (pgv-adequacy.md 3.2), here inside a constant.
3. A polymorphic payload sits below its carrier. T-TApp asks ι₁ ∈ |T|, and |T|
   of a polymorphic payload holds every element of the sequence. A channel whose
   next action is at 1 travels over a carrier at 3 by picking ι₁ = 11. This is
   PGV's missing payload condition (pgv-adequacy.md 3.1) through priority sets.
4. fix never reduces (section 4). The failure needs no channel, like the
   stuck fix fix of Padovani and Novara.
5. An instantiated channel never synchronizes. E-PInst turns inst x into x{ρ},
   and R-Com, R-Ch and R-Close match only endpoint names (p. 30). Every action on
   a polymorphic channel gets stuck.

Programs 2, 3 and 5 read fork with a linear thunk. As printed, fork takes an
unrestricted thunk (Fig. 5), and T-AbsUn then forbids a thunk that captures a
channel. The examples and the derivation on p. 39 use linear thunks.

The repairs are local. R1 gives the arrow after a payload the payload's
priority. R2 makes fork's thunk linear. R3 reads the payload check per channel
or keeps polymorphic session types out of payloads. R4 gives recursion a binder
or the form fix (λf.λx.e) with a β rule. R5 erases inst at run time.

The checks that failed in PGV hold here, except through the defects above.

- Payload against action. Monomorphic payloads pass T-TApp only at their one
  priority, so send and receive ask the payload above the action.
- Rising sessions. send and receive ask the continuation above the action
  through ι₃ ∈ (ι₂, ⊤] and β :: ι₃. A monomorphic session therefore rises. A
  polymorphic continuation can fall, through the same membership as program 3,
  for example !⁵Unit;P with P's sequence starting at 1. As in PGV, a falling
  session breaks no step of the progress argument, and it breaks the rank world
  of section 8.
- Pairs. T-Pair asks the effect of the right component below the left
  component's priority (p. 25).
- Choice. T-Sel's latent effect is the join of the continuation priorities
  (p. 26), stricter than the choice's own priority.

The proof of Theorem 3 picks "the ready expression with the lowest priority
bound" (p. 36), which is the step that pgv-adequacy.md section 4 found wrong in
Kokke and Dardha. The bound of E[e] covers the whole context, and the argument
needs the priority of the current action. The repaired argument of
pgv-adequacy.md section 4 applies here unchanged.

### 7  Gaps without a counterexample

- Ψ is keyed by variable names (p. 9), T-AbsLin passes it into a function body
  (p. 25), and inst reads it there. A function body that instantiates its
  parameter is therefore typed against the caller's sequences under the
  parameter's name. The paper α-renames formal parameters to the concrete
  endpoints (p. 28) and checks worker "under the updated priority sequences" at
  each call (p. 39). A function used at two channels, as worker at b₁, b₂, b₃,
  has no single derivation. The examples type by inlining.
- A recursive body is typed once, with the sequences of its first call. The
  recursive call client{next c1} c1 c2 checks only the call site (p. 28). No
  rule asks that the body's checks hold at later rounds. With equal increments
  they hold by shifting. We found no deadlocking program that exploits unequal
  increments, because a tail-recursive loop over the same channels repeats the
  behaviour of its first round.
- C-Par splits Ψ with ∘, which appends sequences over a common domain (p. 9,
  p. 14). The example on p. 28 splits domains instead.
- Theorem 1 keeps Ψ fixed (p. 15), while T-Let pops it. After E-LetElim the
  continuation is typed under the unpopped map. The case T-Inst of Lemma 7 asks
  the popped prefix to be empty on the free variables (p. 32), which fails after
  a send on the substituted channel.

None of these produces a deadlock, because priorities have no runtime effect.
They decide how our model of the system is stated (decision D3).

## Stage 2 plan, model and translate

### 8  Fragment v1 and the world

Fragment v1 is the paper's system with R1 to R5 and these restrictions.

- Base type Unit, products, arrows, session types, priority abstraction and
  abstraction over session type variables. No functional µα.T and no functional
  type variables. No example uses them. R4 removes the α of fix.
- new only in the main thread, outside every function. All four examples obey
  it.
- ∀^S only at the top of a recursive type µβ.∀^S ι.S₀ or of a one-shot type
  ∀^S ι.S₀, and no polymorphic session type in a payload (R3). Sessions then
  rise.
- Instant-determinate channel types. Along every path through the type the
  b-th action of a channel has one priority, given its sequence. Unary choices
  and binary choices whose branches have equal priority profiles pass. The tree
  channel fails (section 9.5).
- Shift-uniform recursion. Each recursive call advances the priorities of all
  its channel parameters by one common amount. Stream (2 and 2) and the
  scheduler (6 everywhere) pass.

Points. Each new in main gets one root constant a. The instant (a, b) is the
channel after b actions, as everywhere in the core. Its rank is the priority of
the b-th action, read off the type and the sequence n₁ + k·n₂ fixed at new. For
Stream that is n₁ + b·n₂. For Worker = ∀a. ⊕^a{Start: ?^{a+2}(); Worker} it is
n₁ + r·n₂ at b = 2r and n₁ + r·n₂ + 2 at b = 2r + 1 (p. 37). A monomorphic channel
has the ranks written in its type. A monomorphic payload sits at the carried root
(a, b).1, and the carrier type fixes the payload's priorities, which equal those
of the channel the sender aliases there. The bounds of arrows get slots lo(ρ)
and hi(ρ) of one level anchor, ranked below and above every action at ρ, and the
latent effect ⊤ becomes a ceiling ζ above everything, as in theories/pn.

World. W_P orders two points of the same denotation by ≡ and two points of
rising rank by ≺, as Wpn and Wpgv do. Ties between instants of different
channels break by the root. Strictness follows from wgen_strict_den. Sequences
thus become world facts for the channels of main. Inside a box the same facts
become an infinite constraint over the box's points,
C = {ιᵢ + k ≺ ιⱼ + k′ ∣ rank(ιᵢ + k) < rank(ιⱼ + k′)} ∪ {… ≺ ζ}, which holds at
every call instance by shift uniformity. Stream.v already has this constraint
for the stream, and CfstScheduler.v a constraint of the same kind.

Types. Priorities leave the session types, and the world carries them.

```
[!^ρ T]  = ![T]            [?^ρ T] = ?[T]        [Close^ρ] = [Wait^ρ] = Close
[S;S′]   = [S];[S′]        [Skip]  = Skip        [µβ.S] = µX.[S]       [∀^S ι.S] = [S]
[⊕^ρ{ℓ: S}] = !∗;[S]                        (unary, as in stage D)
            = ⊕([S₁], [S₂])                  (binary)
            = balanced nesting, depth ⌈log₂ n⌉, leaves padded by repetition   (n-ary, n ≥ 3)
[&^ρ{…}]    dual
[S@x]    = [S]@x               x the instant of the channel
[T →^{ρ,σ} U]       = [T] ⊸^{hi(σ)}_{lo(ρ)} [U]
[∀ιs. ∀αs. T]       = □(∀κs ζ αs. C. ∗ ⊸^⊥_⊤ [T])       κs the instants of the channel parameters
```

A priority application f{next c} becomes a force at the instant of c, and a
literal f{n} a force at the slot of n. A type application f[S] forces at [S] (K6).
The balanced nesting gives every label the same number of actions, so the
instants after an n-ary choice agree across labels. Nesting as a list, which K1
suggests, gives label ℓᵢ the depth i and breaks instant determinacy.

Terms. send{…}[T]{…}{…}[S] v c becomes send ⟨v, c⟩, and an unapplied
send{…}v becomes λc. send ⟨v, c⟩ with lower point lo(ι₁) (R1). receive c stays,
close and wait both become close, select and match become select and branch with
case, or send and receive of ∗ for a unary choice. fork becomes spawn, whose
upper point ⊥ is the same masking. inst x becomes x, with E-Conv for the unfolding.
Recursion (R4) becomes the recursive box !(f = λx.e′), and a recursive call
becomes a force of f at the next instants. A λ in an unrestricted context becomes a
box, as in theories/pn.

Rules.

| Mordido–Pérez | ours | side condition |
|---|---|---|
| T-Var, T-Const | E-LVar, E-Ch, E-Const after η | unrestricted rest becomes □Δ or spent |
| T-AbsLin | E-Abs with ℓ = lo(\|Γ\|), u = hi(ρ) | ℓ ≼ every head of Γ |
| T-AbsUn, T-PAbs, T-TAbs | E-Exp | C holds at every instance used (shift uniformity) |
| T-App | E-App | ρ₁ < \|Γ₂\| puts hi(ρ₁) below heads(Γ₂), ρ₂ < ρ puts hi(ρ₂) below ℓ |
| T-PApp, T-TApp | E-Force at the instants, or at [S] | C[κs′] from the rank world |
| T-Inst | E-Conv | unfolding of µ and erasure of ∀^S |
| T-Pair, T-Let, T-LetPair | E-Pair, E-App of a λ or E-Let*, E-LetPair | as T-App |
| T-Sel, T-Match | E-Const select or send, branch and E-Case, or recv | rising profile of the choice |
| T-New, T-NewPoly | E-Const new at the root of this new | the root is known |
| T-Eq | E-Conv | erasing equal priorities keeps bisimilarity (p. 27) |
| C-Main | P-Term at F = ∅ | closed program |

The lemma reads Δ | Γ | Θ | Ψ ⊢ e : T ⋄ π̄ ⋄ ρ as [Γ] ⊢^F [e] : [T] for every frame
F with {hi(ρ)} ≺ F, the reading of pn_translate.

### 9  Obstacles

#### 9.1  Asynchrony

None. The semantics is synchronous (section 5). A simulation back to the source
semantics of Fig. 15 with R4 and R5 follows the pattern of PNSimulation.v. The
administrative target steps are the β steps of the η-expanded send, the forces of
boxes, and the extra selects of a balanced n-ary choice. The source has its own
administrative steps, E-TApp, E-PApp and E-PInst, which the target skips, so the
simulation stutters on both sides as in theories/pn. The extra selects never block,
because both ends of the channel perform them in lockstep, and one simulation
step performs all of them, as fwd performs the closes for Padovani and Novara.
No buffers are needed.

#### 9.2  Recursive data types

No obstacle. The paper's calculus has no sums, no data types and no Int either
(Fig. 1). receiveTree builds Tree values only in FreeST. The stage D
simplification of trees, which travel on a channel, matches the paper's own
calculus. Functional µα.T stays outside v1.

#### 9.3  Segment lengths that depend on data (K8)

No typing of the paper needs a fact that depends on the length of a segment.
Their effects have no form for "after the segment". A call that consumes a
segment of unbounded length has latent effect ⊤, because a finite effect σ of a
recursive call that instantiates p := next c would need σ ≥ σ[next c/p] > σ.
receiveTree is typed with effect top (p. 21). After an effect ⊤, T-Let and
T-LetPair forbid every channel in the continuation's context except the ones the
call returns (section 3). The ceiling ζ of K8 above the whole segment is exactly
this. sendTree t c; close d; send v c fails in their system as in ours, and ours
is more permissive. We may hold d across the call when d acts after all of c.

#### 9.4  fix with a general body

fix has no semantics as printed (program 4). Repair R4 adopts recursion only in
the form fix (λf.λx.e), at any arrow with an unrestricted context. The
translation is the recursive box of theories/pn. The simulation needs the same
restriction as fixlam. The source evaluates the body once at the unfolding,
while the box runs it at every force, and the two agree when the body is a λ
(padovani-novara.md 8.5). With R4 in the λ form the restriction holds by
construction.

#### 9.5  Branches that order a channel differently (new)

Our choice puts both continuations at the instant ι + 1 (K4, K5). Their branches
may give the same instant different priorities, and a matching thread may order
the channel against another one differently in each branch. The following
program types in their system and is deadlock free. No strict world types its
translation.

```
c : ⊕¹{A: !⁵Unit; Close⁶, B: !²Unit; Close⁶}      d : Close³
T1 = select A c; send () c; close c
T2 = match c′ with { A → λc′. wait d′; receive c′; wait c′
                   , B → λc′. receive c′; wait d′; wait c′ }
T3 = close d
main = new c, new d, fork T1, fork T3, T2
```

T2 types by T-Match. The branch functions have lower bound |d′| = 3 and effect 6.
In A, wait d′ at 3 lies below c′ at 5, and in B receive c′ at 2 lies below d′ at 3.
T1 has nothing else in its context when it selects. Every run selects A, and
every synchronization finds its partner. In our system T2's branch A blocks on d
while it holds c at (c, 1), which needs (d, 0) ≺ (c, 1). Branch B blocks on c at
(c, 1) while it holds d, which needs (c, 1) ≺ (d, 0). E-Case types both branches
in one world, so the world has a cycle. The argument is by hand and inverts the
derivation.

It is the first program we found that a priority system types and the order
system rejects. It does not touch subsumption of PGV, which has no session
choice. The tree channel has the same shape. A leaf continues at the next
subtree's priority and a node at ι + 1 (p. 21). Our TreeCopy.v types the tree with
a world of its own, so the example still types, and only the translation by ranks
fails.

Three resolutions.

- (a) Fragment v1 asks instant-determinate types (section 8). No cost. It
  excludes T2 and the tree channel from the translation.
- (b) Choice by delegation in the translation. A selection sends a fresh channel
  in a sum, ⊕(S₁, S₂) becomes !(∃ι₁ ι₂. S₁@ι₁ + S₂@ι₂);Close, and each branch
  continues on its own carried root. The core stays unchanged. T2 then types with
  ranks 1 for (c, 0), 5 for (c, 0).1, 2 for (c, 0).2 and 3 for d. Cost is a
  translation of context-free types into a continuation-passing form, with a
  continuation variable under µ inside a payload, and a simulation that relates one
  source channel to a chain of target channels. Roughly the size of PNSimulation.v
  on top of the v1 work.
- (c) Branch roots in the core. selectᵢ moves the channel to a new root ι◁i
  instead of ι + 1. Cost is a change of K4 and K5, the O-Select and O-Branch
  clauses with every lemma of stage B that moves a channel by a choice, and new
  constraints for TreeCopy.v and the scheduler. Comparable to stage B for the
  choice cases.

Recommendation. (a) for v1. (b) if the paper is to claim that the order system
subsumes this one, because it leaves the core alone.

#### 9.6  Priority sets and the map Ψ

The translation reads each channel's priority from its own sequence, which is
what R3 does on their side. Gap 1 of section 7 decides how the source judgment
is stated (D3). A literal model keeps Ψ, names and checking by inlining, and the
translation then rebuilds one box per function from many call-site derivations.
A modular model lets a function's priority parameters name the heads of its
channel parameters, so inst x reads the parameter that the caller instantiates
with next c. Each function then has one derivation, and T-AbsLin needs no Ψ.
All examples already pass next c at every call.

#### 9.7  Shift uniformity

The box constraint holds at every round only when all channels of a recursive
function advance by one amount (section 8). The paper checks the body once,
so it also accepts unequal increments. Such programs repeat their first round and
our system types them with a world that counts instants, as Stream.v does. Only
the rank world fails. v1 keeps the restriction. A later version could build the
world from instants in place of priorities wherever a recursive body is uniform
in instants.

### 10  Theorems for v1

In the style of pn_deadlock_free and pn_deadlock_free_source, in theories/mp/ on
the cfst branch.

```
Theorem mp_translate Γ e T ρ e' :
  mp_typed Γ e T ρ e' →
  ∀ Ψ B ins Δ Φ F, good Ψ B → erel B ins Γ Δ → ub_below Wmp Ψ Φ (hi B ρ) F →
  typed Wmp Φ Ψ ∅ Δ F (rename (ren_of ins) e') (tr B T).

Theorem mp_deadlock_free e ρ e' :
  mp_typed [] e MUnit ρ e' → deadlock_free (∅, {[+ e' +]}).

Theorem mp_deadlock_free_source e ρ e' :
  mp_typed [] e MUnit ρ e' → mp_deadlock_free_src e.

Theorem stream_mp_deadlock_free   : ∃ ρ e', mp_typed [] stream_main MUnit ρ e' ∧ deadlock_free (∅, {[+ e' +]}).
Theorem sched_mp_deadlock_free    : ∃ ρ e', mp_typed [] sched_main MUnit ρ e' ∧ deadlock_free (∅, {[+ e' +]}).
Theorem dlfix_mp_deadlock_free    : ∃ ρ e', mp_typed [] dlfix_main MUnit ρ e' ∧ deadlock_free (∅, {[+ e' +]}).
Lemma   mp_cx1_rejected, mp_cx2_rejected, mp_cx3_rejected : no mp_typed derivation under R1 and R3.
```

mp_typed is v1 of section 8 with the last index the translated term, as
pn_typed. Wmp is the rank world of one closed program, so unlike Wpn it depends
on the sequences of main. The world then becomes an argument computed from the
derivation, or mp_typed carries the table of roots, increments and offsets. R4
in the λ form makes fixlam hold by construction, so mp_deadlock_free_source
needs no extra premise.

Cost. theories/pn has 4067 lines, 2432 for model, world, translation and
examples and 1635 for semantics and simulation. v1 needs the same parts plus
priority sets, sequences and next, and loses the recursive channel types of
Padovani and Novara. A similar size is the estimate. Resolution (b) of 9.5 comes
on top.

In reach now. v1 with resolution (a). It covers the two streams, the scheduler
with k = 3, the classic deadlock and its repair. The tree channel and T2 of 9.5
stay outside the translation. The tree already types directly in TreeCopy.v.

### 11  Decisions for the author

- D1. Target the repaired system, fork with a linear thunk and R1 to R5, as for
  PGV and Padovani and Novara.
- D2. Branches that order a channel differently (9.5). (a), (b) or (c). The
  recommendation is (a) now and (b) for a subsumption claim.
- D3. Model Ψ literally or modularly (9.6). The recommendation is modular.
- D4. The restrictions of v1 (section 8), in particular instant determinacy and
  shift uniformity.
- D5. Correct context-free.md, SHARP-EDGES 74 and the header of
  CfstScheduler.v, which call the paper's semantics asynchronous.
- D6. Whether stage 2 and the simulation go into Rocq on the cfst branch, and
  whether the general theorem or only the examples.

## Stage 2, mechanization

### 12  Version 2 in Rocq

The author decided D1 (the repaired system), D2 = (c) (branch roots in the
core), D3 (Ψ modular), D4 (restrictions only where needed) and D6 (a general
theorem). Fragment v1 (MPTypes.v to MPExamples.v) stays in the tree and is
superseded by version 2.

| File | Content |
|---|---|
| MP2Types.v | priorities, context-free session types with type variables, head normal form, positions, functional types, erasure |
| MP2World.v | ranks with the ceiling, denotations, walks, observational equivalence, `Wmp`, anchors, `good`, the box constraints |
| MP2Typing.v | the judgment `mtyped Θ Γ e T σs e′` |
| MP2Translate.v | `mp2_translate`, `mp2_deadlock_free` |
| MP2Examples.v | receiveTree with a sender, the two streams, T2, the repaired classic deadlock, a partial send |

The source system. Source terms are our terms, as in v1. Session types are
those of Fig. 1 with binary choice: Skip, S;S, !^ρ P, ?^ρ P, ⊕^ρ(S, S),
&^ρ(S, S), Close^ρ, Wait^ρ, µβ.∀^S ι.S, β and session type variables. µβ.S is
µβ.∀^S ι.S with ι unused, and ∀^S ι.S is µβ.∀^S ι.S with β unused. A channel
type is S at a position. A position is either the sequence h + k·d of the
channel (D3) or an abstract position, the walk w from an end point n. T-Eq
(`m_eq`) asks the erasures to be bisimilar at every instance of the type
variables and the two channel points to be observationally equivalent at every
valuation. It covers inst, the monoid laws and distribution. An action needs
its channel type in head shape, and at a sequence it has the side conditions of
Fig. 5 with R1 and R3. Θ is a predicate on valuations of the priority and
session type variables. A priority abstraction ∀ιs αs ∈ Θ. T →^{⊤,σs}_un U is
forced at an instance that meets Θ (T-PApp and T-TApp in one step). A function
over a segment has type ∀αs. Sa →^{⊤,⊤} ∃. Sr (`MSeg`). Its body is typed at
any valuation with its channel at an abstract position (`m_fixseg`). A call
returns ∃. Sr (`m_appseg`), opening it gives a channel at a fresh end point
(`m_open`), and a channel at any position packs into ∃ (`m_pack`). At an
abstract position an action has effect ⊤, the latent effect of receiveTree
(p. 21), and sends only unit.

The world. As in v1, one anchor per box stands for a valuation and a channel
point at a sequence is the slot of the anchor named by its type. A point
denotes a channel by its raw session type and sequence head, and the head
normal form gives its successor, branch roots and payload slot. Two points are
equivalent when every walk from them reaches equal ranks, so T-Eq preserves
points without a canonical form. The rank of a channel is the priority of its
head. An upper point with ⊤ is the ceiling, above every walk of every channel,
junk included, and the lower point of ⊥ is the floor below them. A function
over a segment is a box over a channel point κ and the caller's anchor B with
the constraint {κ·w ≺ ceil(B), floor(B) ≺ κ·w ∣ w} plus every fact about B true
at every valuation. It returns ∃κ′. {κ′·w ≺ ceil(B), floor(B) ≺ κ′·w ∣ w}. This
is the coarse ceiling of K8 with walks that include payload slots, read in the
rank world. The body needs no anchor of its own, so a recursive call on the end
point of an earlier call needs no priority that the caller cannot name.

Theorems, both closed under the global context.

```
Theorem mp2_translate Θ Γ e T ef e' :
  mtyped Θ Γ e T ef e' →
  ∀ ss Ψ B pts ins Δ Φ F, length ss = pc_nt Θ → Forall hcontractive ss →
  good Ψ Θ B → pts_ok Ψ B pts → erel B ss pts ins Γ Δ → ub_below_s Wmp Ψ Φ (hiz B ef) F →
  typed Wmp Φ Ψ ∅ Δ F (rename (ren_of ins) e') (trs ss B pts T).

Theorem mp2_deadlock_free e ef e' :
  mtyped pc0 [] e MUnit ef e' → deadlock_free (∅, {[+ e' +]}).
```

ss is an instance of the session type variables, pts maps end points to points
between the floor and the ceiling of B, and `trs ss B pts T` is the translated
type under ss.

Examples through the translation, each with `∃ ef e', mtyped pc0 [] main MUnit
ef e' ∧ deadlock_free (∅, {[+ e' +]})`.

| Program | Source | Theorem |
|---|---|---|
| receiveTree on the tree channel, against a sender of Node(Leaf, Leaf) | pp. 5, 21 | `rt_mp2_deadlock_free` |
| two streams in a cycle | Listings 1.1, 1.2, p. 4 | `st_mp2_deadlock_free` |
| the repair of the classic deadlock, p = 1, q = 2, f and g inlined | p. 3 | `df_mp2_deadlock_free` |
| T2, branches that order a channel differently | section 9.5 | `t2_mp2_deadlock_free` |

`psend_typed` types a partial send as the closure λc. send x c. Its lower bound
is the payload's priority, which is R1.

Findings.

- Milner's scheduler (A.5) is not typed by the repaired system. In
  follower{next d₁} d₁ a₂ c₂ of the main for k = 3 (p. 38) prev has the
  sequence 2 + 6k and succ the sequence 4 + 6k. Line 14 selects Next on succ at
  b + 4 = 8 while the thread holds prev, whose next action is at 2 + 6 = 8. T-Let
  asks 8 < 8, and with the latent effect ⊔|Sℓ| of T-Sel (Fig. 14, p. 26) it asks
  10 < 8. CfstScheduler.v types the scheduler directly with ranks that read the
  parity of the instant.
- A seventh program types and deadlocks. Close^⊤ and Wait^⊤ are allowed
  (Fig. 5, close at ι ∈ (⊥, ⊤]), and a channel of priority ⊤ is unrestricted
  (S-Top, Fig. 12, and T-Const, which asks |Γ| = ⊤). Program 7 of
  mordido-perez-counterexamples.txt drops the closing end and its partner
  waits forever. Repair R7 keeps channels linear and action priorities finite.
- The bound ∀α :: ρ of a session type variable constrains nothing. Fig. 4 and
  its text (p. 10) read |α| as the interval of ρ when ρ has free priority
  variables. receiveTree types only because T-Match does not check that a
  continuation rises. Version 2 needs no bound, because receiveTree is a
  function over a segment, where only the ceiling and the floor matter.
- Rising continuations are forced by the rank world. A continuation after an
  unbounded segment has a priority either below the last action of the
  segment, which no strict order permits along program order, or at a position
  that depends on the length of the segment.

Not done. The rejection of the seven counterexamples by `mtyped` is not
mechanized. A rejection needs an inversion of derivations through `m_eq` and
`m_sub`, which is not cheap. Section 14 carries deadlock freedom back to their
semantics.

### 13  Restriction log

Each entry gives the reason and what is lost. "Lost" means a program that the
repaired system of Mordido and Pérez types and version 2 does not translate.

Repairs.

- R1, the arrow after a payload has the payload's priority. Reason: program 1
  drops a channel and program 2 hides one from the order. A partial send is the
  closure λc. send x c, and T-AbsLin gives it the lower bound |x|
  (`psend_typed`). Lost: nothing beyond the repair.
- R2, fork takes a linear thunk. Reason: as printed no example types. Lost:
  nothing.
- R3, the payload check reads the head of the payload's sequence. Reason:
  program 3. Lost: programs that type only through the set |T| of Fig. 4, whose
  payload acts at or below the carrier. Polymorphic payloads stay allowed.
- R4, recursion is rec f. Λιs αs. λx.e. Reason: fix never reduces (program 4).
  Lost: uses of fix as printed, which all get stuck.
- R5, inst has no run-time trace. Reason: program 5. inst is T-Eq. Lost:
  nothing.
- R6, T-Match asks ρ < |Γ₂|. Reason: program 6. Lost: programs that block on a
  branching while they hold a channel below it.
- R7, a channel is linear at every priority, and action priorities at a
  sequence are finite. Reason: program 7, a channel at Close^⊤ is unrestricted
  and can be dropped. Lost: programs that close or wait at ⊤ at a sequence.
- R8, the body of a recursive function types at every round, under the
  sequences that the round reaches. A round is one run of the body from one
  call to the next. Reason: program 8 (section 15.2). Their rules type the body
  once, under the sequences of the first call (pp. 28, 29), and accept two loops
  that deadlock in the second round. Lost: programs whose loops type only at
  their first round. Each one we know types again after other sequence
  annotations at new, for example `rr_main` (section 15.2).

Deviations of version 2.

- Ψ in the types (D3). A function names the heads of the sequences of its
  channel parameters as priority variables, so its body holds at every round.
  This is repair R8. Unequal increments are kept when every round advances all
  channels by one amount of priority (`rr_mp2_deadlock_free`). Version 3 keeps
  it. Section 15.2 shows that nothing weaker is sound.
- Functions over unbounded segments. A segment is the part of a session that
  one call of a recursive function consumes, and its length depends on the
  data, as the whole tree does in receiveTree. A function of latent effect ⊤
  that recurses over a segment is written as `MSeg`, over one channel and
  without priority parameters. Its channel sits at an abstract position, a walk
  from an end point whose head of sequence nobody knows. An action there has
  effect ⊤, because the head after earlier calls has no bound. SHARP-EDGES 79
  records an attempt to give these instants their real ranks, which lifted
  nothing.
  - Lost: such functions with a second linear parameter (U2). The core types
    one, `copy` in theories/examples/cfst/TreeCopy.v, with the lockstep facts
    D = {κ·w ≺ ι·w, ι·w ≺ (κ·w)·s, κ·w ≺ ζ, ι·w ≺ ζ ∣ w, s} and an existential
    over two end points with a ⊗ result. So the loss is one of the
    translation, not of the core. It stays in version 3, for two reasons. The
    rank world cannot meet D at a call. Two channels of one tree type with
    heads h₁ < h₂ and one increment have ranks q + h₁ and q + h₂ at the walk w,
    and (κ·w)·s acts at q + 1 + h₁ when the next action of the tree is at ι + 1
    (p. 5). So ι·w ≺ (κ·w)·s asks h₂ − h₁ < 1. D has to be a fact of a world
    built from facts, and the strictness of such a world is a global property
    (section 15.4). Second, segment functions in versions 2 and 3 return one
    channel, and a ⊗ result needs a new form of `MEx` and a new opening rule.
    Their rules type a copy over two tree channels with a pair result,
    because they check the body under the sequences that Ψ fixes for the names
    of the parameters (T-Inst and T-AbsLin, p. 25), as they do for
    receiveTree.
  - Lost: bodies that send a channel, and sends of a channel on the channel a
    call returns. Reason: the core sends a channel only if its point is the slot
    of the carrier and lies above the carrier. At an abstract position the
    carrier is a walk of an existential point, and no fact equates its slot
    with a point of the anchor at every head. The order between a walk and its
    own slot is a fact about one walk. It fails where the rank world puts junk,
    and a recursive call on an end point cannot pass it on, because the caller
    knows only the floor and the ceiling of that end point's walks. Receiving a
    channel there works and leaves it at the walk of the slot.
- After a segment call the returned channel acts with effect ⊤ and has priority
  ⊥ in the context. Reason: the head of its sequence after the call depends on
  the data and has no bound. `rt_rank_data` takes the channel of rt_main, of
  type TreeChannel; Wait⁹ with sequence 1 + 2k. After Node(Leaf, Leaf) it
  reaches Wait⁹ at rank 9. After a tree with four nodes on its left spine the
  last leaf sits at 17 and Wait⁹ is junk, above every finite level. So no fact
  fixed when the function is defined puts the returned channel below an anchor
  point of finite priority.
  - Lost in version 2: programs that act on the returned channel while they
    hold a channel of finite priority, and programs that act on another
    channel while they hold the returned one.
  - Version 3 lifts both for channels created after the call, one direction
    per channel (section 15.3). A channel created below the floor may act
    while the caller holds the returned channel. A channel created above the
    ceiling may be held while the caller acts on the returned channel.
  - Lost in version 3: a channel created after the call that the program
    orders against the returned channel in both directions, and channels
    received or created before the call. Reason: the walks of the returned
    channel have ranks that depend on the data (`rt_rank_data`), so only the
    floor and the ceiling bound them uniformly. A two way interleaving needs
    a world built from facts (section 15.4).
- Session type variables. A priority abstraction binds session type variables,
  which the anchor interprets and the box of the core binds (K6). A bound
  ∀α :: ρ becomes part of the predicate Θ. Type variables do not occur in the
  body of a µ. Reason: an instance with its own ∀^S would nest ∀^S, which
  F-PAbsS forbids (p. 22). Lost: µβ.∀^S ι.S whose body mentions a type variable.
- No functional type variables, no µα.T, products only as the results of new and
  receive, payloads unit or channels. Lost: nothing in the paper.
- A channel at Skip is linear. Fig. 4 gives Skip priority ⊤, so their context
  split may drop it. Reason: the core has no rule that discards a session at
  Skip, and the core does not change. Lost: programs that discard a channel at
  Skip. Every example ends its channels with Close or Wait.
- Choice is binary. A unary choice is a binary one with equal branches, and its
  match a case with equal branches, with no rule of its own. A choice of n ≥ 3
  labels nests binary choices, and each inner choice needs a priority strictly
  between the outer one and the continuations. Lost in version 2: n-ary choices
  whose continuations lie at ρ + 1. Version 3 lifts this. An inner node carries
  the priority of the outer node at a depth, and its rank lies strictly
  between ρ and ρ + 1 (section 15.1, `ch3_mp3_deadlock_free`).
- Every continuation rises at a match, at a sequence. Reason: the branch root
  x◁i is equivalent to the point of the branch only when the branch rises. Lost:
  programs whose branching partner can never select, and abstractions whose
  continuation type variable falls below the branching, which Fig. 4 admits
  because it reads |α| as an interval.
- A priority abstraction captures only units and abstractions and takes and
  returns no channel at an abstract position and no unopened segment result.
  Reason: the core compares existential types on the nose. Lost: a function that
  returns the result of a segment call unopened. No example does.
- A priority abstraction has a satisfiable Θ. Lost: nothing callable.
- Milner's scheduler is outside the repaired system (section 12), so nothing is
  lost there.
- More permissive than the paper. select has effect ρ instead of ⊔|Sℓ|, an
  effect may grow (`m_sub`), T-Eq accepts every rewrite that keeps the erasure
  and the point, and lower bounds and effects are exact lists. These accept more
  source programs and lose none.

Paper examples. Through the translation go receiveTree with the tree channel
(pp. 5, 21), the two streams (Listings 1.1, 1.2) and the repair of the classic
deadlock (p. 3). The classic deadlock itself deadlocks. Their rules reject it,
and CfstDeadlock.v shows that no strict world types it. Milner's scheduler (A.5)
is not typed by their repaired rules.

Programs their repaired system types that version 2 does not translate:
segment functions with a second linear parameter or that send channels,
programs that order the channel returned by a segment call against other
finite channels, µ bodies with type variables, programs that discard a channel
at Skip, n-ary choices without room between priorities, branchings whose
continuation does not rise, and functions that return an unopened segment
result. Recursive functions that type only at their first round are not in
this list, because repair R8 rejects them for soundness (section 15.2).

Version 3 translates n-ary choices without room and channels created after a
segment call that are ordered against the returned channel in one direction.
The other items stay, with the reasons above.

The section "Gaps checked against the core (2026-11-04)" below sorts the
remaining items into translation artefacts, core limits and programs their
rules reject.

## Stage 3, the source semantics

### 14  Deadlock freedom in their semantics

Every closed program that the repaired source system types at unit is deadlock
free in their own semantics, Fig. 15 (p. 30), in the sense of Definition 1
(p. 16).

```
Theorem mp2_deadlock_free_source e ef e' :
  mtyped pc0 [] e MUnit ef e' → mp_deadlock_free_src e.

Definition mp_deadlock_free_src (e : expr) : Prop :=
  ∀ q, rtc src_pstep (∅, {[+ e +]}) q → src_irred q → src_final q.
```

`src_final q` says that no restriction is left, every child thread is () and
the main thread is a value. The four programs of section 12 follow
(`rt_deadlock_free_src`, `st_deadlock_free_src`, `df_deadlock_free_src`,
`t2_deadlock_free_src`). The theorem needs no premise beyond the typing. A
recursive function is rec f. λx.e by repair R4, so the typing yields no other
form of recursion, and the simulation needs no restriction like the one on fix
for Padovani and Novara.

| File | Content |
|---|---|
| MP2Semantics.v | source reduction `src_step` and `src_pstep`, Definition 1 as `mp_deadlock_free_src` |
| MP2Simulation.v | the relation `trm`, the forward simulation `fwd`, `classify`, `final`, the theorem |

The model of Fig. 15. The source terms are the terms of `mtyped`, so both sides
run on the syntax of lang/Syntax.v. The deviations follow.

- Configurations are flat, a set of restricted names and a multiset of threads.
  The rules of ≡ bring every closed configuration into this form.
- Both ends of a channel carry one name. let (x, y) = new S in e is one term for
  R-New and R-NewPoly, because the sequence of R-NewPoly lives in the types. The
  fresh name is fresh for the whole configuration.
- Type and priority applications are erased, and so is inst (R5). The β rule of
  R4 is (rec f. λx.e) v → e[v/x][rec f. λx.e/f].
- match y with {ℓ → eℓ} is a case on branch y, and R-Ch puts the channel into the
  chosen branch in one step.
- R-Close drops the restriction of the closed name. Fig. 15 keeps it, and ≡
  removes it only once no thread mentions the name. A name closes once here, so a
  program that closes a name twice is stuck here and not in Fig. 15. Linearity
  (R7) rules such programs out, but the simulation does not track types and
  does not use this.
- R-Com and R-Ch fire on any name. In Fig. 15 a thread that holds a name always
  runs under its restriction, because ≡ drops a restriction only when no thread
  mentions the name.
- Definition 1 asks the final value of the main thread to have a type of
  priority ⊤. The simulation does not track types, so it shows only that the
  main thread is a value.

The simulation. `trm M s t m` relates a source term to a target term at a mode,
the shape the translation reads: data (unit and channels), a linear function,
or a function that is forced before it is applied. It holds every translation
(`trm_of_typed`) and one administrative form, the translated recursive function
after the force and before its argument is a value. Unit is () in the source and
the box of () in the target. Close is followed by an administrative let, and
fork by the two β steps of `fork_tr`. Communication is synchronous on both sides,
so a message, a choice and a close each match one target step, and no extra step
follows a message.

- `fwd`. Every source step is matched by the corresponding target step with β
  steps before and after.
- `tri` and `classify`. A source thread is a value, steps, or is stuck. A stuck
  source thread, for example () where a channel is expected, has a target that
  reaches a term offering no action at all. The relation does not track the
  payload kind of a channel, so such stuck terms cannot be ruled out, and the
  proof does not need to rule them out.
- `final`. If the source is irreducible, administrative steps bring the target to
  a configuration whose threads are values, pending actions matching pending
  source actions, or terms offering nothing. The target is deadlock free by
  `mp2_deadlock_free`, so it is terminated or it reduces. Termination makes the
  source final. A reduction pairs two pending actions, and the source pairs the
  same two.

## Stage 4, the world from the derivation

### 15  Version 3

The author approved Fix 1, a world built from the typing derivation in place of
the rank world. Every comparison of a derivation was to become a fact between
two points, and rounds of a recursion were to get counted instants as in
Stream.v. The obligation was that the facts form a strict order. Version 3 is
the result. Strictness fails across recursive calls (15.2), so D3 is a repair
and not a loss. The other two losses need no world of facts in the cases that
version 3 covers. The rank world gets room for them (15.1, 15.3). Section 15.4
says what a world of facts would add and why its strictness is a global
property.

| File | Content |
|---|---|
| MPRounds.v | program 8 and its deadlock in their semantics, matching rates through version 2 |
| MP3Types.v | priorities at a depth `PD`, the levels `PBB` below ⊥ and `PTT` above ⊤, positions `PL` and `PH` |
| MP3World.v | ranks with a level and a subrank, the low chain `DLC`, the high chain above the ceiling |
| MP3Typing.v | `brise` for inner nodes, rules `m_newlo` and `m_newhi`, `pmid` for packing and segment calls |
| MP3Translate.v | `mp3_translate`, `mp3_deadlock_free` |
| MP3Examples.v | the v2 examples, a choice with three labels, matching rates, rtA and rtB |
| MP3Simulation.v | `mp3_deadlock_free_source` |

Theorems, all closed under the global context.

```
Theorem mp3_translate Θ Γ e T ef e' :
  mtyped Θ Γ e T ef e' →
  ∀ ss Ψ B pts ins Δ Φ F, length ss = pc_nt Θ → Forall hcontractive ss →
  good Ψ Θ B → pts_ok Ψ B pts → erel B ss pts ins Γ Δ → ub_below_s Wmp Ψ Φ (hiz B ef) F →
  typed Wmp Φ Ψ ∅ Δ F (rename (ren_of ins) e') (trs ss B pts T).

Theorem mp3_deadlock_free e ef e' :
  mtyped pc0 [] e MUnit ef e' → deadlock_free (∅, {[+ e' +]}).

Theorem mp3_deadlock_free_source e ef e' :
  mtyped pc0 [] e MUnit ef e' → mp_deadlock_free_src e.

Theorem p8_not_deadlock_free : ¬ mp_deadlock_free_src p8_main.
Theorem p8_not_mtyped : ¬ ∃ ef e', mtyped pc0 [] p8_main MUnit ef e'.     (version 2)
```

Each example has `∃ ef e', mtyped pc0 [] main MUnit ef e' ∧ deadlock_free (∅,
{[+ e' +]})` and a source version.

| Program | Theorems |
|---|---|
| receiveTree, the two streams, the repaired deadlock, T2 | `rt_mp3_deadlock_free` … `t2_mp3_deadlock_free`, `rt_deadlock_free_src3` … |
| unequal increments with matching rates | `rr_mp2_deadlock_free`, `rr_deadlock_free_src`, `rr_mp3_deadlock_free`, `rr_deadlock_free_src3` |
| a choice with three labels, continuations at ρ + 1 | `ch3_mp3_deadlock_free`, `ch3_deadlock_free_src3` |
| receiveTree, then d below the floor | `rtA_mp3_deadlock_free`, `rtA_deadlock_free_src3` |
| receiveTree, then d above the ceiling | `rtB_mp3_deadlock_free`, `rtB_deadlock_free_src3` |

The core and the statements of soundness and the composition lemmas are
unchanged. Version 2 is unchanged and builds.

#### 15.1  n-ary choice

An n-ary choice ⊕^ρ{ℓ₁, …, ℓₙ} nests binary choices. An inner node of the
nesting carries the priority `PD ρ t`, the priority ρ at the depth t ≥ 1. Its
value is the value of ρ, so every comparison of their rules reads it as ρ. Its
rank is the rank of ρ with the depth as subrank. A rank at a finite priority z
now has a level and a subrank. Lower points sit at level 0, channels at level 1
with their depth, upper points at level 2. So an inner node lies above the outer
node, below every upper point of ρ and below every channel at ρ + 1.

A continuation K of a choice at a rises when its head lies above a, as before,
or when its first choice is `PD a t` with t ≥ 1 (`brise`). The translation of
the select and the match is unchanged. Only the proof that the branch root rises
reads the depth (`ch_branch`).

ch3_main selects the third label of ⊕¹{A: Close², B: Close², C: Close²}, written
⊕¹(A, ⊕^{1·1}(B, C)). Their rules type it with every continuation at 2. Version
2 needs a priority strictly between 1 and 2.

#### 15.2  Rounds and program 8

A round is one run of the body of a recursive function, from one call to the
next. Their rules type the body once, under the sequences of the first call
(the derivation for client, pp. 28 and 29). Program 8 shows that this is
unsound.

```
client a b = let a = send () a in let (_, b) = receive b in client a b        (Listing 1.1)
dsend b a  = let (_, a) = receive a in let b = send () b in
             let b = send () b in dsend b a
main = let (a, a′) = new Stream 1 4 in let (b, b′) = new Stream 2 2 in
       fork (client a b′); dsend b a′
```

The first round of client acts at 1 while it holds b at 2, and at 2 while it
holds a at 5. The first round of dsend acts at 1, 2 and 4 while it holds the
other channel at 2, 5 and 5. All checks hold. In the run, client sends on a and
dsend receives. dsend sends on b and client receives. Then client sends on a
again and dsend sends on b again, and both wait forever.
`p8_not_deadlock_free` runs the program in MP2Semantics.v to this state.
`p8_not_mtyped` concludes that version 2 rejects it, because a derivation would
make it deadlock free. In version 2 client's second round asks 5 < 4.

The strictness argument has three parts.

- Inside straight-line code every generated fact compares two priorities, so
  the priorities rank the facts.
- One recursive function on its own is strict. Rank an instant of round r by
  the pair of r and the priority of the matching instant of the first round,
  read lexicographically. A fact inside round r compares two first round
  priorities, which their rules checked. A fact between round r and round r + 1
  holds by the first component.
- Two loops that share a channel each come with their own count of rounds, and
  the two counts disagree when the loops advance the channel at different
  rates. client advances a and b by one action per round, dsend advances a by
  one and b by two. client's round 1 has a₁ ≺ b₁, dsend's round 0 has b₁ ≺ a₁.
  The union is cyclic, and the program deadlocks.

The exact condition is that the union of the round facts of all loops is
acyclic. It is a property of the whole program. No check of one function at
its first round decides it, because client is the same function in program 8 and
in the deadlock free pairing with newclient. A sufficient condition per function
is that every round types under its own sequences. This is repair R8, and the
priority abstraction of version 2 already asks it. It keeps unequal increments
when the rates match. `rr_main` replaces client by hrecv, which sends once on a
and receives twice on b. Each round advances a by 4 and b by 2 · 2, every round
types, and the program goes through versions 2 and 3.

#### 15.3  Channels created after a segment call

During a call of latent effect ⊤ the caller holds nothing finite (T-Let, p. 25,
Fig. 4, p. 11). The returned channel c′ sits at an end point whose walks have
ranks that depend on the data (`rt_rank_data`). The existential of the call
bounds them by the floor and the ceiling of the anchor, and nothing finer holds
at every tree.

Version 3 adds two places for a channel d created after the call.

- The low chain starts at the anchor slot B[RLow]. Its points rank KL j, below
  every lower point of ⊥, so below the floor. A channel there (`m_newlo`, position
  `PL`) acts with effect ⊥⁻ (`PBB`, value XBB) and counts as ⊥⁻ when held. It may
  act while the caller holds c′, whose priority is ⊥, and nothing may act while
  it is held.
- The high chain starts at the successor of the ceiling, the point ε + 1 for the
  upper point ε of the effect ⊤. Its points rank KU j, the junk of the ceiling.
  A channel there (`m_newhi`, position `PH`) acts with effect ⊤⁺ (`PTT`, value
  XTT) and counts as ⊤⁺ when held. The caller may act on c′, with effect ⊤,
  while it holds d. After an action on d the caller holds nothing finite.

The ranks gain KLL and KLH around the low chain and KV, KW and KX above the high
chain. KV is the upper point of ⊤⁺, KW the lower point of a closure that holds
nothing, which version 2 put at KU 0. A head written with ⊥⁻ or ⊤⁺ counts as ⊥
or ⊤ (`xcl`), because channels at a sequence never act there. Effects with ⊤⁺
lie above ⊤, so `hle` asks ⊤⁺ to stay out of an effect that it bounds by ⊤, and
segment bodies and functions at a segment call carry no ⊤⁺. Channels on a chain
are not packed into an existential and not passed to segment functions
(`pmid`). They send and receive only unit.

rtA_main creates d : Close⁵ after receiveTree returns c′ : Wait⁹, closes d while
it holds c′ and then waits on c′. rtB_main creates d : Close¹², waits on c′
while it holds d, then closes d. Their rules accept both, 5 < 9 and 9 < 12.
Version 3 types rtA with d on the low chain and rtB with d on the high chain.

A program that orders one d against c′ in both directions, for example
c′ : !⁹; Wait¹³ and d : ?¹⁰; Close¹² interleaved, stays out. Each point of d
would have to lie between two walks of c′, whose ranks the data fixes.

#### 15.4  What a world of facts would add

A world of facts orders the points by the facts that a derivation uses and by
program order, and a strict world exists when those facts are acyclic. It
covers what the rank world cannot. The post-call channel c′ can sit just above
the actual end of the segment, with the channels created afterwards ordered
against it by their static priorities, and the lockstep facts of a two channel
segment function hold by construction. The proof obligation is acyclicity of
the facts of the whole closed program. 15.2 shows that it fails for loops with
different rates. For the post-call channel the argument would read the run.
The segment instants have to precede c′, the channels compared with c′ after the
call were created or received after it, and every comparison among them follows
static priorities. A proof needs an invariant over all threads that relates the
facts of each thread to the order of the run, which is the progress argument
itself. Version 3 does not build this world. It keeps the rank world, whose
strictness is free, and records the two cases that need the world of facts,
two way interleaving after a segment call and two channel segment functions
(U2), in section 13.

## Ported to the exists core (2026-11-04)

Versions 1 to 3 run on the merged core of branch `cfst` (docs/extensions/
context-free.md, section "Ported to the exists core"). All 19 files of
theories/mp build, and no theorem changed its statement. `mp_translate`,
`mp_deadlock_free`, `mp2_translate`, `mp2_deadlock_free`,
`mp2_deadlock_free_source`, `mp3_translate`, `mp3_deadlock_free`,
`mp3_deadlock_free_source` and the 29 example theorems have closed
`Print Assumptions`.

### What changed

- The translation stays at its world `Wmp`. Every fact it uses comes from
  the rank of a denotation through `good` at `Wmp`. Moving it to `styped`
  would mean passing every rank comparison as a hypothesis, which is a
  redesign of the translation. PGV makes the same choice on `exists`
  (SHARP-EDGES 111).
- Translated new is `let_new_pair e′`, typed by `t_new_at` at the point
  `rpt B (RCh Q n d)` of the channel. In version 3 the channels below the
  floor and above the ceiling use the first points of the low and high
  chains.
- The simulations relate source new to `let_new_pair`. `post` at a new step
  allows β steps after it, so the target runs new ∗ and the two lets of the
  encoding before the relation holds again, as PN does on `exists`.
- Under K11 a choice continues at x[i]. `dsl` gives the points 0 and 1 of a
  choice its two branches, and the world states x ≺ x[i] through the rank.

### What broke and how it was fixed

- Channels at the end of a segment need x ≺ x[i] too, and only the segment
  and existential constraints can supply it. `pex_fact` gained the family
  `mwalk κ u ≺ (mwalk κ u)[i]` for every walk u. `dsl` guards every point
  that is no anchor, so each of its payload points rises (`dsl_rise`).
- A payload point is junk unless the payload lies above its carrier. So
  `ch_pay` takes the premise of R1 and R3 that the payload lies above,
  which `snd_ok` and `rcv_ok` already provide. `pts_ok` and `cseg_hold`
  gained the same conjunct.
- Lower bounds `Some x` became `LPt x`, and E-Pack asks the ⊥ flag of the
  packed type to be off. The flag tactics `bot_false`, `lbhb` and `bclean`
  come from PN on `exists`.

SHARP-EDGES 145 has the details.

## Gaps checked against the core (2026-11-04)

Branch `cfst-gaps` checks the items of section 13 that the repaired rules
type and versions 2 and 3 do not translate. An item counts as a gap of the
core only for a concrete program that their repaired rules type and the core
does not. Three such programs now type in the core with a whole-program
`styped` derivation and `soundness_source`. One item needs a change of the
semantics, which waits for the author. Every claim about the paper is in the
store with its page.

| Item | Concrete program | Their rules | Core | Status |
|---|---|---|---|---|
| drop at Skip | `sd_main`, SkipDrop.v | type it | no, the run keeps a restricted name | needs a decision |
| second linear parameter (U2) | `copy`, TreeCopy.v | type it | `tree_deadlock_free` | translation artefact |
| channel after a call, both directions | `si_go`, SegmentInterleave.v | type it | `si_deadlock_free` | translation artefact |
| µ body with a type variable | `lp_go`, MuVar.v | type it | `lp_deadlock_free` | translation artefact |
| unopened segment result | `rt2_main` below | type it | drain's λr. r | translation artefact |
| channel held across a call, sent after it | `hc_main` below | reject it | | no gap |
| channel created after a call, sent on the returned channel | `sd_go`, SegmentDeleg.v | type it | `sd_deadlock_free` | translation artefact |
| held channel sent at the first action | `fa_go`, FirstAction.v | type it | `fa_deadlock_free` | translation artefact |
| held channel sent where the data decides | `ll_main` below | reject it | no | no gap |

### Dropping a channel at Skip

```
sd_main = let (x, y) = new (!∗;Skip) in
          spawn (λu. let () = u in (λ_. ∗) (send ⟨∗, x⟩));
          let (_, _) = recv y in ∗
```

Their rules type it. Skip has priority ⊤ (Fig. 4, p. 11), S-Top copies a
type of priority ⊤ into both halves of a split (Fig. 12, p. 24), and T-Var
and T-Const accept a rest of priority ⊤ (pp. 12, 25). Their structural
congruence removes the restriction once no thread mentions its endpoints
(Fig. 15, p. 30), so the run ends in •⟨()⟩.

Our semantics keeps a restricted name until a close or a link releases it,
and `terminated` asks for no restricted name. `sd_not_deadlock_free` runs
`sd_main` to ({a}, {[+ ∗; ∗ +]}), which makes no step and is not terminated.
So no typing rule alone can let a thread drop a channel at Skip, and the
change reaches the statement of `soundness`. Two ways are open.

1. `terminated` accepts restricted names that no thread mentions. This is
   what their ≡ does. E-Stop and P-Stop then accept entries at Skip next to
   the value, and readiness skips entries at Skip, because they offer
   nothing and their partner is at Skip too.
2. A process step releases a restricted name that no thread mentions. The
   relation needs the same changes, and every simulation of theories/pgv,
   theories/pn and theories/mp gains a case.

Either way the weakening lemma has to absorb a Skip end that a message
brings in, because the partner may delegate its end at Skip. No example of
the paper drops a channel. Each ends its channels with Close or Wait.
SHARP-EDGES 151 has the details.

### Segment functions with a second linear parameter

The core types `copy` (TreeCopy.v, `tree_deadlock_free`), so U2 is an
artefact of the translation. The plan was to build the lockstep facts into
the creation constraint of each new, where `cc_ok` is a local check. The
translation states its result at the world `Wmp` with `typed`, and every
fact it uses comes from a rank of a denotation. Facts from creation
constraints need `styped` with the facts of the derivation as hypotheses,
which is the redesign that SHARP-EDGES 145 declined. It is not done.

### A channel ordered against the returned channel in both directions

SegmentInterleave.v types the program of section 15.3 with treeSum as the
segment function. The server gets c′ at κ′, creates d at δ under the
creation constraint {κ′ ≺ δ, δ+1 ≺ κ′+1, δ+1 ≺ z}, sends on c′ while it
holds d, receives on d and closes d while it holds c′, and closes c′. Each
fact relates δ to a known point, and the only fact it derives between known
points is κ′ ≺ κ′+1, so `cc_ok` holds (`sid_ok`). Their rules type the same
program with c′ : !⁹;Wait¹³ and d : ?¹⁰;Close¹² (T-Let, p. 25).

### µ bodies with a type variable

```
loop : ∀p ∈ (⊥,⊤). ∀a :: p. (µβ.∀^S ι.&^ι{Done: a, More: ?^{ι+1}Unit;β}) → a
loop c = match inst c with { Done c → c,
                             More c → let (_, c) = receive c in loop{next c}[a] c }
lp_main = let (x, y) = new (µβ.∀^S ι.⊕^ι{Done: Close⁵⁰, More: !^{ι+1}Unit;β}) 1 2 in
          fork (λ_. close (select Done (inst (send () (select More (inst x))))));
          wait (loop{1}[Wait⁵⁰] y)
```

F-PAbsS keeps ∆ when it forms ∀^S ι.S, and F-Rec forms µγ.T under ∆ (Fig. 9,
p. 22), so the body may mention a. The checks at the sequence [1, 3, 5, …]
are 1 < 2 < 3 < 50. The core has no rule that excludes the program. Session
instantiation goes under µ with `sty_up`, and V-Box ranges over hereditarily
contractive instances. The loss comes from the translation, where an
instance of a with its own ∀^S would nest ∀^S. A mechanized example is
missing. Unfolding the instantiated µ needs a fusion lemma for `sinst` after
`sren`, which types/Types.v does not have.

### Returning an unopened segment result

```
rt2 : ∀p ∈ (⊥,⊤). ∀a :: p. TreeChannel;a → (Tree, a)
rt2 c = receiveTree{p}[a] c
rt2_main = rt_main with rt2 in place of receiveTree
```

T-AbsLin and T-App type rt2 at the type of receiveTree (p. 25). The core
already returns the result of a segment call. drain returns the result of
its second recursive call through λr. r, which opens it and packs it again
at its own lower point (TreeCopy.v), and treeSum does the same around its
reply. The translation can open the result at the call and pack it with the
caller's lower point. Versions 2 and 3 do not, because their priority
abstractions return no unopened segment result.

### Handing over a channel on the channel a call returns

```
hc_main = let (d, d′) = new (Close¹²) in let (t, c′) = receiveTree{1}[!⁹Close¹²;Wait¹³] c in
          close (send d c′) …
```

Their rules reject it. receiveTree has latent effect ⊤ (p. 21), and T-Let
asks the effect of the call below the priority of everything the
continuation holds (ρ₁ < |Γ₂|, p. 25), so d at 12 cannot be held across the
call. A channel created after the call can be sent. SegmentDeleg.v creates
d at the payload point κ′[0] of the returned channel and sends it on c′. The
send owes κ′ ≺ κ′[0], which the existential of treeSum states along every
walk. The client receives d at (α·w)[0] and closes it in a thread of its
own. Their rules type this program with d at 12 and c′ : !⁹(Close¹²);Wait¹³,
because the send asks 9 < 12 (Fig. 5, p. 11).

### Handing over a held channel inside a segment function

A held channel d enters a function as a second linear parameter. In the core
a send asks the payload's point to be the payload point of the carrier
(O-Send reads `payload_at`). Two programs differ in where the send happens.

```
fa c d = let c = send d (inst c) in receiveTree{next c}[a] c
fa_main = … d created at 12, c : !⁵(Close¹²);TreeChannel;Wait⁹⁹ …
```

The send is the first action of c. Their rules check it at the call with the
concrete sequence of c, 5 < 12 (p. 39). The core needs the box constraint of
fa to state ι ≡ κ[0] for the point ι of d, and the caller creates d at κ[0].
This is not mechanized.

```
ll c d = match inst c with { Leaf c → send d c,
                             Node c → let c = ll{next c}[TreeL;a] c d in receiveTree{next c}[a] c }
```

ll sends d at the leftmost leaf, so the walk of the send depends on the tree.
The core cannot type it, because d has one point and the payload point
(κ·w)[0] depends on the walk w. Their repaired rules reject it too. The
payload check of send asks the carrier's priority below the payload's
(ι₂ ∈ (⊥, ι₁), Fig. 5, p. 11). Repair R8 asks the check at every round, and
the carrier's priority grows by at least one per level of the tree while
the priority of d stays fixed. Their rules as printed check only the first
round (pp. 28, 29), and section 15.2 shows why that is unsound. So ll is no
gap. fa stays open until an example types it in the core.

### Addendum (2026-11-04), the two open programs type

Branch `claude/cfst-open-examples-ftovnz` types both programs in the core
with a whole-program `styped` derivation and proves deadlock freedom with
`soundness_source`. No definition of the core and no statement of an
existing theorem changed. Every theorem below is closed under the global
context.

```
Lemma sinst_sren σ r s : sinst σ (sren r s) = sinst (σ ∘ r) s.     (types/SinstFusion.v)
Lemma unroll_up b s : sinst (SMu b .: SVar) (sren S s) = s.

Lemma lp_typed W F : world_wf W → typed W ∅ [] ∅ [] F lp lp_ty.   (examples/cfst/MuVar.v)
Lemma lp_go_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) lp_go TUnit.
Theorem lp_deadlock_free : deadlock_free (∅, {[+ lp_go +]}).

Lemma fa_typed W Ψ F : world_wf W → typed W ∅ Ψ ∅ [None; Some tsum_ty] F fa fa_ty.
Lemma fa_go_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) fa_go TUnit.   (examples/cfst/FirstAction.v)
Theorem fa_deadlock_free : deadlock_free (∅, {[+ fa_go +]}).
Theorem fac_deadlock_free : deadlock_free (∅, {[+ fac_go +]}).
```

lp. loop is a box over κ, ζ and one session variable a with the
constraint and the result of treeSum. Its channel has type µβ. &(a, ?∗;β)
at κ. The body is typed at every hereditarily contractive instance s of
a, where the µ body holds sren S s. Unrolling substitutes the µ for β, and
`unroll_up` turns the substituend back into s (`LpI_unroll`). Done packs
the channel at κ[0], More receives at κ[1], calls loop at κ[1]+1, opens the
result and packs it again at κ. lp_go runs loop at a := Close against a
client that sends one More and then Done. The priority abstraction ∀^S ι
of their type has no counterpart inside a session type of the core. Its
role goes to the points of the walk and the facts of the box constraint.

fa. fa is a box over κ, ι, ζ and a with the constraint
C = {ι ≡ κ[0]} ∪ {κ·w ≺ ζ, κ·w ≺ (κ·w)[i] ∣ w, i}. It takes c at κ and d at
ι as a pair, moves d to κ[0] with E-Conv and the fact ι ≡ κ[0], sends it
on c at κ and calls treeSum at κ+1. The caller creates d at the payload
point α[0] of its channel c at α and forces fa at [α; α[0]; z], where
ι ≡ κ[0] holds by reflexivity. The other end of c receives d at its own
payload point α[0] and runs the tree client of TreeSum.v from α+1. Each
end of d is closed in a thread of its own. Their rules pass c and d as two
curried arguments and check 5 < 12 at the call (p. 39). The core checks
the send once, in the body of fa against its constraint. The curried form
fac types too (`fac_typed`, `fac_go_typed`, `fac_deadlock_free`). Applied
to c, fac returns a closure with the lower point κ, and only the second
application carries the upper point ζ.

So fa_main is no gap of the core, and lp_main needed one lemma about
session substitution and no change of a rule.
