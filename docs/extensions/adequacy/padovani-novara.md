# D.2 Adequacy for Padovani and Novara (FORTE 2015)

Status. Stage 1 done on 2026-10-30. Stage 2 done on 2026-10-30 in
theories/pn/ (section 7), with the general theorem `pn_deadlock_free` and both
examples closed under the global context. Same procedure as for PGV
(pgv-adequacy.md). Study first, then model the system on our terms and
translate it into the static system.

Source. L. Padovani and L. Novara, Types for Deadlock-Free Higher-Order Programs,
FORTE 2015, LNCS 9039, pp. 3–18. Indexed as padovani2015types with full text. The
longer technical report hal-00954364 has different rule names ([T-REC POLY], a
displacement constructor). The published chapter is the reference, and the
report is read only where the chapter leaves a gap. It is indexed as
padovani2014typesTR with full text.

## What the system is

A higher-order functional language with fork, new, send and recv over linear
channels, which are used exactly once. Synchronous communication, send blocks
(p3). Channel types p[t]^n carry a level n. Judgments Γ ⊢ e : t & ρ carry an
effect ρ, and arrows t →^{ρ,σ} s carry the level of the closure and the latent
effect (p8). Level polymorphism is level shifting ⇑ⁿ, applied by [T-APP-POLY] to
functions of level ⊤, and the recursive calls of fibo need it, so it is
polymorphic recursion (p10). Effect masking and polymorphic recursion are the two
key ingredients (p15). Examples are parallel Fibonacci (p5, p11) and a cyclic
signal pipe with a recursive channel type (p5, p13).

## Stage 1 results

Page numbers are pdf pages of the stored HAL copies, p for the chapter
(hal-01767327) and TR p for the report (hal-00954364v1). The chapter states its
theorems without proofs and points to a long version (p4, p14). The report proves
a different system, so section 4 checks the chapter's rules against the report's
proof. One closed program types and gets stuck, which the chapter's definition
counts as a deadlock. It involves no channel (section 4,
padovani-novara-counterexamples.txt). We found no program that types and
deadlocks on channels.

### 1  Levels, effects and arrows

Levels are L = ℤ ∪ {⊥, ⊤}. Types are B, p[t]ⁿ and t →^{ρ,σ} s, with p a
nonempty set of polarities and # = {?, !} (p7). The level of a type is |B| = ⊤,
|p[t]ⁿ| = n and |t →^{ρ,σ} s| = ρ. A type is linear when its level is an integer
and unlimited when it is ⊤. ρ is the least level of a channel in the closure, and
σ is the greatest level of a channel the call acts on (p7). |Γ| is the least
level in Γ, and |∅| = ⊤.

```
constants (p7)                                  → abbreviates →^{⊤,⊥}
  fix  : (t → t) → t
  fork : (unit →^{ρ,σ} unit) → unit
  new  : unit → #[t]ⁿ                            n < |t|
  recv : ?[t]ⁿ →^{⊤,n} t                         n < |t|
  send : ![t]ⁿ → t →^{n,n} unit                  n < |t|

expressions (p8, p10)
  T-Name      Γ, u : t ⊢ u : t & ⊥                                   un(Γ)
  T-Const     Γ ⊢ k : t & ⊥                                          un(Γ),  t ∈ types(k)
  T-Fun       Γ, x : t ⊢ e : s & ρ   ⇒   Γ ⊢ λx.e : t →^{|Γ|,ρ} s & ⊥
  T-App       Γ₁ ⊢ e₁ : t →^{ρ,σ} s & τ₁    Γ₂ ⊢ e₂ : t & τ₂    τ₁ < |Γ₂|    τ₂ < ρ
              ⇒   Γ₁ + Γ₂ ⊢ e₁ e₂ : s & σ ⊔ τ₁ ⊔ τ₂
  T-App-Poly  Γ₁ ⊢ e₁ : t →^{⊤,σ} s & τ₁    Γ₂ ⊢ e₂ : ⇑ⁿt & τ₂    τ₁ < |Γ₂|    τ₂ < ⊤
              ⇒   Γ₁ + Γ₂ ⊢ e₁ e₂ : ⇑ⁿs & (n + σ) ⊔ τ₁ ⊔ τ₂

processes (p8)
  T-Thread    Γ ⊢ e : unit & ρ   ⇒   Γ ⊢ ⟨e⟩
  T-Par       Γ₁ ⊢ P    Γ₂ ⊢ Q   ⇒   Γ₁ + Γ₂ ⊢ P | Q
  T-New       Γ, a : #[t]ⁿ ⊢ P   ⇒   Γ ⊢ (νa)P

combination (p8)   t + t = t if un(t),    p[t]ⁿ + q[t]ⁿ = (p ∪ q)[t]ⁿ if p ∩ q = ∅
```

The effect of an expression is the greatest level of a channel its evaluation
acts on, and values have effect ⊥. T-Fun turns the effect of the body into the
latent effect and reads the level of the closure off Γ. Application evaluates
e₁, then e₂, then the body (p5). τ₁ < |Γ₂| keeps the actions of e₁ below every
channel of e₂. τ₂ < ρ keeps the actions of e₂ below the channels of the function
value, which already exists while e₂ runs (p9). The latent effect σ joins the
result effect, and the enclosing rules compare it with what the context holds.
The combination + hands the two polarities of a channel to two parts of the
program (p8). A thread ignores its effect. Two threads cannot close a cycle,
because every occurrence of a channel has the same level (p10).

The chapter has no pairs. Its examples use let and let … and … as sugar (p5),
read as application. Then let x = e₁ in e₂ asks τ₂ below the level of the
closure λx.e₂.

### 2  Effect masking

fork has level ⊤ and latent effect ⊥ whatever the thunk does, and the chapter
calls this effect masking (p7). fibo uses it to hand the ! ends of a and b to two
children while the parent keeps the ? ends (p5). cont uses it to send without
blocking, which makes cont pure (p13). Masking is necessary in fibo. Without it
the first fork would have effect −2, the level of a, while the rest of the body
holds the ? end of a at −2, and T-App would ask −2 < −2. The report's Example 3.2
shows the same pattern inside one pair (TR p8).

Masking is sound because fork never blocks. fork v reduces at once to () and a
new thread ⟨v ()⟩ (p5), and afterwards the parent holds none of the thunk's
channels. Every channel keeps its level in both threads, and the argument across
threads in section 4 reads levels only. In the report's proof the fork case of
subject reduction types v () as a thread of its own (TR p15). Our spawn :
(∗ ⊸^u_ℓ ∗) ⊸^⊥_⊤ ∗ is the same masking. Its upper point is ⊥ whatever the
thunk's u.

### 3  Shifting and recursion

⇑ⁿ adds n to every finite level of a type and leaves ⊥ and ⊤ alone (p10).
T-App-Poly lets a function of level ⊤ take an argument whose levels are shifted
by n, and it shifts the result and the latent effect by the same n. A function of
level ⊤ holds no channel, so it acts only on channels of its argument and on
channels it creates, and its whole typing shifts with them (p10). A function of
lower level holds channels at fixed levels. fwd = λx.λy.send y (recv x) shows the
danger. With a at level 2, fwd a has level 2, and one more shift would type
fwd a a, which deadlocks (p11).

fix takes a function of type t → t, which means t →^{⊤,⊥} t. The recursive
function is therefore typed in an unlimited environment and has level ⊤ at every
occurrence. Each recursive call can go through T-App-Poly at a new shift, which
makes it polymorphic recursion (p10). fibo has type int → ![int]⁰ →^{⊤,0} unit.
Its fresh channels sit at a : −2 and b : −1, because recv a + recv b orders a
before b and both block the send on c. The call on a is T-App-Poly at shift −2
(p11). Example 3 applies fibo (n − 2) to a, while the code of Example 1 applies
fibo (n − 1) to a (p5). Both orders type.

The pipe needs a channel type whose payload is the same type two levels up,
t^n = ?[t^{n+2}]^n, and no regular type solves that equation (p12). The
constructor ⌈t⌉ⁿ postpones the shift. |⌈t⌉ⁿ| = n + |t|, and wrap and unwrap
convert between ⌈t⌉ⁿ and ⇑ⁿt (p12, p13). Then t^n = ?[⌈t^n⌉²]^n,
s^n = ![⌈t^{n+1}⌉²]^{n+1}, cont : s^n → s^{n+2} and
pipe : t^n → s^n →^{n,⊤} unit (p13). We checked the body by hand. unwrap (recv x)
has type t^{n+2} and effect n, so pipe (unwrap (recv x)) is T-App-Poly at shift 2
with type s^{n+2} →^{n+2,⊤} unit. cont y has type s^{n+2} and effect ⊥. The outer
T-App asks n < |y| = n + 1 and ⊥ < n + 2. Each round adds 2 to the latent effect,
so σ = 2 + σ forces σ = ⊤. An effect ⊤ admits no later action, so pipe stands
only in tail position (p13). In the main program pipe b (cont a) is T-App-Poly
at shift 1.

The chapter claims that the pipe deadlocks when cont sends without fork (p6).
That variant types and runs forever. cont′ = λx. let c = new () in
(send x (wrap c)); c has type s^m →^{⊤,m+1} s^{m+2}, and in the body of pipe the
argument cont′ y has effect n + 1 < n + 2. At run time the second thread's
cont′ a sends on a while the first thread receives on a, and from then on each
send of one thread meets a receive of the other. The other variant of the claim,
pipe b a in place of pipe b (cont a), deadlocks and does not type.

### 4  The soundness proof

The report's proof reads levels in one lemma (TR p14 to p18). Lemma A.20 says
that in a thread E[recv a] or E[a!v] every other free channel b of E or v has a
level above that of a (TR p17). Its cases are the side conditions. n < |t| of
send covers the payload, τ₁ < |Γ₂| covers E e, τ₂ < ρ covers v E, and ρ₂ < |t₁|
of T-Pair covers a pair whose left value is held. The value cases use Lemma A.5,
a value's type has the level of its environment (TR p14). Lemma A.22 takes, in a
stable process, the channel c of least level among those whose both ends the
process holds. By Lemma A.20 no thread holds c inside a context or a payload, so
both ends are subjects of pending actions and the process reduces (TR p17). This
is the corrected PGV argument of pgv-adequacy.md §4. It compares the subject with
every other channel directly, and no bound of a whole evaluation context enters.

The places where PGV fails hold here.

- Payload against carrier. new, send and recv all ask n < |t| (p7).
- Pairs. The chapter has none. The report's T-Pair asks ρ₂ < |t₁| (TR p7).
- let. As sugar, let x = e₁ in e₂ checks the effect of e₁ against the closure of
  λx.e₂, which is all the context holds while e₁ runs. The value of e₁ does not
  exist yet. The report's T-Split asks ρ < |Γ₂| (TR p7).
- Forked closures. Section 2.
- Recursive types. The level stays well defined under the contractiveness
  condition (p13). wrap and unwrap move no channel, and unwrap (wrap v) → v keeps
  every level.
- T-App-Poly. The report has no such rule. It proves a system with bounded
  quantification, [T-Rec Poly] and displacements $ρ (TR p9), so no published
  proof covers the chapter's system. The missing piece is one lemma,
  Γ ⊢ e : t & ρ ⇒ ⇑ⁿΓ ⊢ e : ⇑ⁿt & n + ρ. Every rule keeps it, because
  |⇑ⁿt| = n + |t| and every constant scheme is closed under ⇑ⁿ. T-App-Poly keeps
  it too, because ⇑ⁿ and ⇑ᵐ commute. At run time the closure of a function of
  level ⊤ is a ground environment of level ⊤ and hence empty, so the β step under
  T-App-Poly shifts the body alone. In Lemma A.20 the case v E under T-App-Poly
  holds because v has level ⊤ and so holds no channel.

The stuck program is ⟨(λ_.()) (fix fix)⟩. Section 3.3 admits infinite types, and
s = s →^{⊤,⊥} s is contractive. At t = s the scheme (t → t) → t of fix equals
s → s, so fix fix has type s. fix fix is no value and matches no rule, because
fix reduces only when applied to an abstraction (p5). Definition 1 counts the
irreducible thread as a deadlock (p14), against Theorem 2. The report has no such
case, because its recursion is the binder rec x e (TR p6).
padovani-novara-counterexamples.txt gives the derivation and the repairs. It is a
progress failure of the constant fix and says nothing about levels.

### 5  One static order

Every derivation gives one strict world. Rank each instant by its level and break
ties by the instant, rank(x) = (level, b) for x = (p, b), ordered
lexicographically in ℤ × ℕ, and let x ≺ y when rank(x) < rank(y). A one-shot
channel has two instants in our encoding, the message at (a, 0) and the close at
(a, 1). Program order (a, 0) ≺ (a, 1) holds by the second coordinate, and no
session falls. A sent channel sits at the carried root of its carrier, and P&N
gives the two the same type and so the same level. Aliases therefore keep ranks
equal, and a world whose order comes from a rank is strict.

Our worlds differ from levels in five places.

- Names. A level is a number in a type, and a world speaks about named points.
  Channels from top-level new become constants. Channels created or received
  under a box become carried roots of its instance points, as in the relay and
  the forwarder.
- Shifts. T-App-Poly at shift n becomes a force at an instance whose levels are
  shifted by n. The box constraint states the relative facts, and a rank world
  satisfies them at every instance that keeps relative levels. For a recursive
  box the constraint covers every descendant of the instance, so it is infinite.
  Spec §4 allows that.
- Unbounded ranks. fibo's levels fall without bound (−2, −4, …) and the pipe's
  rise without bound, so ranks go into ℤ. A world needs no well-founded order,
  because a finite configuration has finitely many pending points.
  ExampleTools.v ranks into ℕ or pairs of ℕ.
- Effect ⊤. Our upper points are ι or ⊥. A latent effect ⊤ becomes a ceiling ζ
  with every instant of the recursion below ζ, as in tc_deadlock_free. The ranks
  then need a top element.
- Arrow bounds. ρ and σ are numbers, and ℓ and u are points. ℓ must lie at or
  below every head of the closure, and u above every action of the call and below
  the caller's frame. A level has no point of its own, so the translation needs
  points for levels (section 6).

None of these needs more than one world per program.

### 6  Plan for stage 2

Fragment v1 is the chapter's system with four restrictions.

- Base types are unit only. fibo keeps its shape with its test as a case on an
  argument d : ∗ + ∗. The call on a passes inj₁ ∗ and the call on b passes inj₂ ∗,
  so the left spine ends and the right spine recurses forever. The levels and
  shifts stay those of the paper.
- Payloads are channels and unit. A payload function would need carried points
  for its ℓ and u.
- fix stands only as fix λx.e at an arrow type of level ⊤ (repair R2 of the
  counterexample file). This excludes fix fix and the diverging fix at a linear
  type.
- Recursive types stay, with wrap and unwrap erased. Our session types are
  regular where the leveled types are not, because the world carries the shift.
  t^n becomes μα.?(∃ι. α@ι).Close, and the payload's rank two levels up is a fact
  about the carried root ι.1.

Types, with lo(n) and hi(n) the points for level n described below.

```
[unit]          = ∗
[?[t]ⁿ]         = (?(∃ιs. [t]).Close)@ι         ι the channel's point, payload channels at ι.1 … ι.k
[![t]ⁿ]         = (!(∃ιs. [t]).Close)@ι
[t →^{ρ,σ} s]   = [t] ⊸^{hi(σ)}_{lo(ρ)} [s]       ρ ∈ ℤ,  hi(⊥) = ⊥,  hi(⊤) = a ceiling ζ
[t →^{⊤,σ} s]   = □(∀ι₀ ιs. C. ∗ ⊸^⊥_⊤ ([t] ⊸^{hi(σ)}_⊤ [s]))
```

A name a : #[t]ⁿ becomes the two ends of new, split as + splits the polarities.
send e₁ e₂ becomes a send followed by close, and recv e a receive followed by
close. fork becomes spawn. A function of level ⊤ becomes a box, and its
application a force followed by E-App. fix λx.e becomes the recursive box
!(x = …), and a recursive call a force of x at the shifted instance.

Points for levels. lo(n) and hi(n) rank at (n, −1) and (n, ω), below and above
both instants of every channel at level n. Inside a box they are carried roots of
a level anchor ι₀, a point that no channel uses. The instance of ι₀ carries the
shift of T-App-Poly, and the instance of ιs are the points of the argument's
channels. Two lo points of one level reached along different paths must be
aliased, or {ℓ} ≼ heads fails between two closures of equal level. C therefore
holds ≡ facts that collapse a path of offsets to its sum. A fresh channel of a
box body sits at a carried root of ι₀ coded by its level offset and its new site,
so carried congruence along the collapse aliases relates payloads of equal type
only. The examples can do with less. fibo creates a and b at ι.1 and ι.2, carried
roots of c's message, which carries no channel. The pipe creates c at ι′.1, the
carried root of y, and receives at ι.1.

Derivations. The lemma reads Γ ⊢ e : t & τ in P&N as [Γ] ⊢^F [e] : [t] for every
frame F with {hi(τ)} ≺ F, as the PGV plan reads its bound p.

```
T-Fun        E-Abs with ℓ = lo(|Γ|) and u = hi(ρ)
T-App        E-App. τ₁ < |Γ₂| gives the frame F ∪ heads(Θ₂, Δ₂) of t₁, τ₂ < ρ the frame F ∪ {ℓ} of t₂
T-App-Poly   E-Force at (ι₀ shifted by n, the argument's points), then E-App with ℓ = ⊤
T-Thread     P-Term at F = ∅
T-Par, T-New P-Connect over the restricted channel
```

World. W_P is the rank world of section 5 over the constants of top-level new,
the anchor root and their carried roots, with the aliases of delegation and the
collapse aliases.

Theorem. A closed process of v1 with ∅ ⊢ P translates to · ⊢_{W_P} [P] : ∗ with
W_P strict, so [P] is deadlock free by soundness. [P] differs from P by the
closes, the forces and the erased wraps. A simulation that skips them gives the
statement for P, on paper and outside Rocq.

Examples. The fibo of v1 and the pipe, each with a closed deadlock_free proof.
The pipe's box has the ceiling ζ and
C = {ι.1ᵏ ≺ ι′.1ᵏ ≺ ι.1ᵏ⁺¹, all instants below ζ ∣ k ∈ ℕ}, close instants
included, and its world ranks (a,0).1ᵏ at level n + 2k and (b,0).1ᵏ at n + 1 + 2k.
Here x.1ᵏ is x.1 … .1 with k carried steps.

Decisions for the author. The level anchor or argument-relative points for the
general theorem. The fibo of v1. Whether ExampleTools.v gets ranks into ℤ with a
top element. Whether the theorem goes into Rocq or stays on paper with the two
examples in Rocq.

## Stage 2 results

### 7  Mechanization

theories/pn/ proves the following, closed under the global context.

```
Theorem pn_deadlock_free e τ e' :
  pn_typed [] e PUnit τ e' → deadlock_free (∅, {[+ e' +]}).

Theorem pn_translate Γ e t τ e' :
  pn_typed Γ e t τ e' →
  ∀ Ψ B k ins Δ Φ F, good Ψ B → erel B k ins Γ Δ → ub_below_s Wpn Ψ Φ (hiz B k τ) F →
  typed Wpn Φ Ψ ∅ Δ F (rename (ren_of ins) e') (trz B k t).

Theorem fibo_deadlock_free :
  ∃ τ e', pn_typed [] fibo_main PUnit τ e' ∧ deadlock_free (∅, {[+ e' +]}).
Theorem pipe_deadlock_free :
  ∃ τ e', pn_typed [] pipe_main PUnit τ e' ∧ deadlock_free (∅, {[+ e' +]}).
```

Branch pn-adequacy, commits 9900084 (model, world, translation, theorem) and
cb18433 (examples).

#### 7.1  The judgment

`pn_typed Γ e t τ e′` (PNTyping.v) is Γ ⊢ e : t & τ of Table 2 (p8) with
[T-APP-POLY] (p10) on the terms of lang/Syntax.v. The last index e′ is the term
of the static system the derivation translates to. The translation needs the
types, because a function of level ⊤ becomes a box and its application a force.
Levels are `lvl` = ⊥ | ℤ | ⊤. Types are `pty` (PNTypes.v).

```
pty ::= PUnit | PSum t s | PChan inp t n | PRec inp m n | PDisp m t | PArr t r σ s
        ?[t]ⁿ / ![t]ⁿ    μα.p[⌈α⌉ᵐ]ⁿ    ⌈t⌉ᵐ    t →^{r,σ} s with r ∈ ℤ ∪ {⊤}

source syntax
  x, λ, application, ()             Var, Lam, App, EUnit
  fix λf.e                          EBox e, f the index 0 of e (repair R2)
  let a = new() in e                LetP (App ENew EUnit) e, a? at index 1, a! at index 0
  send e₁ e₂, recv e, fork e        App (App ESend e₁) e₂, App ERecv e, App ESpawn e
  inj₁ e, inj₂ e, case              Inj1, Inj2, Case (sums of unlimited types)
  wrap, unwrap                      erased, [T-Conv] at the top of a type
```

|t|, un(t), ⇑ⁿ, |Γ| and Γ₁ + Γ₂ follow p7, p8, p10 and p13. The shift goes
inside level-⊤ arrows and leaves basic types alone (p10).

#### 7.2  The world and the types

`Wpn` (PNWorld.v) has one root constant. Levels become slots of a level anchor
B. B[RAnc a] is the anchor shifted by a. B[RCh c] is the point of the channel
with code c, its message at offset 0 and its close at offset 1. B[RLo z] is the
lower point of level z, B[RHi z] the upper point of level z and B[RTop] the
ceiling for the latent effect ⊤. The root constant is the anchor of shift 0.
Inside a box the anchor is the box's one point variable, and a force
instantiates it with an anchor of the caller.

A denotation `den` reads points. It commutes with successor and slots and adds
the anchor's shift to every level of its slots. The rank `rank` of a denotation
is (level, instant) in ℤ × ℕ with a top element, read lexicographically.
B[RLo z] ranks at (z, 0), the message of a channel of level z at (z, 1), its close at
(z, 2), B[RHi z] at (z, 3) and B[RTop] at top. `Wpn` identifies two points of
the root with one denotation and orders two with rising rank. `Wpn_strict`
follows from `wgen_strict_den`, a new general lemma in ExampleTools.v next to
`wgen_strict_by`, together with `zrank` and `wgen_strict_z` (decision 4).

`trz B k t` translates ⇑ᵏ t at the anchor B.

```
unit               □(∀. C0. ∗ ⊸^⊥_⊤ ∗)                       (unit is unlimited in P&N, ∗ is linear here)
t + s              □(∀. C0. ∗ ⊸^⊥_⊤ ([t] ⊕ [s]))
p[t]ⁿ              (p(∃ιs. P).Close)@B[RCh c]               c the code of ⇑ᵏ p[t]ⁿ
μα.p[⌈α⌉ᵐ]ⁿ        (µα. p(∃ι. α@ι).Close)@B[RCh c]
⌈t⌉ᵐ               trz B (k + m) t                          (wrap and unwrap erased)
t →^{r,σ} s        [t] ⊸^{B[RHi σ+k]}_{B[RLo r+k]} [s]       r ∈ ℤ, σ = ⊥ gives ⊥, σ = ⊤ gives B[RTop]
t →^{⊤,σ} s        □(∀ι. Crel. ∗ ⊸^⊥_⊤ ([t] ⊸^{ι[RHi σ−m]}_⊤ [s]))   [t], [s] at anchor ι and offset −m
```

A channel payload sits at the first slot of the carrier's point (one binder).
The denotation sends that slot to the point of the payload's channel, so the
received channel converts by E-Conv. An unlimited payload needs no binder. m is
the first finite level of the arrow (`mlev`), so ⇑ⁿ of a level-⊤ arrow has the
same box type (`trz_lshift`). Crel holds every fact between points of the box
variable that the denotation and the rank give, an infinite constraint. A force
at the anchor B[RAnc a] meets it, because instantiating the variable at an
anchor of shift a adds a to every level (`den_inst`, `crel_hold`).

#### 7.3  How each rule maps

The lemma holds at every anchor B whose facts Ψ provides (`good`), at every
offset k (the shift ⇑ᵏ of the whole derivation, which is the missing lemma of
section 4 built into the induction), at every frame F above hi(τ), and up to
inserted unlimited or spent entries of Δ (`erel`).

| P&N | ours | side condition |
|---|---|---|
| T-Name | E-LVar after E-Weak | un(Γ) makes the other entries boxes |
| T-Const () | E-Exp of ∗ (`unitv`) | un(Γ) gives □Δ |
| T-Fun, \|Γ\| ∈ ℤ | E-Abs with ℓ = B[RLo \|Γ\|+k], u = hi(ρ) | ℓ ≼ every head of Γ (`env_lo_below`) |
| T-Fun, \|Γ\| = ⊤ | E-Exp then E-Abs with ℓ = ⊤, body at anchor ι and offset −m | □Δ, heads ∅ |
| T-App, ρ ∈ ℤ | E-App | τ₁ < \|Γ₂\| puts hi(τ₁) below heads(Δ₂), τ₂ < ρ puts hi(τ₂) below ℓ |
| T-App-Poly at n | E-Force at B[RAnc k+n+m], E-Conv, E-App | Crel holds at the anchor, the forced arrow converts to ⇑ⁿ by ≡ of the denotation |
| let a = new() in e | E-LetPair over E-App of new | the point B[RCh c] is known |
| send e₁ e₂ | E-App of `send_tr` = λc.λv. send (v, c) ; close | hi(n) above both instants, payload above the carrier |
| recv e | E-App of `recv_tr` = λc. let (v, c′) = recv c in close c′ ; v | the close lies below the payload's head |
| fork e | E-App of `fork_tr` = λf. spawn (λz. z ; force (f ∗)) ; ∗ | spawn's upper point ⊥ is P&N's masking |
| fix λf.e | E-Exp of force e at the box's own ι | the body's hypothesis (Crel, ι) |
| inj₁ e, inj₂ e | E-App of λx. !(y = injᵢ x) | un components |
| case | E-Case over force e | τ₁ < \|Γ₂\| |
| T-Conv | E-Conv | unfolding keeps the point and unrolls the µ, ⌈t⌉ᵐ and ⇑ᵐ t translate alike |
| T-Thread | P-Term at F = ∅ | none |

Print Assumptions. `pn_translate`, `pn_deadlock_free`, `fibo_deadlock_free` and
`pipe_deadlock_free` are closed under the global context, and so are the 31
earlier ones (35 in all).

#### 7.4  Examples

fibo (`fibo_deadlock_free`). The printed program of Example 1 with unit for int.
The test n ≤ 1 is a case on d : unit + unit, fibo (n − 1) a and fibo (n − 2) b
are fibo (inj₁ ()) a and fibo (inj₂ ()) b, recv a + recv b is
plus (recv a) (recv b) with plus = λx.λy.(), and send c n is send c (). The main
program is let c = new() in (fork λ_.fibo (inj₂ ()) c); recv c. c has level 0,
a level −2 and b level −1 (p11). The calls are T-App-Poly at the shifts 0 and −2
for a, 0 and −1 for b, 0 and 0 in the main program. The right spine recurses
forever.

pipe (`pipe_deadlock_free`). Example 2 with the types of Example 4 (p13) and
the main program of p5, both pipes forked. tⁿ = μα.?[⌈α⌉²]ⁿ,
sⁿ = ![⌈tⁿ⁺¹⌉²]ⁿ⁺¹, cont : s⁰ → s², pipe : t⁰ → s⁰ →^{0,⊤} unit. The recursive
call is T-App-Poly at the shift 2. In the main program a has level 0 and b level
1, pipe a b is at the shift 0, pipe b (cont a) at the shift 1 and cont a at the
shift −1. The fresh channel of cont has level 3 and payload ⌈t³⌉², folded to t³
and wrapped to ⌈t¹⌉² by T-Conv.

#### 7.5  Discrepancies with the paper and the report

Every place where the Rocq model differs from the chapter (hal-01767327) or the
report (hal-00954364v1), one per line, with its location.

- PNTypes.v `pty`. int is left out. unit is the only basic type.
- PNTypes.v `PSum`, PNTyping.v `pn_inj1`, `pn_inj2`, `pn_case`. Sums t + s are an addition. Neither the chapter nor this fragment of the report has them. A sum is a basic type with level ⊤, and ⇑ⁿ leaves it alone.
- PNTyping.v `pn_inj1`, `pn_inj2`, `pn_case`. Both components of a sum must be unlimited. A sum of linear types is not typable.
- PNTyping.v `pn_case`. The side condition τ₁ < |Γ₂| and the result effect τ₁ ⊔ τ₂ are our choice, by analogy with let as application (p5) and T-Split of the report (TR p7). Both branches have one effect τ₂.
- PNTypes.v `PChan`. Polarities are ? and !. The full polarity # is no type of a variable.
- PNTyping.v `pn_new`. new appears only as let a = new() in e, applied to the literal (). The name a of type #[t]ⁿ becomes two variables, its ? end at index 1 and its ! end at index 0, because our new returns both ends and our variables are linear. The rule is T-App on (λa.e)(new ()), whose side conditions hold trivially.
- PNTyping.v. new is no value. λ_.new () has no type in the model, while the chapter types it at unit → #[t]ⁿ.
- PNTyping.v `pn_split`. + on variables merges no polarities. A linear variable goes to one side and an unlimited one to both. p[t]ⁿ + q[t]ⁿ arises only for names.
- PNTyping.v. Names, runtime typing, T-New and T-Par are not modelled. The theorem covers closed programs ⟨e⟩, as for PGV.
- PNTypes.v `PArr`. The level of an arrow is in ℤ ∪ {⊤}. Level ⊥ is left out. No rule produces it, and no function of level ⊥ can be applied (τ₂ < ⊥ fails).
- PNTyping.v `pn_send`, `pn_recv`, `pn_fork`, `pn_fix`. Constants appear only applied. T-Const covers () alone. Unapplied send, recv and fork are η-expanded by the programmer, with the same type (send = λc.λv.send c v has ![t]ⁿ → t →^{n,n} unit).
- PNTyping.v `pn_send`. The partial application send e₁, a value of type t →^{n,n} unit on p5, exists only inside send e₁ e₂. The rule is the composite of two T-App.
- PNTyping.v `pn_send`, `pn_recv`, `pn_fork`. Each rule takes one instance of the schema. T-App-Poly on a constant is T-App at the shifted instance, because every schema is closed under ⇑ⁿ. The model has no separate rule for it.
- PNTyping.v `pn_fix`. fix stands only as fix λf.e (repair R2) at an arrow of level ⊤, Γ unlimited, e of effect ⊥. This is exactly what T-App of fix : (t → t) → t to λf.e gives when t is an arrow of level ⊤.
- PNTyping.v `pn_app`, `pn_app_top`. T-App asks ρ ∈ ℤ. T-App at ρ = ⊤ is T-App-Poly at the shift 0 (`pn_app_top`), and its translation forces.
- PNTyping.v `pn_conv`, `pconv`. wrap and unwrap are erased from the syntax. A conversion relates μα.p[⌈α⌉ᵐ]ⁿ and its unfolding, and ⌈t⌉ᵐ and ⇑ᵐ t, in both directions and at the top of a type only. The chapter's types are trees, equal everywhere, and wrap and unwrap are constants (p13). Conversions inside payloads are not modelled.
- PNTypes.v `PRec`. Recursive types are only μα.p[⌈α⌉ᵐ]ⁿ, the channel that carries a later copy of itself. Other infinite types are left out, recursion through arrows among them. This also excludes the stuck program fix fix of section 4, which needs s = s → s.
- PNTypes.v `payok`. Payloads are channels, possibly wrapped, or unlimited types. A payload of linear arrow type is left out, because its points would need carried roots.
- PNTyping.v `penv`. Environments are de Bruijn lists. un(Γ) of T-Name and T-Const is weakening of unlimited entries.
- PNExamples.v. let x = e₁ in e₂ and e₁; e₂ are (λx.e₂) e₁, as p5 allows. e₁; e₂ binds an unused unit variable.
- PNExamples.v `fibo_pn`. int becomes unit + unit, the test a case, fibo (n − 1) and fibo (n − 2) become fibo (inj₁ ()) and fibo (inj₂ ()), + becomes plus = λx.λy.(), and send c n becomes send c (). The right spine does not terminate.
- PNExamples.v `fibo_main`. The chapter gives no main program for fibo. Ours is let c = new() in (fork λ_.fibo (inj₂ ()) c); recv c.
- PNExamples.v `cont_pn`, `pipe_pn`. cont and pipe are typed once at n = 0 and used at other levels by T-App-Poly, as p13 intends.

#### 7.6  Workarounds on our side

- PNWorld.v `trz`, PNTyping.v `unitv`. unit translates to the box □(∗ ⊸ ∗) and () to !(x = ∗), because P&N's unit is unlimited and our ∗ is linear. Sums translate to the box of the sum.
- PNTyping.v `send_tr`, `recv_tr`. A linear channel is a session with one message followed by Close. send and recv close the channel after the message, and both ends close.
- PNTyping.v `fork_tr`. fork applies the thunk to the box of ∗ and forces the result back to ∗ for spawn. A thunk of level ⊤ is forced first, at the anchor of shift 0.
- PNTyping.v `inj1_tr`, `inj2_tr`. inj e becomes (λx. !(y = inj x)) e, so the injection happens after e and inside a box.
- PNTyping.v `lam_tr`. A λ of level ⊤ becomes !(f = λx.e) with the box's index skipped by a renaming. fix λf.e becomes !(f = force e), which forces the inner box at the box's own variable.
- PNTyping.v `pn_app_poly`. An application of a level-⊤ function forces first.
- PNWorld.v `rpt`, `mneg`. A box binds one point variable, the level anchor. Every point of its type is a slot of it. The stage 1 plan had ∀ι₀ ιs with the argument's points, which turned out unnecessary. Shifted copies of one arrow share a box type through the normalization by the first finite level.
- PNWorld.v `Crel`. The box constraint is infinite, all facts that the denotation and the rank give between points of the box variable. The same constraint serves every box.
- PNWorld.v `chres`. Channel points are keyed by the channel's code (type up to polarity, wrappings resolved, one unfolding), not by a new site. Two channels with one type and level share a point. The stage 1 plan keyed fresh channels by level offset and new site.
- PNWorld.v `rank`. lo(n), the two instants and hi(n) rank at (n, 0), (n, 1), (n, 2) and (n, 3). The stage 1 plan said (n, −1) and (n, ω).
- PNWorld.v `hiz`. The latent effect ⊤ becomes the ceiling B[RTop], ranked at the top element. All ceilings are aliased.
- PNTranslate.v `erel`, `ren_of`. The static system has no lemma that inserts a binding, and a box body sees the box at index 0. The translation lemma therefore types e′ renamed past inserted unlimited or spent entries.
- PNTranslate.v `pn_translate`. Frames stand for effects, as for PGV. A thread is typed at the empty frame, which matches T-Thread ignoring the effect.
- PNTranslate.v `pn_deadlock_free`. The theorem is about the translation e′, which differs from e by the boxes, the forces, the closes, the closed λ terms of send, recv, fork and injections, and the erased wraps. A simulation from e′ to e is not mechanized.
- ExampleTools.v `zrank`, `wgen_strict_z`, `wgen_strict_den`. New general helpers for strict worlds by ranks into ℤ with a top element (decision 4).

#### 7.7  Findings about the paper, the plan and our documents

- Chapter p10. ⇑ⁿ of a level-⊤ arrow gives a different P&N type, although such a function is level polymorphic. Two shifted copies of one arrow are distinct P&N types and need T-App-Poly to be used alike. Our translation identifies them.
- Chapter p13. The contractiveness condition is needed for |⌈t⌉ⁿ|. The restricted μα.p[⌈α⌉ᵐ]ⁿ is contractive by construction.
- Report. The report proves a different system (section 4). Nothing in stage 2 used the report beyond T-Split as a model for the case rule.
- Stage 1, section 6. The plan's "∀ι₀ ιs" (one anchor plus argument points), its ranks (n, −1) and (n, ω), and its keying of fresh channels by new site differ from the mechanization (7.6). The plan's claim that the shift lemma Γ ⊢ e : t & ρ ⇒ ⇑ⁿΓ ⊢ e : ⇑ⁿt & n + ρ holds is confirmed in the form of the offset k of `pn_translate`, for our fragment.
- gvsharp-orders.lagda E-Weak (around line 827) and ORDERS-SPEC.md §9 state weakening with a named fresh variable. Rocq's `t_wk` is positional (an unlimited entry becomes spent) and the static system has no renaming lemma that inserts a binding. Nothing is wrong, but the lagda reading suggests a lemma that Rocq does not have. `erel` works around it.
- No core change was needed. lang/, types/, relation/, invariance/, composition/, rules/ and static/ are untouched.

## Stage 2, model and translate (after the author has seen stage 1)

- Linear channels as one-shot sessions on our terms. A channel of type p[t]^n
  becomes a session with one message at the point of level n.
- Arrows t →^{ρ,σ} s become T ⊸^u_ℓ U with ℓ from ρ and u from σ.
- Level shifting becomes a box ∀ι with the shift as the instance. [T-APP-POLY]
  applies only to functions of level ⊤, and our boxes hold no channel either.
- Recursion through fix becomes a recursive box whose constraint is the
  invariant over all shifts.
- Effect masking becomes whatever stage 1 shows it to be.
- World. Points by level, as for PGV, with the shifts as successor families.
- Theorem. A closed well-typed program is deadlock free, through soundness.
- Examples. fibo and the signal pipe, each with a closed deadlock_free proof.
