# A bidirectional algorithmic system with effects

State of 2026-11-04, on top of ORDERS-SPEC.md after sharp edges 152. Notation
follows the spec. p[j] is the payload point. The declarative reference is the
source judgment `styped` of static/Source.v, written Γ ; Δ ⊢_F t : T below with
Γ the hypotheses Ψ and the frame hypotheses Φ. Nothing here changes a
declarative rule or a theorem.

The mechanized part is theories/algorithmic/Algorithmic.v and
theories/algorithmic/Soundness.v. Section 9 says which rules of this file it
covers and how it differs from them.

## 1  What the algorithm does

A declarative derivation makes four kinds of guesses. It splits Δ at every
binary rule, it picks the instance of every constant scheme, it applies E-Conv
wherever two points or two session types have to agree, and it reads side
conditions from a fact context Γ that a whole program fixes only at its
creation constraints. The algorithm removes the first three guesses by
construction and turns the fourth into an output.

The output is a constraint 𝒞. Its atoms are the side conditions of the
declarative rules, written over the points of the program and over point
metavariables for the bounds the program leaves implicit. A solution of 𝒞 is a
fact context Γ, together with values for the metavariables, in which every atom
holds. Every solution gives a declarative derivation (Section 8). Which
solutions exist, and how to find one, is the job of the decision procedure of
algorithmic-decidable.md and of the inference step of Section 7.

Completeness is not claimed. The algorithm types a program when a derivation
exists whose conversions are the ones the algorithm performs (Section 4.3) and
whose splits are the occurrence splits (Section 4.1).

## 2  Judgments, modes and the three effects

Two judgments, both with the fact context as an output.

```
Φ ; Δ ⊢_F t ⇒ T  ⊣ 𝒞        synthesis: Φ, Δ, F, t in, T and 𝒞 out
Φ ; Δ ⊢_F t ⇐ T  ⊣ 𝒞        checking: Φ, Δ, F, t, T in, 𝒞 out
```

Φ maps every frame variable φ in scope to its one hypothesis u ≺ φ, or to
"no hypothesis" for a λ without an upper point. Δ is the linear environment,
a list with one entry per variable in scope. F is the future, a finite set of
points and at most one frame variable or the ⊥ flag (static/FactTheory.v).

The three effects of the system and their modes.

- The future F is inherited. Every rule passes F down, extended by the heads
  of what the context still holds, exactly as the declarative rules do. No
  rule synthesizes a future. This is the ambient effect.
- The upper point u of an arrow T ⊸^u_ℓ U is synthesized with the arrow. At an
  application it is checked against the ambient future by the atom u ≺ F. The
  thunk of a spawn is the one place where u is unknown, and there it is a
  metavariable (Section 4.5). This is the latent effect.
- The lower point ℓ of an arrow is checked at the λ that introduces it, against
  the heads of the environment the closure captures, by the atom ℓ ≼ heads(Δ).
  In checking mode ℓ comes from the expected type, in synthesis mode from the
  annotation or, for a spawn thunk, from a metavariable.

The points of a λ's body run under the future {φ} with the hypothesis u ≺ φ.
The algorithm picks φ fresh (a counter), so no rule reads φ from an oracle.

## 3  The constraint language

```
atom  ::= x ≺ y | x ≡ y | x ≼ y | u ≺ P | ℓ ≼_b H | known x | cc(C) | false
𝒞     ::= true | atom | 𝒞 ∧ 𝒞 | ∃ι:C. 𝒞
```

x, y, u, ℓ are point terms over the point variables in scope and over
metavariables α. P and H are finite sets of point terms. u ≺ P abbreviates
u ≺ y for every y ∈ P. ℓ ≼_b H is the lower-bound condition of E-Abs with the
⊥ flag b of H. known x is knownness of x. cc(C) says that C is a creation
constraint over the context in scope, which is the premise of new. ∃ι:C. 𝒞
binds the fresh point of a new under the hypothesis (C, ι).

Satisfaction in a hypothesis context Ψ reads the fact theory of
static/Source.v. x ≺ y is `hlt Ψ x y`, x ≡ y is `heqs Ψ x y`, cc(C) is
`cc_ok (heqs Ψ) (hlt Ψ) C`, and ∃ι:C. 𝒞 holds in Ψ when 𝒞 holds in Ψ shifted
past ι and extended by (C, ι). With metavariables, a solution also assigns a
point term to every α.

Three remarks on the shape.

- Frame variables do not occur in atoms. The gate u ≺ F of E-App is resolved
  at generation time against Φ. For F = (P, φ) with Φ(φ) = u′ the atoms are
  u ≺ P and u ≼ u′. For F with the ⊥ flag, or with a φ that has no hypothesis,
  the atom is false. [derived] The resolution is complete for the one
  hypothesis a frame variable has. A derivation of u ≺ φ in the fact theory
  ends in the rule for the hypothesis u′ ≺ φ, preceded by steps between points,
  so u ≺ φ holds exactly when u ≼ u′ holds (Soundness.v, `ub_constr_sound`,
  proves the direction the algorithm needs).
- Conversion produces ≡ atoms only between points. Session types are compared
  on the nose after the head normal form unr is taken (Section 4.3). An
  algorithm for bisimilarity of context-free session types would replace that
  comparison without touching the rest.
- The atoms of a program with n top-level point variables and no metavariable
  form a finite tree whose leaves are finite facts, with one binder per new.
  Deciding satisfaction in the context [(C₀, ιs)] is the finite ground fragment
  of algorithmic-decidable.md.

## 4  The rules for the core

Δ is a list indexed by de Bruijn variables, as in the Rocq development. An
entry is a type or a spent mark. heads(Δ) and the flag bot(Δ) are the heads and
the ⊥ flag of the available entries.

### 4.1  Splitting by occurrence

Every binary rule splits Δ into the part Δ₁ that the first subterm uses and
the part Δ₂ that the second one uses. The split is computed. Δ₁ keeps an
available entry when its variable occurs in the first subterm, Δ₂ when it
occurs in the second, and an unlimited entry stays in both. The rule fails
when a linear variable occurs in both or in neither (`lp` and `sok` of
examples/ExampleTools.v, with `lp_split`). The leaves then need no guess.

```
x : T   with every other entry of Δ spent
─────────────────────────────────────── ⇒Var
Φ ; Δ ⊢_F x ⇒ T ⊣ true

every entry of Δ spent
────────────────────── ⇒Unit
Φ ; Δ ⊢_F ∗ ⇒ ∗ ⊣ true
```

### 4.2  Functions

A λ in checking mode needs no annotation. In synthesis mode it carries its
arrow. In both the body runs under a fresh frame variable φ with the one
hypothesis u ≺ φ, and the lower point is checked against the captured heads.

```
φ fresh    Φ, u ≺ φ ; Δ, x : T ⊢_{{φ}} t ⇐ U ⊣ 𝒞
──────────────────────────────────────────────────── ⇐Abs
Φ ; Δ ⊢_F λx.t ⇐ T ⊸^u_ℓ U ⊣ ℓ ≼_{bot(Δ)} heads(Δ) ∧ 𝒞

φ fresh    Φ, u ≺ φ ; Δ, x : T ⊢_{{φ}} t ⇒ U ⊣ 𝒞
──────────────────────────────────────────────────── ⇒Abs (annotated)
Φ ; Δ ⊢_F (λx:T.t)^u_ℓ ⇒ T ⊸^u_ℓ U ⊣ ℓ ≼_{bot(Δ)} heads(Δ) ∧ 𝒞
```

Application synthesizes the function, checks the argument against the domain,
and gates the upper point against the ambient future. The argument's future is
F plus the lower point of the function, the function's future is F plus the
heads of what the argument uses, as in E-App.

```
Δ = Δ₁ ⊎ Δ₂ by occurrence
Φ ; Δ₁ ⊢_{F ∪ heads(Δ₂)} t₁ ⇒ T ⊸^u_ℓ U ⊣ 𝒞₁
Φ ; Δ₂ ⊢_{F ∪ {ℓ}} t₂ ⇐ T ⊣ 𝒞₂
──────────────────────────────────────────────── ⇒App
Φ ; Δ ⊢_F t₁ t₂ ⇒ U ⊣ 𝒞₁ ∧ 𝒞₂ ∧ gate(Φ, u, F)
```

gate(Φ, u, F) is the resolution of u ≺ F of Section 3. An absent u gives
true.

Checking is subsumption by points. A term in checking mode synthesizes and the
two types are matched (Section 4.3).

```
Φ ; Δ ⊢_F t ⇒ T′ ⊣ 𝒞    T′ ≈? T ⊣ 𝒞′
─────────────────────────────────────── ⇐Sub
Φ ; Δ ⊢_F t ⇐ T ⊣ 𝒞 ∧ 𝒞′
```

⇐Abs takes priority over ⇐Sub for a λ. Every other introduction form in
checking position goes through ⇐Sub, except injections (Section 4.4).

### 4.3  Matching and the one conversion

T′ ≈? T ⊣ 𝒞′ matches two types structurally and emits x ≡ y at every pair of
points, both for channels S@x against S@y and for the bounds of arrows. Session
types must be syntactically equal. Boxes and existentials must be syntactically
equal as well, bound points included, which is what `hsteq` asks of them. The
match fails otherwise. [derived] A successful match with its atoms satisfied
gives `hsteq Ψ T′ T`, the premise of E-Conv (Soundness.v, `tmatch_sound`).

The algorithm performs exactly one other conversion. A constant applied to a
channel reads the session type through its head normal form unr(S), which is
the function `hd` of types/Types.v. [known] unr(S) is bisimilar to S for every
S, so the conversion is an instance of E-Conv with ≈ (Soundness.v,
`seq_unfoldS`). This is where Skip, ; and μ are unrolled, and the only place.

### 4.4  Constants

Constants are constrained schemes (sharp edges 147). The algorithm never
synthesizes a bare constant. An application k t synthesizes t first and reads
the instance of the scheme off the argument's type. This reverses the order of
⇒App, and it is the reason the argument is synthesized and not checked. Each
constant has one rule. The future for the argument is F, because every
constant has an absent lower point. The gate is on the point of the channel.

```
Φ ; Δ ⊢_F t ⇒ (?P;S)@x ⊣ 𝒞    unr at x read by hd    P = ∃ιs.T
─────────────────────────────────────────────────────────────────── ⇒Recv
Φ ; Δ ⊢_F recv t ⇒ P[x] ⊗ S@(x+1) ⊣ 𝒞 ∧ gate(Φ, x, F)

Φ ; Δ ⊢_F t ⇒ V ⊗ (!P;S)@x ⊣ 𝒞    V ≈? P[x] ⊣ 𝒞′    P[x] without the ⊥ flag
──────────────────────────────────────────────────────────────────────────── ⇒Send
Φ ; Δ ⊢_F send t ⇒ S@(x+1) ⊣ 𝒞 ∧ 𝒞′ ∧ x ≺ heads(P[x]) ∧ gate(Φ, x, F)

Φ ; Δ ⊢_F t ⇒ Close@x ⊣ 𝒞
──────────────────────────────────────── ⇒Close
Φ ; Δ ⊢_F close t ⇒ ∗ ⊣ 𝒞 ∧ gate(Φ, x, F)

Φ ; Δ ⊢_F t ⇒ ⊕(S₁, S₂)@x ⊣ 𝒞
───────────────────────────────────────────────────────── ⇒Selectᵢ
Φ ; Δ ⊢_F selectᵢ t ⇒ Sᵢ@x[i] ⊣ 𝒞 ∧ x ≺ x[i] ∧ gate(Φ, x, F)

Φ ; Δ ⊢_F t ⇒ &(S₁, S₂)@x ⊣ 𝒞
──────────────────────────────────────────────────────────────────────────── ⇒Branch
Φ ; Δ ⊢_F branch t ⇒ S₁@x[0] + S₂@x[1] ⊣ 𝒞 ∧ x ≺ x[0] ∧ x ≺ x[1] ∧ gate(Φ, x, F)

Φ ; Δ ⊢_F t ⇒ S@x ⊗ S′@y ⊣ 𝒞    S′ = dual S
──────────────────────────────────────────── ⇒Link
Φ ; Δ ⊢_F link t ⇒ ∗ ⊣ 𝒞 ∧ x ≡ y

Φ ; Δ ⊢_F t ⇒ ∗ ⊸^u_ℓ ∗ ⊣ 𝒞
────────────────────────────── ⇒Spawn
Φ ; Δ ⊢_F spawn t ⇒ ∗ ⊣ 𝒞
```

In ⇒Send the sender's payload V is matched against P[x], the payload at the
payload points of x. The sender's channels therefore have to sit at points
aliased to x[j], and the match emits exactly those aliases. This is the
"sender aliases d to (c,k)[1]" of the spec, as an output. In ⇒Recv and ⇒Send
the payload type must have no free point variable beyond its ιs (kscoped),
a syntactic check.

Pairs, lets and sums follow the declarative rules with the occurrence split.
Injections are checked against the sum, or carry the other arm in synthesis
mode. Case synthesizes the scrutinee, checks both branches against the
expected type, or synthesizes both and matches the second against the first.

```
Δ = Δ₁ ⊎ Δ₂ by occurrence
Φ ; Δ₁ ⊢_{F ∪ heads(Δ₂)} t₁ ⇒ T ⊣ 𝒞₁    Φ ; Δ₂ ⊢_{F ∪ heads(T)} t₂ ⇒ U ⊣ 𝒞₂
──────────────────────────────────────────────────────────────────────────── ⇒Pair
Φ ; Δ ⊢_F ⟨t₁, t₂⟩ ⇒ T ⊗ U ⊣ 𝒞₁ ∧ 𝒞₂

Δ = Δ₁ ⊎ Δ₂    Φ ; Δ₁ ⊢_{F ∪ heads(Δ₂)} t₁ ⇒ T₁ ⊗ T₂ ⊣ 𝒞₁    Φ ; Δ₂, x : T₁, y : T₂ ⊢_F t₂ ⇒ T ⊣ 𝒞₂
──────────────────────────────────────────────────────────────────────────────────────── ⇒LetPair
Φ ; Δ ⊢_F let (x, y) = t₁ in t₂ ⇒ T ⊣ 𝒞₁ ∧ 𝒞₂

Δ = Δ₁ ⊎ Δ₂    Φ ; Δ₁ ⊢_{F ∪ heads(Δ₂)} t ⇒ T₁ + T₂ ⊣ 𝒞
Φ ; Δ₂, x : T₁ ⊢_F t₁ ⇐ T ⊣ 𝒞₁    Φ ; Δ₂, x : T₂ ⊢_F t₂ ⇐ T ⊣ 𝒞₂
────────────────────────────────────────────────────────────── ⇐Case
Φ ; Δ ⊢_F case t of … ⇐ T ⊣ 𝒞 ∧ 𝒞₁ ∧ 𝒞₂
```

### 4.5  new and spawn, the two places with unknowns

new creates a fresh point and has no witness. Its declarative premise is a
creation constraint C over the context (sharp edges 105). The algorithm takes
C as an annotation on the let that opens the pair, or infers it (Section 7).
The body runs under the hypothesis (C, ι) with every outer context shifted
past ι, as E-Open does, and its type must not mention ι.

```
Φ↑ ; Δ↑, a : S@ι, b : dual S@ι ⊢_{F↑} t ⇒ T↑ ⊣ 𝒞    ι ∉ T
────────────────────────────────────────────────────────────────── ⇒New
Φ ; Δ ⊢_F let (a, b) = new^{S,C} ∗ in t ⇒ T ⊣ cc(C) ∧ known(env C) ∧ ∃ι:C. 𝒞
```

spawn takes a thunk ∗ ⊸^u_ℓ ∗ at any u and ℓ. The thunk is checked against
∗ ⊸^α_β ∗ with two fresh metavariables. ⇐Abs then emits β ≼ heads(Δ) for the
captured heads and runs the body under α ≺ φ. Every gate inside the body
resolves to x ≼ α for its blocking point x. So α is bounded below by every
point the thunk blocks at and β above by every head it captures. Section 7
says how a solution picks them.

The future of the body of a spawned thunk is {φ} and nothing else, as the
spec says. The caller's future F does not enter the thunk, which is what lets
a spawned thread block at points the spawner never waits for.

## 5  What is standard and what is specific

Standard, and taken over without change.

- The mode discipline is the one of bidirectional typing [known]: introduction
  forms are checked, elimination forms synthesize, a λ needs an annotation only
  in synthesis position, and checking falls back to synthesis plus subsumption.
  In the terminology of Dunfield and Krishnaswami's survey of bidirectional
  typing this is the Pfenning recipe with a subsumption rule [uncited, verify].
- Linear environments are split by occurrence, the standard way to make a
  linear type system algorithmic without input and output contexts. The
  occurrence check is the one `lp` and `sok` already implement for the
  examples.
- The upper point is a latent effect on the arrow and the future is an ambient
  effect that flows down. That is the shape of a type-and-effect system
  [known], with the latent effect synthesized and the ambient effect inherited.
- The lower point is a condition on what a closure captures, checked at the
  λ. That is the shape of a coeffect, or of a capture rule in a system with
  regions or lifetimes [known as a shape, uncited].
- A constant with implicit parameters is instantiated by matching its scheme
  against the synthesized argument type, first-order matching with the points
  as the unknowns.

Specific to this system.

- Effects are points of a partial order that the program itself constrains,
  and comparison of effects is entailment in a fact theory with program order
  and two congruences. A lattice join never appears. In an effect system the
  effect of an application is the join of the effects of its parts. Here the
  future of the function is the caller's future plus the heads the argument
  still holds, and the future of the argument is the caller's future plus the
  lower point of the function. Both are unions of point sets, not joins in the
  order.
- The frame variable φ is a sort of its own (sharp edges 146). A gate against
  φ is resolved at generation time into u ≼ u′ for the one hypothesis u′ ≺ φ.
  No effect system has this device, and its correctness is the one-hypothesis
  shape of Φ.
- The ≡ atoms are not unification problems but congruence closure with
  potentials. x+k ≡ y+m identifies the names of x and y up to the integer
  potential m−k, and x ≡ y forces x[j] ≡ y[j] for every j. Solving them is
  union-find on names carrying an offset, with congruence on payload names
  (egg-smt-demo.md, stage 1). Plain first-order unification would not identify
  (c,2) with (d,5) at every later offset.
- The ⊥ flag of a future is a third value next to "a frame variable" and
  "none". Under it no gate can pass, which the resolution renders as false.
- new has no witness. Its unknown is a whole constraint, and the inference of
  Section 7 chooses it from the atoms of the body. Existential introduction in
  a bidirectional system otherwise infers a witness term by matching.

## 6  Choice and context-free session types

Choice is in the core above (⇒Selectᵢ, ⇒Branch). The two facts x ≺ x[i] a
choice owes are atoms like the facts of send, and the branch arms are a sum
that ⇐Case dispatches with the two channels at the payload points x[0] and
x[1]. No further rule is needed.

Context-free session types need three more things.

- Head normal forms. `hd` already unrolls Skip and ; and μ, so ⇒Recv and the
  other constant rules read S;S′ and μX.S without a rule of their own.
  Bisimilarity between two syntactically different session types is not
  decided by the matching of Section 4.3. A program that returns a channel at
  type α;Skip where (α;Skip);β is expected fails the match. The repair is a
  decision procedure for ≈ in place of syntactic equality in `tmatch`, and
  [known] bisimilarity of context-free session types is decidable.
- Boxes with session variables and existential results. A segment function
  such as drain or treeSum (examples/cfst) is a box □(∀κ ζ β. C. …) whose
  body returns ∃κ′≽κ. C′. β@κ′. The box is an annotation. force instantiates
  the ιs by matching the argument against the domain, as for the other
  constants, and the session variable β by matching the session type of the
  argument against S;β, which is matching with one variable at the tail of a
  sequence and succeeds when the argument's session type is syntactically
  S;s for some s. The instance of C is then an atom cᶜ(C[xs/ιs]) whose
  satisfaction is `bcs_hold`. pack is inferred by matching the synthesized type
  against T[xs/ιs] for the witnesses xs and emitting the lower-bound atom
  ℓ ≼ heads(T[xs/ιs]) and the instance of C′. open is the rule ⇒New without
  cc, applied at a variable whose type is an existential, the body under the
  hypothesis (C′, ιs).
- Ceilings over walks. The constraints of the segment functions are infinite
  and regular, κ·w ≺ ζ and κ·w ≺ (κ·w)[i] for every walk w ∈ (+1 | [0] | [1])*.
  Inside the body the atoms mention κ·w for concrete short walks only, and the
  recursive force asks C at κ·w for a concrete w. Satisfaction of such an atom
  under the hypothesis C is membership of a word in a regular language. The
  decision procedure for the body's constraint under C is the entailment
  question of algorithmic-decidable.md, and that document says how far it
  reaches.

Recursion needs no rule. A recursive call is a force of the box variable at
an instance, and the atom cᶜ(C[xs/ιs]) is discharged by the body's own
hypothesis when C[xs/ιs] ⊆ C. For the request and reply box that is the shift
by one, for drain it is the step along a walk. The algorithm emits the atom
and the decision procedure checks the containment.

## 7  Inference of the unknowns in the finite fragment

A program without boxes generates finitely many atoms, each over the point
variables of the enclosing binders, the top-level variables of C₀, and the
metavariables of its spawns. The unknowns are the metavariables and the
creation constraints of the news. The following procedure chooses them.

1. Generate 𝒞 with every new annotated by the placeholder C = ?, and read the
   atom tree as one flat set 𝒜 of atoms together with the binder order of the
   point variables.
2. Solve the ≡ atoms by union-find on names with integer potentials and
   congruence on payload names. A merge of a name with itself at a nonzero
   potential is a cycle through program order, and the program is rejected.
3. Instantiate the metavariables. β of a spawn thunk needs β ≼ h for every
   captured head h. Pick β as one captured head when all captured heads are
   related by the facts so far, else fail. The declarative rule allows an
   absent ℓ only when nothing is captured. α of a spawn thunk needs x ≼ α for
   every blocking point x of the thunk. Pick α as one of those points when
   they are related, else introduce a fresh top-level variable α into the
   binder of C₀ with the atoms x ≺ α. [guess] The second choice loses no
   program of theories/examples. What would falsify it is an example whose
   spawned thunk blocks at two unrelated points and whose typing needs the
   thunk's upper point below some other point.
4. Saturate. Close 𝒜 under the congruences, program order and transitivity
   with the solved aliases. Call the closure 𝒢. If 𝒢 contains x ≺ x, reject.
5. Slice. For every bound point variable ι, let C_ι be the facts of 𝒢 whose
   innermost root is ι, where the innermost root of a fact is the most recently
   bound root among the roots of its two points. The top-level slice is C₀.
6. Check. Run the algorithm again with the slices as annotations and decide 𝒞
   in the context [(C₀, ιs)].

[derived] Step 6 succeeds whenever step 4 does not reject. Every ≺ and ≡ atom
of 𝒜 is a fact of its slice or follows from the slices in scope by the closure
rules. Every slice C_ι is a creation constraint over the slices outside it.
Acyclicity holds because Γ_ι + C_ι is a subset of 𝒢 and 𝒢 has no cycle.
Conservativity holds because a fact between two points with roots other than ι derivable from Γ_ι + C_ι is a
fact of 𝒢 between points in scope at ι, so it lies in the slice of its
innermost root, which is outside ι, and that slice is part of Γ_ι. The known
atoms hold because every root in scope is an instance point of a hypothesis.

Step 5 is what sharp edges 144 does by hand. BranchOrder.v creates c with
ι[1] ≺ ι[0] because d's constraint derives it, and the slice of c contains
exactly that fact.

Boxes fall outside this procedure. Their constraints are annotations, and the
inference heuristic C = ⋃ₖ C₀[σᵏ(ιs)/ιs] of algorithmic.md is not run here.

## 8  Soundness

Theorem (soundness of synthesis). Let Φ ; Δ ⊢_F t ⇒ T ⊣ 𝒞 with every frame
variable of Φ below the counter, and let Ψ be a hypothesis context in which 𝒞
holds. Then Γ ; Δ ⊢_F t : T is derivable in `styped` with Γ = (Ψ, Φ).

The proof is by induction on t. Each rule of Section 4 is the declarative rule
of the same name with the guesses filled in. The occurrence split is a
`lenv_split`, the gate atoms give `hub_below_s`, the lower-bound atom gives
`hlb_below_hb`, a successful match gives `hsteq` and hence E-Conv, the head
normal form gives E-Conv with ≈, and the atoms of a constant give its scheme
instance through `konst_ty`. ⇒New is E-LetPair, E-Pair, E-Const at new,
E-Let*, E-Open and E-LetPair, the derivation of `t_new_open` of
static/Typing.v transported to `styped`.

Corollary (deadlock freedom). A closed program accepted by the algorithm under
C₀, whose constraint holds in [(C₀, ιs)] and whose C₀ is a creation constraint
against the empty context, is deadlock free, by `soundness_source`.

Both are mechanized for the fragment of Section 9 (`synth_sound` and
`synth_deadlock_free` in theories/algorithmic/Soundness.v).

The checking judgment is sound by ⇐Sub and ⇐Abs. ⇐Sub is E-Conv on the
synthesized type. ⇐Abs is E-Abs with the bounds taken from the expected type,
the same derivation as ⇒Abs. [derived, not mechanized] The mechanization has
the synthesis judgment only.

## 9  The mechanized fragment

theories/algorithmic/Algorithmic.v defines `synth n Φ Δ F a`, a function on
annotated terms `aexpr` with an erasure to `expr`. It covers ⇒Var, ⇒Unit, ⇒Abs
with the arrow annotated, ⇒App, the eight constant rules, ⇒Pair, ⇒LetUnit,
⇒LetPair, injections with the other arm annotated, case by synthesis of both
branches with a match, and ⇒New with S and C annotated. The counter n is the
next frame variable. The constraint type `constr` is the language of Section 3
without metavariables, and `csat` is satisfaction in a hypothesis context.

Differences from Section 4.

- Synthesis only. A λ carries its bounds and argument type. The checking mode
  is replaced by synthesis followed by `tmatch` at every position where the
  declarative rule compares two types.
- No metavariables. The spawn thunk's bounds come from its λ annotation. The
  inference of Section 7 is a front end that produces the annotations.
- No boxes, no force, no pack and open beyond the one of new, no bare
  constants, no session variables.
- Session types are compared by syntactic equality after `hd`.

theories/algorithmic/Soundness.v proves `synth_sound` and
`synth_deadlock_free`. The report lists the result of `Print Assumptions`.

## 10  Where annotations stay

- □(∀ιs αs. C. ∗ ⊸^u T). The quantified points, the session variables and the
  constraint are annotations. C is the invariant of a recursion and the body
  cannot derive it. force needs no annotation.
- ∃^ℓ ιs. C. T at a pack. The witnesses are inferred by matching, the lower
  bound ℓ is checked. The type itself is an annotation, because a value does
  not say which of its points are to be abstracted.
- λ in synthesis position, and inj in synthesis position.
- new. The creation constraint is inferred in the finite fragment (Section 7)
  and annotated otherwise.
- Nothing else. In particular recv, send, close, select, branch, link and
  spawn carry no annotation, and the points of every channel are determined by
  the program.
