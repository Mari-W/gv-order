# Order-based GV♯: specification (state of 2026-10-29)

This file is the current design. It supersedes every earlier order design
(the old `orders` branch, `orders.lagda`, `orders-examples.txt`,
`paper/orders-plan.pdf`). Notation follows the paper (`paper/2-calculus.tex`,
`paper/3-logical-rel.tex`, `paper/4-extensions.tex`). Tags: `[new]`,
`[changed]`, `[removed]` relative to the paper.

The frame F is an input parameter of E. F = ∅ is exactly the paper's E. It is
part of E (not a separate relation) so that E and the frame condition use the
same world extension at every `new`.

Worlds speak about points only, never about channel names (decision N, 2026-10-29).
Every environment entry carries the point of its channel's current instant,
c : S@x. Renaming channels therefore never touches a world, link substitutes as
in the paper, and the paper's renaming and junk lemmas hold with the world fixed.

## 1  Syntax

```
k  ::= new | spawn | recv | send | close | link | force                    [changed] fork removed
v  ::= ∗ | k | c | λx.t | ⟨v, v⟩ | inj₁ v | inj₂ v | !(x = t)
t  ::= x | v | t t | ⟨t, t⟩ | inj₁ t | inj₂ t | let () = t in t | let (x, y) = t in t
     | case t of inj₁ x ⇒ t | inj₂ x ⇒ t
𝒦  ::= □ | 𝒦 t | v 𝒦 | ⟨𝒦, t⟩ | ⟨v, 𝒦⟩ | injᵢ 𝒦 | let () = 𝒦 in t | let (x, y) = 𝒦 in t | case 𝒦 of …

σ  ::= c?v | c!v | c! | c↔d                                             session labels
λ  ::= β | σ | (νc) | ⇑v                                                [changed] term labels
fc(β) = fc((νc)) = fc(⇑v) = ∅    fc(c?v) = fc(c!v) = fc(c!) = {c}    fc(c↔d) = {c, d}
sent(c!v) = fchans(v),  otherwise ∅
```

Both ends of a channel keep one name (`chan := string` stays).

## 2  Term LTS

```
T-Act-App       (λx.t) v                   —β→      t[v/x]
T-Act-Let*      let () = ∗ in t            —β→      t
T-Act-LetPair   let (x,y) = ⟨w,v⟩ in t     —β→      t[w/x][v/y]
T-Act-Case      case injᵢ v of … xᵢ ⇒ tᵢ   —β→      tᵢ[v/xᵢ]
T-Act-Exp       force !(x = t)             —β→      t[!(x = t)/x]
T-Act-New       new ∗                      —(νc)→   ⟨c, c⟩                    [new]
T-Act-Spawn     spawn v                    —⇑v→     ∗                         [new]
T-Act-Recv      recv c                     —c?v→    ⟨v, c⟩
T-Act-Send      send ⟨v, c⟩                —c!v→    c
T-Act-Close     close c                    —c!→     ∗
T-Act-Link      link ⟨c, d⟩                —c↔d→    ∗            (c = d allowed)
T-Act-Ctx       t —λ→ t′   ⇒   𝒦[t] —λ→ 𝒦[t′]
```

## 3  Process LTS   p = (C, E),  π ::= τ | σ

```
P-Act-New       c fresh    t —(νc)→ t′      (C, E ⊎ {t}) —τ→ (C ⊍ {c}, E ⊎ {t′})        [new]
P-Act-Spawn     t —⇑v→ t′                   (C, E ⊎ {t}) —τ→ (C, E ⊎ {t′, v ∗})          [new]
P-Act-Beta      t —β→ t′                    (C, E ⊎ {t}) —τ→ (C, E ⊎ {t′})
P-Act-Msg       t —c!v→ t′   u —c?v→ u′     (C, E ⊎ {t, u}) —τ→ (C, E ⊎ {t′, u′})
P-Act-Close     t —c!→ t′    u —c!→ u′      (C ⊍ {c}, E ⊎ {t, u}) —τ→ (C, E ⊎ {t′, u′})
P-Act-Link      t —c↔d→ t′                  (C ⊍ {c}, E ⊎ {t}) —τ→ (C, (E ⊎ {t′})[d/c])      unchanged
P-Act-Session   t —σ→ t′   fc(σ) # C        (C, E ⊎ {t}) —σ→ (C ∖ sent(σ), E ⊎ {t′})      unchanged
                                                                   [removed] P-Act-Fork
```

Link substitutes in the whole soup, as in the paper. With c = d it releases c. Worlds
mention no channel names, so the substitution never has to move a fact. A forwarder
encoding was tried and dropped. Under forwarders link ⟨a, b⟩ ∥ link ⟨b, a⟩ over a
P-Connect cut {a, b} deadlocks, and under substitution it terminates (sharp edges 35 to 37).

With multi-channel P-Connect (cycles) a channel can travel back to the holder
of its other end ("migration"). The paper never meets this: with
single-channel P-Connect (a tree) and the extrusion split, a received
channel's other end is never inside the receiver. The LTS stays as in the
paper; the relation handles migration in Q-Recv (§7) by stating the
continuation for the process with the returning channels already restricted,
so process-level Σ stays a plain map with one end per channel.

```
terminated, safe, deadlock free        unchanged
```

## 4  Types and environments   [changed]

```
T, U ::= ∗ | T ⊗ U | T + U | T ⊸^u_ℓ U | S@ι | □(∀ιs. C.^u_Σ T)    term types (u may mention ιs; sharp edges 52)
C    ::= {x₁ ≺ y₁, …, xₖ ≺ yₖ}  constraint of a box, a finite set of ≺ facts over ιs and   [new, 58]
                          outer points. No ≡ facts. C = ∅ is the box of 52. □(∀ιs.^u T) abbreviates C = ∅.
Σ    ::= {σ₁, …, σₘ}      steps of a box, each a substitution of ιs by points over ιs        [new, 61]
                          (ι ↦ ι+1, ι′ ↦ ι[0]+1). C holds at xs when C[w(xs)/ιs] holds for every
                          word w over Σ, the empty word giving xs. Σ = ∅ is the box of 58.
u    ::= ι | ⊥            upper point: the call blocks at most at u     (⊥: never blocks)
ℓ    ::= ι | ⊤            lower point: the closure holds only above ℓ   (⊤: holds nothing)
                          (no ⊤ for u: every function has a known upper point, a function that may
                           block anywhere gets a point variable)
S    ::= ?P.S | !P.S | Close | μX.S | X                                 session types, unannotated
P    ::= ∃ιs. T           payload, all points of T bound                sugar: !(S₁ ⊗ S₂).S binds them implicitly
ι    ::= (p, b)           a point: a name with an offset
p    ::= a | ι-variable | p[b][i]     point constant, bound point variable, slot "the i-th point carried at (p,b)"
x[i] ≔ (p[b][i], 0)  for x = (p, b)     the i-th point carried at instant x, as a point
         Neither types nor worlds mention channel names (decisions F2 and N). Channels occur only
         as keys of environments. Renaming channels changes no type and no world.               [changed]

Σ    ::= · | c : S@x | Σ, Σ                       process level, a finite map,  x a ground point,
                                                  c's current instant; each action on c moves x to x+1
Θ    ::= Σ | Θ, c : S@x, c : S′@x                  term level, may hold both ends,  S ⊥ S′
Δ    ::= · | x : T | Δ, Δ
prim ∗,  prim T ⊗ U,  prim T + U,  prim □T if prim T     (as in the paper)

heads(∗) = heads(□σ) = ∅      heads(S@ι) = {ι}      heads(T ⊸^u_ℓ U) = {ℓ} ∖ {⊤}
heads(T ⊗ U) = heads(T + U) = heads(T) ∪ heads(U)
heads(c : S@x) = {x}         heads(Σ, Δ) = ⋃ heads of the entries
```

- ∀ appears only directly under □ (never on linear functions, never inside session types).
- Points are the only names in the order. Facts may place them anywhere. A value c of type S@ι needs ι ≡ the point of c's entry.

## 5  Worlds   [new]

```
carrier     instants (p, b),  p a point constant or a slot of one. No channel names.   [changed]
W = (≡, ≺)  ≡ equivalence (aliases),  ≺ strict partial order on ≡-classes
            ⊇ program order (p, b) ≺ (p, b+1) for every name p
successor congruence   x ≡ y  ⇒  x+1 ≡ y+1     (aliased instants stay aliased; replaces the
                                                 separate alias notation p@a ≡ q@b)        [new]
slot congruence        x ≡ y  ⇒  x[i] ≡ y[i]    (equal instants carry the same message)     [new]
x ≼ y       x ≺ y or x ≡ y
F ≺ G       every element of F is ≺ every element of G        (frames, ⊥ and ⊤ as expected)

W ⊑ W′      ≡ ⊆ ≡′,  ≺ ⊆ ≺′,  W′ strict                        (Kripke order)
W ⊑ₒ W′     W ⊑ W′ and W′ adds nothing between old instants    (only at new)
W₁ ⊔ W₂     (≡₁ ∪ ≡₂)* with (≺₁ ∪ ≺₂)⁺ on the classes
```

## 6  Readiness and frames   [new]

```
entries(Θ)   one entry per end:  c : S@x  (twice for a channel whose both ends Θ holds)
offered(x)   = the entries selected by the labels of x's transitions     x a term or a process
               c!v selects the entry of c whose type unfolds to !…,  c?v the one with ?…,
               c! either Close entry,  c↔d the entries of c and d
stable(t)    = no t —λ→ t′ with λ ∈ {β, (νc), ⇑v}        stable(p) = no p —τ→ p′

ready_W(Θ, x) ≔ stable(x) ⇒
                  (offered(x) = ∅  ⇒  x is a value / p is terminated)
                ∧ ∀e ∈ entries(Θ) ∖ offered(x).  ∃o ∈ offered(x).  head(o) ≺_W head(e)

frame_W(t, F) ≔ stable(t) ⇒ ∀o ∈ offered(t).  {head(o)} ≺_W F
```

ready counts entries, not names: a thread holding both ends of c and blocking
on one of them must hold the other entry not offered, so it needs
head(c) ≺ head(c), which fails. Two threads holding one end each are both
offered and can synchronize, so that state is not stable.

## 7  Logical relation   V^W_n⟦Σ ⊢ T⟧,  E^W_n⟦Θ ⊢ T ≺ F⟧,  P^W_n⟦Σ ⊢ T⟧

```
V-Unit    ∗ ∈ V^W_n⟦· ⊢ ∗⟧
V-Chan    c ∈ V^W_n⟦c : S@x ⊢ S′@y⟧            if S ≈ S′ and x ≡_W y                     [changed]
V-Const   k ∈ V^W_n⟦· ⊢ T⟧                     if k : T₀ (instance of its signature) and T₀ ≈_W T
          (≈_W: ≈ with ground points compared up to ≡_W; needed for Type point conversion)   [changed]
          (new's ι must be known to W, its root in the support, so that O-New can alias
           the created point to it; sharp edges 49)                                          [new]
V-Pair    v₁ ∈ V^W_n⟦Σ₁ ⊢ T⟧   v₂ ∈ V^W_n⟦Σ₂ ⊢ U⟧   ⇒   ⟨v₁, v₂⟩ ∈ V^W_n⟦Σ₁, Σ₂ ⊢ T ⊗ U⟧
V-Inj     v ∈ V^W_n⟦Σ ⊢ Tᵢ⟧   ⇒   injᵢ v ∈ V^W_n⟦Σ ⊢ T₁ + T₂⟧
V-Abs     fchans(t) = dom Σ        {ℓ} ≼_W heads(Σ)                                      [changed]
          ∀W′ ⊒ W, j < n, Σ′, v ∈ V^{W′}_j⟦Σ′ ⊢ T⟧, F with {u} ≺_{W′} F.
              t[v/x] ∈ E^{W′}_j⟦Σ, Σ′ ⊢ U ≺ F⟧
          ⇒   λx.t ∈ V^W_n⟦Σ ⊢ T ⊸^u_ℓ U⟧
V-Box     fchans(t) = ∅     ∀W′ ⊒ W, xs known to W′ with C at every Σ-word of xs in W′,
              F with {u[xs/ιs]} ≺_{W′} F.
              fix x.t ∈ E^{W′}_n⟦· ⊢ T[xs/ιs] ≺ F⟧
          ⇒   !(x = t) ∈ V^W_n⟦· ⊢ □(∀ιs. C.^u_Σ T)⟧                                  [changed, 52, 58, 61]
          (C[xs/ιs] in W′: every fact x ≺ y of C holds as x[xs/ιs] ≺_{W′} y[xs/ιs].
           Rocq: bcs_hold (w_lt W′) C xs and Forall (pt_known W′) xs, sharp edges 59, 61)
          (≈_W compares the constraints of two boxes fact by fact and step by step,
           points up to ≡_W)                                                              [new, 58, 61]
V-All     v ∈ V^W_n⟦Σ ⊢ ∀ιs. T⟧   ≔   ∀xs.  v ∈ V^W_n⟦Σ ⊢ T[xs/ιs]⟧                     [new]

payload at a slot      P[x] ≔ T[x[1], …, x[m] / ι₁, …, ιₘ]  for P = ∃ι₁ … ιₘ. T and c : S@x.     [changed]
                       A plain substitution, no quantifier on either side. The sender's channels
                       satisfy it up to ≡ (V-Chan), so the sender must have aliased them to the slots.
                       (Before decision N slots of channel instants could not occur in types, which
                       forced ∃xs at the sender and ∀xs at the receiver.)
names                  one sort, points. Worlds and environments use ground points (constants and their
                       slots). Static types also use bound point variables. (Replaces the two sorts of F2.)

E-Zero    t ∈ E^W_0⟦Θ ⊢ T ≺ F⟧
E-Stop    v ∈ V^W_{n+1}⟦Θ ⊢ T⟧   ⇒   v ∈ E^W_{n+1}⟦Θ ⊢ T ≺ F⟧
E-Step    ¬irred t    ready_W(Θ, t)    frame_W(t, F)                                      [changed]
          ∀λ, t′.  t —λ→ t′  ⇒  Θ ⊩ⁿ_W t —λ→ t′ : T ≺ F
          ⇒   t ∈ E^W_{n+1}⟦Θ ⊢ T ≺ F⟧

Giving steps keep the index (sharp edges 45)                                             [new]
          send, close and link are giving steps. Their obligations (O-Send, O-Close, O-Link,
          Q-Send, Q-Close, Q-Link, and Q-Tau for the τ of P-Act-Link) state the successor at
          n+1, the index of the step itself. β, new, spawn, receive and a synchronization
          (τ of P-Act-Session or P-Act-Close) cost one. E_{n+1} and P_{n+1} are least fixpoints over giving
          steps at fixed n+1, over E_n and P_n. Giving steps are well founded because each removes
          a send, close or link redex outside every λ, or a channel from C ∪ dom Σ.
          In the clauses below, read the continuation index of a giving step as n+1.
          The giving clause for the τ of P-Act-Link keeps the world (W′ = W), because a link
          creates no points. Rocq encodes E_{n+1} and P_{n+1} as inductive predicates (Eind, Pind)
          over the level-n relations, with induction principles Erel_S_ind and Prel_S_ind.

O-Beta    t′ ∈ E^W_n⟦Θ ⊢ T ≺ F⟧
O-New     ∃a ∉ names(W) ∪ points(Θ, T, F), S ⊥ S′, W′ ⊒ₒ W placing a.   t′ ∈ E^{W′}_n⟦Θ, c : S@(a,0), c : S′@(a,0) ⊢ T ≺ F⟧
          (the created channel name needs no condition, only its point is fresh)               [new]
O-Spawn   Θ = Θ₁, Θ₂     v ∈ V^W_{n+1}⟦Θ₁ ⊢ ∗ ⊸^u_ℓ ∗⟧     t′ ∈ E^W_n⟦Θ₂ ⊢ T ≺ F⟧       [new]
O-Send    Θ = Θ₁, Θ₂, c : (!P.S)@x     v ∈ V^W_{n+1}⟦Θ₂ ⊢ P[x]⟧                          [changed]
          t′ ∈ E^W_n⟦Θ₁, c : S@(x+1) ⊢ T ≺ F⟧
O-Recv    Θ = Θ₁, c : (?P.S)@x                                                           [changed]
          ∀W′ ⊒ W, j ≤ n, Σ₂, v ∈ V^{W′}_j⟦Σ₂ ⊢ P[x]⟧,  (Θ₁, c : S@(x+1)), Σ₂ defined.
              t′ ∈ E^{W′}_j⟦(Θ₁, c : S@(x+1)), Σ₂ ⊢ T ≺ F⟧
          (the payload is composed with the continuation, so a returning end of c must be
           dual to it at an aliased point; sharp edges 43)
          (Θ may then hold both ends of a received channel; Θ₁, Σ₂ is defined when every
           overlap is a pair of dual ends at ≡_{W′} points. Every overlap condition of the
           relation reads ≡_W, never equality of points: sharp edges 40)
O-Close   Θ = Θ₁, c : Close@x      t′ ∈ E^W_n⟦Θ₁ ⊢ T ≺ F⟧
O-Link    Θ = Θ₁, c : S@x, d : S′@y    S ⊥ S′    x ≡_W y    t′ ∈ E^W_n⟦Θ₁ ⊢ T ≺ F⟧       [changed]
          (c = d allowed: a self-link, Θ holds both ends of c, both entries leave Θ.
           Matches P-Act-Link with c = d, which releases c. `link (new ∗)` is typable.)
                                                                [removed] O-Fork

P-Zero    p ∈ P^W_0⟦Σ ⊢ T⟧
P-Stop    v ∈ V^W_{n+1}⟦Σ ⊢ T⟧   ⇒   (∅, {v, ∗, …, ∗}) ∈ P^W_{n+1}⟦Σ ⊢ T⟧
P-Step    ¬irred p    ready_W(Σ, p)                                                       [changed]
          ∀π, p′.  p —π→ p′  ⇒  Σ ⊩ⁿ_W p —π→ p′ : T
          ⇒   p ∈ P^W_{n+1}⟦Σ ⊢ T⟧

Every clause is stated for the successor itself. Restricted channels carry no facts,
because worlds speak about points only, so the environment's world cannot pin anything on
them. Gone with decision N: the α-variant at a receive (E), the freshness of received
names, the name guard at new and the invisible-names condition of Q-Tau.

Q-Tau     p —τ→ p′    p′.1 # dom Σ  ⇒  ∃W′ ⊒ₒ W.   p′ ∈ P^{W′}_n⟦Σ ⊢ T⟧                    [changed]
          (W′ places the points N of channels the step creates, N # names(W) ∪ points(Σ, T).
           The paper's Q-Tau is W′ = W.)
Q-Recv    Σ = Σ₁, c : (?P.S)@x     p —c?v→ (C′, E′)                                       [changed]
          ∀W′ ⊒ W, j ≤ n, Σ₂ # p.1, v ∈ V^{W′}_j⟦Σ₂ ⊢ P[x]⟧,  Σ₂ dual to (Σ₁, c : S@(x+1)) on their overlap B.
              (C′ ∪ B, E′) ∈ P^{W′}_j⟦(Σ₁, c : S@(x+1)) ∖ B, Σ₂ ∖ B ⊢ T⟧
          (B = channels whose other end the receiver already holds. The obligation is stated
           for the successor with B restricted; the LTS itself does not restrict. If the carrier c
           itself is in B (an end of c was sent over c), its continuation entry leaves Σ as well.
           Σ₂ is a term-level environment: a payload may carry both ends of one channel; such a
           channel also belongs to B and is restricted in the continuation.
           The guard c ∉ dom Σ₂ of the paper is dropped (c may be in B).
           Lemma needed: restricting B only removes external steps on channels no environment holds.)
Q-Send    Σ = Σ₀, Σ_v, c : (!P.S)@x      dom Σ_e = fchans(v) ∩ C                          [changed]
          ∃Σ_e, Σ_e′ (points chosen by the obligation).
          v ∈ V^W_{n+1}⟦Σ_v, Σ_e′ ⊢ P[x]⟧      p′ ∈ P^W_n⟦Σ₀, Σ_e, c : S@(x+1) ⊢ T⟧
          Σ_e′ = ends of dom Σ_e that leave with v,   Σ_e = ends that stay
          (both ends of a restricted channel may leave with v; then it has no entry in Σ_e)

Obligations whose continuation environment cannot be formed (e.g. Θ already holds both
ends of c) fail; such a thread is never ready anyway.
Q-Close   Σ = Σ₁, c : Close@x      p′ ∈ P^W_n⟦Σ₁ ⊢ T⟧
Q-Link    c ≠ d    Σ = Σ₁, c : S@x, d : S′@y    S ⊥ S′    x ≡_W y    p′ ∈ P^W_n⟦Σ₁ ⊢ T⟧   [changed]
          (c = d cannot reach the interface: process-level Σ holds one end per channel)
                                    [removed] extrusion split 𝒯, T-Nil, T-Cons, Q-Twice
```

## 8  Semantic judgments

```
Θ; Δ ⊨^F_W t : T   ≔   ∀n, W′ ⊒ W, Θ′, γ ∈ G^{W′}_n⟦Θ′; Δ⟧, (Θ, Θ′) defined in W′.   tγ ∈ E^{W′}_n⟦Θ, Θ′ ⊢ T ≺ F⟧
                       (Θ, Θ′ composes, dual ends at ≡_{W′} points allowed: a bound value may hold
                        the other end of a channel of Θ; sharp edges 50)
Σ ⊨_W p : T        ≔   ∀n.  p ∈ P^W_n⟦Σ ⊢ T⟧
Θ; Δ ⊨_W t : T     ≔   Θ; Δ ⊨^∅_W t : T                  (the paper's judgement, plus ready)
```

## 9  Static typing   Θ; Δ ⊢^F_G t : T   [new parts]

```
G          finite set of fact schemas and alias schemas over points
W_G        the world G generates, required strict
           Num: total.   Fin: G finite.   Decided by Kosaraju–Sullivan plus free coordinates (§11)

new    : ∗ ⊸^⊥_⊤ S@ι ⊗ S′@ι                                  S ⊥ S′,  ι fresh
spawn  : (∗ ⊸^u_ℓ ∗) ⊸^⊥_⊤ ∗
send   : (P[ι] ⊗ (!P.S)@ι) ⊸^ι_⊤ S@(ι+1)                     {ι} ≺_G heads(P[ι])
recv   : (?P.S)@ι ⊸^ι_⊤ P[ι] ⊗ S@(ι+1)
close  : Close@ι ⊸^ι_⊤ ∗
link   : S@ι ⊗ S′@ι′ ⊸^ι_⊤ ∗                                  S ⊥ S′,  ι ≡_G ι′
force  : □(∀ιs. C.^u_Σ T) ⊸^{u[ιs′/ιs]}_⊤ T[ιs′/ιs]    C at every Σ-word of ιs′, ιs′ known   [changed, 52, 58, 61]
         (premises on the order and the support, as pt_known is for new: KTForce reads C in the
          order konst_ty is given and knownness in its predicate. V-Const reads ≺_W and pt_known W.
          The static system reads W ∪ Ψ and skn, sharp edges 61)
new    : as above, ι known. The static system reads ι known when W knows it or ι has the     [changed, 61]
         root of an instance point of a hypothesis in Ψ, so new may create a channel at a
         box's ιs (sharp edges 59)

E-Unit     ·; · ⊢^F ∗ : ∗
E-Const    k : T   ⇒   ·; · ⊢^F k : T
E-LVar     ·; x : T ⊢^F x : T
E-Ch       c : S@ι; · ⊢^F c : S@ι′       with ι′ ≡_G ι
E-Abs      Θ; Δ, x : T ⊢^{{μ}} t : U      μ fresh, only fact u ≺ μ      ℓ fresh, only facts {ℓ} ≼ heads(Θ, Δ)
           ⇒   Θ; Δ ⊢^F λx.t : T ⊸^u_ℓ U
E-App      Θ₁; Δ₁ ⊢^{F ∪ heads(Θ₂, Δ₂)} t₁ : T ⊸^u_ℓ U     Θ₂; Δ₂ ⊢^{F ∪ {ℓ}} t₂ : T     {u} ≺_G F
           ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊢^F t₁ t₂ : U
E-Pair     Θ₁; Δ₁ ⊢^{F ∪ heads(Θ₂, Δ₂)} t₁ : T     Θ₂; Δ₂ ⊢^{F ∪ heads(T)} t₂ : U
           ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊢^F ⟨t₁, t₂⟩ : T ⊗ U
E-Let*     Θ₁; Δ₁ ⊢^{F ∪ heads(Θ₂, Δ₂)} t₁ : ∗     Θ₂; Δ₂ ⊢^F t₂ : T
           ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊢^F let () = t₁ in t₂ : T
E-LetPair  Θ₁; Δ₁ ⊢^{F ∪ heads(Θ₂, Δ₂)} t₁ : T₁ ⊗ T₂     Θ₂; Δ₂, x : T₁, y : T₂ ⊢^F t₂ : T
           ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊢^F let (x, y) = t₁ in t₂ : T
E-Inj      Θ; Δ ⊢^F t : Tᵢ   ⇒   Θ; Δ ⊢^F injᵢ t : T₁ + T₂
E-Case     Θ₁; Δ₁ ⊢^{F ∪ heads(Θ₂, Δ₂)} t : T₁ + T₂     Θ₂; Δ₂, xᵢ : Tᵢ ⊢^F tᵢ : U  (i = 1, 2)
           ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊢^F case t of … : U
E-Exp      ·; □Δ, x : □(∀ιs. C.^u_Σ T) ⊢^{μ}_{Ψ, (C,ιs)} t : T   (μ fresh, only u ≺ μ)     G closed under the substitutions at recursive calls
           ⇒   ·; □Δ ⊢^F_Ψ !(x = t) : □(∀ιs. C.^u_Σ T)                                       [changed, 52, 58, 61]
           Ψ: the constraints of the enclosing boxes with their instances, hypotheses (C, xs).
           Every side condition x ≺ y of the static system is read in W ∪ Ψ: the closure of ≺_W
           and the facts of every (C, xs) at every Σ-word of xs, under ≡_W and transitivity
           (58, 61). A recursive call forces x at a step σᵢ(ιs) and gets C at every word of it
           from the body's own hypothesis (C, ιs), because those words are words of ιs. Any
           other instance asks C at all its words from W ∪ Ψ.
           ιs are point variables in the premise, typed once (57). E-Const at send and recv asks
           the payload ∃ιs.T to have no free point variable beyond ιs, the "all points of T bound" of §4 (57)
E-Weak, E-Contract, E-Conv      as in the paper, with ⊢^F

P-Term     prim T    Σ, Θ_B; · ⊢^∅ t : T    Θ_B = both ends of every channel in C₀, some points  [changed]
           ⇒   Σ ⊢_G (C₀, {t}) : T
P-Connect  Σ₁, Σ_C ⊢_G (C₁, E₁) : T    Σ₂, Σ_C′ ⊢_G (C₂, E₂) : ∗    Σ_C ⊥ Σ_C′ over C₀ (possibly ∅)
           ⇒   Σ₁, Σ₂ ⊢_G (C₁ ⊍ C₂ ⊍ C₀, E₁ ⊎ E₂) : T                                     [changed]
                                                      [removed] P-Independent, P-Res
```

## 10  Lemmas: LTS and worlds

```
Harmony                          p —τ→ p′  ⇔  p ⟶ p′                       unchanged
Internalizing communication      generalized to a cut C₀ (statement otherwise unchanged)          [changed]
Restriction of returning channels
                  in the P-Connect proof the composite's successor equals the receiving component's
                  successor with B restricted, because B already lies in the cut C₀            [new]
Internalizing a close            unchanged
Internalizing a link             unchanged (the paper's, world fixed)

Amalgamation      W₁, W₂ strict  ⇒  (W₁ ⊔ W₂ strict  ⇔  (W₁|_A ⊔ W₂|_A) strict),   A = points W₁ and W₂ share
Fresh extension   W₁ ⊑ₒ W₁′ placing points N,  N # names(W₂),  W₂ strict,  W₁ ⊔ W₂ strict
                  ⇒   W₁′ ⊔ W₂ strict
Monotonicity      W ⊑ W′  ⇒  V/E/P^W ⊆ V/E/P^{W′}      (needs world_wf W; expected for P without
                  restriction now, because no fact can mention a restricted channel)
Renaming channels the paper's Renaming.v and Junk.v, with the world fixed                       unchanged
Renaming points   a bijective renaming of point constants applied to the world, the environment
                  and the types preserves V, E and P (P-Connect's new case renames a component's
                  fresh point away from the other world)                                       [new]
Type point conversion  ι ≡_W ι′ ⇒ V/E/P with ι in a type ⇔ with ι′ in its place   [new]
                  (send and recv use it to move between P[x] and the sender's own points)
Entry conversion  x ≡_W y  ⇒  (t ∈ E^W_n⟦Θ, c : S@x ⊢ T ≺ F⟧ ⇔ t ∈ E^W_n⟦Θ, c : S@y ⊢ T ≺ F⟧),
                  likewise for P (P-Term's link case; uses slot congruence for payloads)       [new]
Frame weakening   F′ ⊆ F  ⇒  E^W_n⟦Θ ⊢ T ≺ F⟧ ⊆ E^W_n⟦Θ ⊢ T ≺ F′⟧
Prel_steps, Prel_safe            unchanged (the paper's)
```

## 11  Lemmas: compositionality (one per rule)

```
E-Unit      ·; · ⊨^F ∗ : ∗
E-Const     k : T   ⇒   ·; · ⊨^F k : T                      for new, spawn, send, recv, close, link, force
E-LVar      ·; x : T ⊨^F x : T
E-Ch        c : S@x; · ⊨^F c : S@ι        with ι ≡_W x
E-Abs       ∀F′ with {u} ≺ F′.  Θ; Δ, x : T ⊨^{F′} t : U       {ℓ} ≼ heads(Θ, Δ)
            fchans(t) = dom Θ      fv(t) = dom(Δ, x : T)
            ⇒   Θ; Δ ⊨^F λx.t : T ⊸^u_ℓ U
E-App       Θ₁; Δ₁ ⊨^{F ∪ heads(Θ₂, Δ₂)} t₁ : T ⊸^u_ℓ U     Θ₂; Δ₂ ⊨^{F ∪ {ℓ}} t₂ : T     {u} ≺ F
            ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊨^F t₁ t₂ : U
E-Pair      Θ₁; Δ₁ ⊨^{F ∪ heads(Θ₂, Δ₂)} t₁ : T     Θ₂; Δ₂ ⊨^{F ∪ heads(T)} t₂ : U
            ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊨^F ⟨t₁, t₂⟩ : T ⊗ U
E-Let*      Θ₁; Δ₁ ⊨^{F ∪ heads(Θ₂, Δ₂)} t₁ : ∗     Θ₂; Δ₂ ⊨^F t₂ : T
            ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊨^F let () = t₁ in t₂ : T
E-LetPair   Θ₁; Δ₁ ⊨^{F ∪ heads(Θ₂, Δ₂)} t₁ : T₁ ⊗ T₂     Θ₂; Δ₂, x : T₁, y : T₂ ⊨^F t₂ : T
            ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊨^F let (x, y) = t₁ in t₂ : T
E-Inj       Θ; Δ ⊨^F t : Tᵢ   ⇒   Θ; Δ ⊨^F injᵢ t : T₁ + T₂
E-Case      Θ₁; Δ₁ ⊨^{F ∪ heads(Θ₂, Δ₂)} t : T₁ + T₂     Θ₂; Δ₂, xᵢ : Tᵢ ⊨^F tᵢ : U
            ⇒   Θ₁, Θ₂; Δ₁, Δ₂ ⊨^F case t of … : U
E-Exp       ∀xs with C[xs/ιs], F′ with {u[xs/ιs]} ≺ F′.  ·; □Δ, x : □(∀ιs. C.^u T) ⊨^{F′} t : T[xs/ιs]
            fchans(t) = ∅     fv(t) ⊆ dom(□Δ, x)
            ⇒   ·; □Δ ⊨^F !(x = t) : □(∀ιs. C.^u T)                                      [changed, 52, 58]
E-Force     Θ; Δ ⊨^F t : □(∀ιs.^u T)    {u[xs/ιs]} ≺ F   ⇒   Θ; Δ ⊨^F force t : T[xs/ιs]
E-Weak      Θ; Δ ⊨^F t : U   ⇒   Θ; Δ, x : □T ⊨^F t : U
E-Contract  Θ; Δ, x : □T, y : □T ⊨^F t : U   ⇒   Θ; Δ, x : □T ⊨^F t[x/y] : U
E-Conv      Θ; Δ ⊨^F t : T,   T ≈ T′   ⇒   Θ; Δ ⊨^F t : T′
            Rocq: the elimination rules go through Erel_bind (Bind.v, sharp edges 48). The hole runs
            under frame F ∪ H, where every entry of the context's environment lies at or above H.
            The semantic condition behind H: the environment of v ∈ V⟦Θ ⊢ T⟧ lies at or above
            heads(T) (Vrel_heads_above, TermRules.v), and a grounding's environment at or above
            heads(Δ) (grounding_heads). Typing then needs nothing extra.
            Proved in TermRules.v: sem_typed_unit, sem_typed_konst, sem_typed_var, sem_typed_chan,
            sem_typed_lam (E-Abs; premise for every later world W₁ and F′ with {u} ≺_{W₁} F′),
            sem_typed_inj1/2, sem_typed_letu, sem_typed_letp, sem_typed_case, sem_typed_pair,
            sem_typed_wk, and E-App as sem_typed_app_gen from app_good, which Erel_app_noforce
            gives for every function value but force. E-Conv is sem_typed_teq (Convert.v).
            Proved in TermRules2.v (after 52): Erel_app_force, hence app_good_all and E-App for
            every function (sem_typed_app); E-Force (sem_typed_force, at an instance xs with
            {u[xs/ιs]} ≺_W F); E-Exp (sem_typed_box, premise for every later world, xs and F′
            with {u[xs/ιs]} ≺ F′, by induction on the index); E-Contract (sem_typed_contract,
            the two most recent bindings, t[x/y] = rename pred t).

P-Term      prim T,   Σ, Θ_B; · ⊨^∅_W t : T,   Θ_B both ends of C₀
            ⇒   Σ ⊨_W (C₀, {t}) : T
            proof: chain argument over C₀ inside one thread
            Rocq (sharp edges 47): induction on n, inside on the size of the thread. Proved as
            Prel_term (PTerm.v). Implicit side conditions made explicit there: W strict,
            dom Θ_B = C₀, Θ_B only both-ends entries, dual at ≡_W points, dom Σ # C₀.
P-Connect   prim T,   Σ₁, Σ_C ⊨_{W₁} (C₁, E₁) : T,   Σ₂, Σ_C′ ⊨_{W₂} (C₂, E₂) : ∗,
            Σ_C ⊥ Σ_C′ over C₀,   C₁ # dom Σ₂,   C₂ # dom Σ₁,   W₁ ⊔ W₂ strict
            ⇒   Σ₁, Σ₂ ⊨_{W₁ ⊔ W₂} (C₁ ⊍ C₂ ⊍ C₀, E₁ ⊎ E₂) : T
            proof: ready by the chain argument across C₀;  τ steps by the Internalizing lemmas,
                   a message instantiates Q-Recv with W₁ ⊔ W₂ (the sender's alias names the payload),
                   new by Fresh extension and Renaming points,  link by Internalizing a link and Entry conversion

            Rocq (sharp edges 46): induction on n, inside on the size of the composite's soup;
            both components in one world W ⊒ W₁, W₂ (monotonicity), one at T, the other at ∗.
            Proved as Prel_connect (Connect3.v). Implicit side conditions made explicit there:
            dom Σ_C = dom Σ_C′ = C₀, cut ends dual at ≡ of W₁ ⊔ W₂, W₁ and W₂ well formed,
            Σ₁, Σ₂, Σ_C pairwise disjoint as maps, C₁ # dom Σ₁, C₂ # dom Σ₂, C₁, C₂, C₀ disjoint.
            index (sharp edges 45, replaces the budget of plan A): components in P at n give the
            composite in P at n. A synchronization of the composite is a giving step of one component
            (free) and a receive or close of the other. A link of two cut channels fuses the other ends
            inside one component by Internalizing a link.
Internalizing a link (component level)
            prim T,  p ∈ P^W_n⟦Σ, c : S̄@x, d : S@y⟧,  x ≡_W y   ⇒   (C ∪ {d}, E[d/c]) ∈ P^W_n⟦Σ ⊢ T⟧
            proof: a synchronization on d of the fused process is c!v (free) then d?v of p, and a
            close on d is two closes of p (both free); induction on n, inside on the giving-step
            fixpoint of p; readiness by the chain argument (the two ends are never both offered in a
            stable fused process); prim T rules out a terminated p that returns the two ends.

P-Connectⁿ  (corollary, by induction on n using P-Connect; every partial amalgam is a subset of the full one)
            Σᵢ, Σ_Cᵢ ⊨_{Wᵢ} (Cᵢ, Eᵢ) : Tᵢ  (i = 1 … n),  exactly one Tᵢ = T, all others ∗,
            the Σ_Cᵢ together hold both ends of every channel in C₀, each end once, dual,
            W₁ ⊔ … ⊔ Wₙ strict
            ⇒   Σ₁, …, Σₙ ⊨_{W₁ ⊔ … ⊔ Wₙ} (C₁ ⊍ … ⊍ Cₙ ⊍ C₀, E₁ ⊎ … ⊎ Eₙ) : T
            Rocq (sharp edges 55): Prel_connect_n (ConnectN.v). The components move to the
            full amalgam first (monotonicity), then P-Connect folds at that one world
            (Prel_connect_list). The cut ends are dual at ≡ of the full amalgam.
```

## 12  Main results

```
Fundamental     Θ; Δ ⊢^F_G t : T   ⇒   Θ; Δ ⊨^F_{W_G} t : T
                Σ ⊢_G p : T        ⇒   Σ ⊨_{W_G} p : T
Adequacy        · ⊨_W p : T   ⇒   p deadlock free         (the paper's proof)
Soundness       · ⊢_G p : T,  W_G strict   ⇒   p deadlock free
Decidability    W_G strict is decidable:  Kosaraju–Sullivan for edges with offsets,
                plus our lemma for schemas with a variable on one side only (free coordinates)
                (paper-level, not mechanized in this round)
```

Rocq (Static.v, sharp edges 53, 56): typed W Φ Θ Δ F e T and ptyped W Σ p T, indexed by the
world W = W_G. The fresh μ of E-Abs and E-Exp is a frame variable φ with the hypothesis u ≺ φ
in Φ, at the same W. E-Exp types the body once with ιs as point variables 0, …, m−1 and Φ, □Δ
and the recursive binding shifted past them (57). E-Const asks kscoped of send and recv. The
other rules as in §9. typed_pinst substitutes points for point variables. typed_ityped does that
and instantiates φ at any later world into the infinitary judgment of 53. "G closed under the
substitutions" holds of every well-formed W, because W knows constants only and relates points
with a variable root by reflexivity and program order.
fundamental (terms), fundamental_proc (processes, P-Connect by Prel_connect with W₁ = W₂ = W),
soundness (strict W, ptyped W ∅ p T ⇒ deadlock_free p, via adequacy). All closed under the
global context.
Restoring a fresh point μ needs "dropping a fresh conservative extension", which is false at
V-Const (sharp edges 54, DropCounter.v). A frame variable avoids the lemma, because no point,
type or world mentions it (56).
Constrained boxes (58): typed W Φ Ψ Θ Δ F e T carries the hypotheses Ψ, and slt W Ψ is the
static ≺. E-Exp extends the shifted Ψ by C. typed_pinst asks Ψ[σ] in slt W Ψ′, typed_ityped
asks Ψ[σ] in ≺_{W₁}, and a derived fact survives because each generator does (slt_pinst).
The infinitary it_box reads C[xs/ιs] in W₁ and carries term_wf of the body, which
typed_term_wf_s reads off the finitary derivation. Example: ordered_typed, ordered_force.
Steps and new under □∀ (61): Ψ is a list of hypotheses (C, xs) and sl_h yields C at every word
of xs. typed_ityped asks every hypothesis of Ψ[σ] to hold in W₁ at known instance points,
typed_pinst asks it in slt W Ψ′ with skn. Words commute with substitution (wins_pinst), so
bcs_hold_inst and hyp_fact_inst carry facts through both. A recursive call at a step uses
bcs_hold_step. soundness, fundamental, fundamental_proc, Prel_connect_n and all eight
deadlock_free examples are closed under the global context (dc8acc1, 18b13f1).


## 13  Examples

(c, k) below is the point of c's entry after k actions.

```
sync            typable                       new and spawn instead of fork
cycle           typable (before: semantic)     P-Connect over {c, d},  (c,0) ≺ (d,0) in both threads
blocked         rejected                       (c,0) ≺ (d,0) and (d,0) ≺ (c,0)
load balancer   semantic                       races on c, unchanged
factory         typable                        new at ι under □∀ι, two sessions at (a,0), (b,0) held at once (61)
leader election semantic                       breaks linearity, unchanged
scheduler       typable (before: semantic)     (r₁,0) ≡ (r₀,0) from the link,  reversed ag₀ rejected
request/reply   typable, recursive             step (ι+1, ι′+1), (a,k) ≺ (b,k) ≺ (a,k+1) for all k (61)  [new]
relay           typable, recursive             step (ι+1, ι[0]+1), producer creates its payload at ι[0] (61)  [new]
delegation      typable                        receiver: c[k][1] ≺ (c,k+1),  sender aliases d to it  [new]
bad link        rejected                       (c,0) ≺ (e,0) ≺ (d,0) ≡ (c,0)                         [new]
```

## 14  Open

- Deferred by the author: order that depends on the run (one W per component); slot positions must be finite schemas in G.
- To prove: free-coordinate extension of Kosaraju–Sullivan (paper level); chain arguments in P-Term and P-Connect; all frame-carrying lemmas.
- Mechanization: Θ (both ends) only at term level, points in `senv` entries, worlds over points with aliases, amalgamation.

## 15  Lessons from the earlier mechanization (respect these)

An earlier order design was mechanized and abandoned. What it taught, and how this spec already accounts for it:

- Minimality ("my instant is minimal") is unsound as a gate. ready here compares every held entry with some offered entry, strictly, and compares entries, never sets of instants (equal instants must not collapse into one element; that is why no "distinct channels have distinct instants" premise is needed).
- The old cut only composed when the composite's external interface carried no ordering, because a leastness-shaped gate is not invariant under external steps. Here ready is checked per state by each component, and P-Connect combines them state by state with the chain argument. This is the central claim and the main risk; report early if it does not go through.
- Step preservation of the cut was left open in three cases: rendezvous with payload migration (handled here by Q-Recv stating its continuation with the returning channels restricted), link with an external survivor (the paper's substitution, plus Entry conversion; worlds name no channels), mixed extrusion (no plain/ordered mix here). Report early if any of them resists.
- Term-level ∀-introduction got stuck (instantiation needed an order-indistinguishable world copy). Here ∀ appears only directly under □, on values, and is an intersection over instances.
- The frame/window condition holds for offered entries only; a condition on all pending heads is false (recv returns a continuation above its own instant).
- A closure without a lower bound must hold nothing (ℓ = ⊤ forces Σ = ∅).
- Unrolling under ≈ needs contractiveness (the paper already assumes it). Counters live in Σ, not in types, so unrolling never has to advance an annotation.
- Constants are typed through their signatures, one compositionality lemma per constant.

## 16  Out of scope for now

Neither item is part of the current Rocq round, and neither is on the progress page.

Decidability of "W_G strict". Uniform schemas (every counter shifted by a constant on both
sides) are a zero-cycle problem on a periodic graph, decided by Kosaraju–Sullivan 1988 in
polynomial time. Schemas with a counter on one side only (e.g. ∀b. (c[κ][1], b) ≺ (c, κ+1)) give
edges with a free coordinate; extension of their linear program believed decidable, proof open.
The static system produces only uniform edges (equal counters on both sides) and free-coordinate
edges (independent counters), so the free-coordinate extension covers every schema it emits.

An algorithmic type system. The static system of §9 is declarative. Missing for an algorithm:
- choosing G: rules emit facts instead of checking them; G is the collected set
- checking G: the decision procedure above
- fresh points (E-Abs μ, ℓ; new ι): generate fresh point variables
- ∀ instantiation (E-Force): unification over points
- payload points (send's ∃xs): determined by the aliases to the slot
- environment splitting (E-App, E-Let*): input/output contexts
- conversion (E-Conv): ≈ on regular session types is decidable; apply at application/ascription
- annotations: ∀ schemes under □ and recursive types are given, not inferred
