# Order-based GV♯: specification (state of 2026-10-29)

This file is the current design. It supersedes every earlier order design
(the old `orders` branch, `orders.lagda`, `orders-examples.txt`,
`paper/orders-plan.pdf`). Notation follows the paper (`paper/2-calculus.tex`,
`paper/3-logical-rel.tex`, `paper/4-extensions.tex`). Tags: `[new]`,
`[changed]`, `[removed]` relative to the paper.

The frame F is an input parameter of E. F = ∅ is exactly the paper's E. It is
part of E (not a separate relation) so that E and the frame condition use the
same world extension at every `new`.

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
T-Act-Link      link ⟨c, d⟩                —c↔d→    ∗
T-Act-Ctx       t —λ→ t′   ⇒   𝒦[t] —λ→ 𝒦[t′]
```

## 3  Process LTS   p = (C, E),  π ::= τ | σ

```
P-Act-New       c fresh    t —(νc)→ t′      (C, E ⊎ {t}) —τ→ (C ⊍ {c}, E ⊎ {t′})        [new]
P-Act-Spawn     t —⇑v→ t′                   (C, E ⊎ {t}) —τ→ (C, E ⊎ {t′, v ∗})          [new]
P-Act-Beta      t —β→ t′                    (C, E ⊎ {t}) —τ→ (C, E ⊎ {t′})
P-Act-Msg       t —c!v→ t′   u —c?v→ u′     (C, E ⊎ {t, u}) —τ→ (C, E ⊎ {t′, u′})
P-Act-Close     t —c!→ t′    u —c!→ u′      (C ⊍ {c}, E ⊎ {t, u}) —τ→ (C, E ⊎ {t′, u′})
P-Act-Link      t —c↔d→ t′                  (C ⊍ {c}, E ⊎ {t}) —τ→ (C, (E ⊎ {t′})[d/c])
P-Act-Session   t —σ→ t′   fc(σ) # C        (C, E ⊎ {t}) —σ→ (C ∖ sent(σ), E ⊎ {t′})      unchanged
                                                                   [removed] P-Act-Fork
```

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
T, U ::= ∗ | T ⊗ U | T + U | T ⊸^β_λ U | S@ι | □(∀ιs. T)            term types
β    ::= ι | ⊥            upper point: the call blocks at most at β     (⊥: never blocks)
λ    ::= ι | ⊤            lower point: the closure holds only above λ   (⊤: holds nothing)
S    ::= ?P.S | !P.S | Close | μX.S | X                                 session types, unannotated
P    ::= ∃ιs. T           payload, all points of T bound                sugar: !(S₁ ⊗ S₂).S binds them implicitly
ι    ::= (p, b)           a point: a name with an offset
p    ::= a | ι-variable | p[b][i]     point constant, bound point variable, slot "the i-th point carried at (p,b)"
         Types never mention channel names (decision F2). Channel names, and slots rooted at channels
         such as (c,k)[i], occur only in worlds and environments; types reach channels only through
         aliases in W. Renaming channels therefore never changes a type.                          [changed]

Σ    ::= · | c : S@k | Σ, Σ                       process level, a finite map,  k = actions done on c
Θ    ::= Σ | Θ, c : S@k, c : S′@k                  term level, may hold both ends,  S ⊥ S′
Δ    ::= · | x : T | Δ, Δ
prim ∗,  prim T ⊗ U,  prim T + U,  prim □T if prim T     (as in the paper)

heads(∗) = heads(□σ) = ∅      heads(S@ι) = {ι}      heads(T ⊸^β_λ U) = {λ} ∖ {⊤}
heads(T ⊗ U) = heads(T + U) = heads(T) ∪ heads(U)
heads(c : S@k) = {(c, k)}     heads(Σ, Δ) = ⋃ heads of the entries
```

- ∀ appears only directly under □ (never on linear functions, never inside session types).
- Points are extra names in the order, not k-th actions of a channel; facts may place them anywhere. A point used as S@ι is aliased to the channel's current instant.

## 5  Worlds   [new]

```
carrier     instants (p, b)
W = (≡, ≺)  ≡ equivalence (aliases),  ≺ strict partial order on ≡-classes
            ⊇ program order (p, b) ≺ (p, b+1) for every name p
alias       p@a ≡ q@b   ≔   (p, a+n) ≡ (q, b+n) for all n
slot congruence   x ≡ y  ⇒  x[i] ≡ y[i]        (equal instants carry the same message)      [new]
            the support of a world is counted on root names (channels and point variables)
F ≺ G       every element of F is ≺ every element of G        (frames, ⊥ and ⊤ as expected)

W ⊑ W′      ≡ ⊆ ≡′,  ≺ ⊆ ≺′,  W′ strict                        (Kripke order)
W ⊑ₒ W′     W ⊑ W′ and W′ adds nothing between old instants    (only at new)
W₁ ⊔ W₂     (≡₁ ∪ ≡₂)* with (≺₁ ∪ ≺₂)⁺ on the classes
```

## 6  Readiness and frames   [new]

```
entries(Θ)   one entry per end:  c : S@k  (twice for a channel whose both ends Θ holds)
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

```
```

## 7  Logical relation   V^W_n⟦Σ ⊢ T⟧,  E^W_n⟦Θ ⊢ T ≺ F⟧,  P^W_n⟦Σ ⊢ T⟧

```
V-Unit    ∗ ∈ V^W_n⟦· ⊢ ∗⟧
V-Chan    c ∈ V^W_n⟦c : S@k ⊢ S′@x⟧            if S ≈ S′ and c@k ≡_W x,  x a point (never a channel)   [changed]
V-Const   k ∈ V^W_n⟦· ⊢ T⟧                     if k : T  (instance of its signature)
V-Pair    v₁ ∈ V^W_n⟦Σ₁ ⊢ T⟧   v₂ ∈ V^W_n⟦Σ₂ ⊢ U⟧   ⇒   ⟨v₁, v₂⟩ ∈ V^W_n⟦Σ₁, Σ₂ ⊢ T ⊗ U⟧
V-Inj     v ∈ V^W_n⟦Σ ⊢ Tᵢ⟧   ⇒   injᵢ v ∈ V^W_n⟦Σ ⊢ T₁ + T₂⟧
V-Abs     fchans(t) = dom Σ        {λ} ≼_W heads(Σ)                                      [changed]
          ∀W′ ⊒ W, j < n, Σ′, v ∈ V^{W′}_j⟦Σ′ ⊢ T⟧, F with {β} ≺_{W′} F.
              t[v/x] ∈ E^{W′}_j⟦Σ, Σ′ ⊢ U ≺ F⟧
          ⇒   λx.t ∈ V^W_n⟦Σ ⊢ T ⊸^β_λ U⟧
V-Box     fchans(t) = ∅     ∀W′ ⊒ W.  fix x.t ∈ E^{W′}_n⟦· ⊢ T ≺ ∅⟧   ⇒   !(x = t) ∈ V^W_n⟦· ⊢ □T⟧
V-All     v ∈ V^W_n⟦Σ ⊢ ∀ιs. T⟧   ≔   ∀xs.  v ∈ V^W_n⟦Σ ⊢ T[xs/ιs]⟧                     [new]

payload at a slot      the value is typed T[xs/ιs] for P = ∃ι₁ … ιₘ. T, with type points xs such that
                       xᵢ ≡_W (c, k)[i].  O-Send/Q-Send: ∃xs in the sender's world.  O-Recv/Q-Recv:
                       ∀W′ ⊒ W, ∀xs with these aliases in W′ (no freshness: P-Connect instantiates the
                       receiver with the sender's xs). Written P[(c, k)] below.
names                  two sorts: type points (constants, bound variables, slots of those) and world
                       instants (channels, embedded type points, slots of either), joined by an embedding;
                       slots rooted at channels exist only in worlds.

E-Zero    t ∈ E^W_0⟦Θ ⊢ T ≺ F⟧
E-Stop    v ∈ V^W_{n+1}⟦Θ ⊢ T⟧   ⇒   v ∈ E^W_{n+1}⟦Θ ⊢ T ≺ F⟧
E-Step    ¬irred t    ready_W(Θ, t)    frame_W(t, F)                                      [changed]
          ∀λ, t′.  t —λ→ t′  ⇒  Θ ⊩ⁿ_W t —λ→ t′ : T ≺ F
          ⇒   t ∈ E^W_{n+1}⟦Θ ⊢ T ≺ F⟧

O-Beta    t′ ∈ E^W_n⟦Θ ⊢ T ≺ F⟧
O-New     c ∉ names(W)    ∃S ⊥ S′, W′ ⊒ₒ W placing c.   t′ ∈ E^{W′}_n⟦Θ, c : S@0, c : S′@0 ⊢ T ≺ F⟧    [new]
O-Spawn   Θ = Θ₁, Θ₂     v ∈ V^W_{n+1}⟦Θ₁ ⊢ ∗ ⊸^β_λ ∗⟧     t′ ∈ E^W_n⟦Θ₂ ⊢ T ≺ F⟧       [new]
O-Send    Θ = Θ₁, Θ₂, c : (!P.S)@k     v ∈ V^W_{n+1}⟦Θ₂ ⊢ P[(c, k)]⟧                    [changed]
          t′ ∈ E^W_n⟦Θ₁, c : S@(k+1) ⊢ T ≺ F⟧
O-Recv    Θ = Θ₁, c : (?P.S)@k                                                           [changed]
          ∀W′ ⊒ W, j ≤ n, Σ₂, v ∈ V^{W′}_j⟦Σ₂ ⊢ P[(c, k)]⟧,  Θ₁, Σ₂ defined.
              t′ ∈ E^{W′}_j⟦Θ₁, Σ₂, c : S@(k+1) ⊢ T ≺ F⟧
          (Θ may then hold both ends of a received channel; Θ₁, Σ₂ is defined when every
           overlap is a pair of dual ends at the same count)
O-Close   Θ = Θ₁, c : Close@k      t′ ∈ E^W_n⟦Θ₁ ⊢ T ≺ F⟧
O-Link    Θ = Θ₁, c : S@k, d : S′@j    S ⊥ S′    c@k ≡_W d@j                              [changed]
          t′ ∈ E^W_n⟦Θ₁ ⊢ T ≺ F⟧
          (c = d allowed: a self-link, Θ holds both ends of c; both entries leave Θ.
           Matches P-Act-Link with c = d, which releases c. `link (new ∗)` is typable.)
                                                                [removed] O-Fork

P-Zero    p ∈ P^W_0⟦Σ ⊢ T⟧
P-Stop    v ∈ V^W_{n+1}⟦Σ ⊢ T⟧   ⇒   (∅, {v, ∗, …, ∗}) ∈ P^W_{n+1}⟦Σ ⊢ T⟧
P-Step    ¬irred p    ready_W(Σ, p)                                                       [changed]
          ∀π, p′.  p —π→ p′  ⇒  Σ ⊩ⁿ_W p —π→ p′ : T
          ⇒   p ∈ P^W_{n+1}⟦Σ ⊢ T⟧

Q-Tau     p —τ→ p′    ∃W′ ⊒ W.   W′ strict,   W′|_vis = W|_vis,   p′ ∈ P^{W′}_n⟦Σ ⊢ T⟧         [changed]
          vis = all names except those restricted in p or in p′ (what the environment can see;
                "or in p" so that a link removing d can create the alias c ≡ d)
          checked for steps with p′'s restricted channels disjoint from dom Σ (the paper's implicit
          convention "Σ and C share no channels", made explicit)
          if the step creates c (new):  c ∉ names(W)
          if the step links an external c (Σ ∋ c : S@k) with a restricted d at count j:
              c@k ≡_{W′} d@j        (the alias may be created by this step; mirrors O-Link;
                                      a link between two restricted channels needs nothing)
          The paper's Q-Tau is the case W′ = W. The world may grow, but invisibly; this replaces
          the paper's invariance under channel substitution, which no longer holds for free once
          names carry facts.
Q-Recv    Σ = Σ₁, c : (?P.S)@k     p —c?v→ (C′, E′)                                       [changed]
          ∀W′ ⊒ W, j ≤ n, Σ₂, v ∈ V^{W′}_j⟦Σ₂ ⊢ P[(c, k)]⟧,  Σ₂ dual to (Σ₁, c : S@(k+1)) on their overlap B,
          dom Σ₂ ∖ B # names(W)   (fresh: no received channel inherits stale facts of an old name).
              ∃π renaming only restricted names of (C′ ∪ B, E′).
              π·(C′ ∪ B, E′) ∈ P^{W′}_j⟦(Σ₁, c : S@(k+1)) ∖ B, Σ₂ ∖ B ⊢ T⟧
          (α-variant: restricted names are bound, so the environment's W′ cannot pin
           stale facts on them; P-Term uses π = id)
          (B = channels whose other end the receiver already holds. The obligation is stated
           for the successor with B restricted; the LTS itself does not restrict. If the carrier c
           itself is in B (an end of c was sent over c), its continuation entry leaves Σ as well.
           Σ₂ is a term-level environment: a payload may carry both ends of one channel; such a
           channel also belongs to B and is restricted in the continuation.
           The guard c ∉ dom Σ₂ of the paper is dropped (c may be in B).
           Lemma needed: restricting B only removes external steps on channels no environment holds.)
Q-Send    Σ = Σ₀, Σ_v, c : (!P.S)@k      dom Σ_e = fchans(v) ∩ C                          [changed]
          v ∈ V^W_{n+1}⟦Σ_v, Σ_e′ ⊢ P[(c, k)]⟧      p′ ∈ P^W_n⟦Σ₀, Σ_e, c : S@(k+1) ⊢ T⟧
          Σ_e′ = ends of dom Σ_e that leave with v,   Σ_e = ends that stay
          (both ends of a restricted channel may leave with v; then it has no entry in Σ_e)

Obligations whose continuation environment cannot be formed (e.g. Θ already holds both
ends of c) fail; such a thread is never ready anyway.
Q-Close   Σ = Σ₁, c : Close@k      p′ ∈ P^W_n⟦Σ₁ ⊢ T⟧
Q-Link    c ≠ d    Σ = Σ₁, c : S@k, d : S′@j    S ⊥ S′    c@k ≡_W d@j                     [changed]
          p′ ∈ P^W_n⟦Σ₁ ⊢ T⟧
          (c = d cannot reach the interface: process-level Σ holds one end per channel)
                                    [removed] extrusion split 𝒯, T-Nil, T-Cons, Q-Twice
```

## 8  Semantic judgments

```
Θ; Δ ⊨^F_W t : T   ≔   ∀n, W′ ⊒ W, Σ′ # Θ, γ ∈ G^{W′}_n⟦Σ′; Δ⟧.   tγ ∈ E^{W′}_n⟦Θ, Σ′ ⊢ T ≺ F⟧
Σ ⊨_W p : T        ≔   ∀n.  p ∈ P^W_n⟦Σ ⊢ T⟧
Θ; Δ ⊨_W t : T     ≔   Θ; Δ ⊨^∅_W t : T                  (the paper's judgement, plus ready)
```

## 9  Static typing   Θ; Δ ⊢^F_G t : T   [new parts]

```
G          finite set of fact schemas and alias schemas over points
W_G        the world G generates, required strict
           Num: total.   Fin: G finite.   Decided by Kosaraju–Sullivan plus free coordinates (§11)

new    : ∗ ⊸^⊥_⊤ S@ι ⊗ S′@ι                                  S ⊥ S′,  ι fresh
spawn  : (∗ ⊸^β_λ ∗) ⊸^⊥_⊤ ∗
send   : (T[ιs] ⊗ (!P.S)@ι) ⊸^ι_⊤ S@(ι+1)    P = ∃ιs. T,  {ι} ≺_G heads(T[ιs]),  each ιsᵢ ≡_G ι[i]
recv   : (?P.S)@ι ⊸^ι_⊤ P[ι] ⊗ S@(ι+1)
close  : Close@ι ⊸^ι_⊤ ∗
link   : S@ι ⊗ S′@ι′ ⊸^ι_⊤ ∗                                  S ⊥ S′,  ι ≡_G ι′
force  : □(∀ιs. T) ⊸^⊥_⊤ T[ιs′/ιs]

E-Unit     ·; · ⊢^F ∗ : ∗
E-Const    k : T   ⇒   ·; · ⊢^F k : T
E-LVar     ·; x : T ⊢^F x : T
E-Ch       c : S@k; · ⊢^F c : S@ι        with ι ≡_G (c, k)  (a point aliased to the channel's instant)
E-Abs      Θ; Δ, x : T ⊢^{{μ}} t : U      μ fresh, only fact β ≺ μ      λ fresh, only facts {λ} ≼ heads(Θ, Δ)
           ⇒   Θ; Δ ⊢^F λx.t : T ⊸^β_λ U
E-App      Θ₁; Δ₁ ⊢^{F ∪ heads(Θ₂, Δ₂)} t₁ : T ⊸^β_λ U     Θ₂; Δ₂ ⊢^{F ∪ {λ}} t₂ : T     {β} ≺_G F
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
E-Exp      ·; □Δ, x : □(∀ιs. T) ⊢^∅ t : T     G closed under the substitutions at recursive calls
           ⇒   ·; □Δ ⊢^F !(x = t) : □(∀ιs. T)
E-Weak, E-Contract, E-Conv      as in the paper, with ⊢^F

P-Term     prim T    Σ, Θ_B; · ⊢^∅ t : T    Θ_B = both ends of every channel in C₀           [changed]
           ⇒   Σ ⊢_G (C₀, {t}) : T
P-Connect  Σ₁, Σ_C ⊢_G (C₁, E₁) : T    Σ₂, Σ_C′ ⊢_G (C₂, E₂) : ∗    Σ_C ⊥ Σ_C′ over C₀ (possibly ∅)
           ⇒   Σ₁, Σ₂ ⊢_G (C₁ ⊍ C₂ ⊍ C₀, E₁ ⊎ E₂) : T                                     [changed]
                                                      [removed] P-Independent, P-Res
```

## 10  Lemmas: LTS and worlds

```
Harmony                          p —τ→ p′  ⇔  p ⟶ p′                       unchanged statement
Internalizing communication      generalized to a cut C₀ (statement otherwise unchanged)          [changed]
Restriction of returning channels
                  in the P-Connect proof the composite's successor equals the receiving component's
                  successor with B restricted, because B already lies in the cut C₀            [new]
Internalizing a close            unchanged

Amalgamation      W₁, W₂ strict  ⇒  (W₁ ⊔ W₂ strict  ⇔  (W₁|_A ⊔ W₂|_A) strict),   A = names W₁ and W₂ share
Fresh extension   W₁ ⊑ₒ W₁′ placing names N,  N # names(W₂),  W₂ strict,  W₁ ⊔ W₂ strict
                  ⇒   W₁′ ⊔ W₂ strict
Monotonicity      W ⊑ W′  ⇒  V/E^W ⊆ V/E^{W′}      (needs world_wf W)
                  P: monotone only up to renaming restricted names (a larger world may mention them)
Renaming restricted names                                                                  [new]
                  restricted names are bound: V, E and P are invariant under a bijective renaming of
                  channel names applied to processes, types, environments and worlds alike; a process
                  can rename its restricted names away from any names a given world mentions.
                  (Extends the paper's invariance under channel substitution, Renaming.v, to worlds.
                   Needed because Q-Recv's W′ ⊒ W may state facts about names the process restricts.)
Frame weakening   F′ ⊆ F  ⇒  E^W_n⟦Θ ⊢ T ≺ F⟧ ⊆ E^W_n⟦Θ ⊢ T ≺ F′⟧
Renaming along an alias
                  p ∈ P^W_n⟦Σ, c : S@k ⊢ T⟧,   c@k ≡_W d@j   ⇒   p[d/c] ∈ P^W_n⟦Σ, d : S@j ⊢ T⟧
                  (needs slot congruence; report if a further freshness premise is needed)
Internalizing a link
                  a link between two cut channels in the composite combines the components' steps   [new]
LTS renaming      a bijective renaming of channel names preserves process steps and safety        [new]
                  (used by adequacy: runs whose fresh names are known to W are renamings of runs
                   whose fresh names are not)
Prel_steps, Prel_safe            restated for runs with names fresh for W (Q-Tau at new)
Invisible extension
                  W₁ ⊑ W₁′ strict with W₁′ unchanged on the names W₂ knows, W₁ ⊔ W₂ strict
                  ⇒  W₁′ ⊔ W₂ strict        (by Amalgamation; generalizes Fresh extension)   [new]
```

## 11  Lemmas: compositionality (one per rule)

```
E-Unit      ·; · ⊨^F ∗ : ∗
E-Const     k : T   ⇒   ·; · ⊨^F k : T                      for new, spawn, send, recv, close, link, force
E-LVar      ·; x : T ⊨^F x : T
E-Ch        c : S@k; · ⊨^F c : S@ι        with ι ≡_W (c, k)
E-Abs       ∀F′ with {β} ≺ F′.  Θ; Δ, x : T ⊨^{F′} t : U       {λ} ≼ heads(Θ, Δ)
            fchans(t) = dom Θ      fv(t) = dom(Δ, x : T)
            ⇒   Θ; Δ ⊨^F λx.t : T ⊸^β_λ U
E-App       Θ₁; Δ₁ ⊨^{F ∪ heads(Θ₂, Δ₂)} t₁ : T ⊸^β_λ U     Θ₂; Δ₂ ⊨^{F ∪ {λ}} t₂ : T     {β} ≺ F
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
E-Exp       ∀xs.  ·; □Δ, x : □(∀ιs. T) ⊨^∅ t : T[xs/ιs]     fchans(t) = ∅     fv(t) ⊆ dom(□Δ, x)
            ⇒   ·; □Δ ⊨^F !(x = t) : □(∀ιs. T)
E-Force     Θ; Δ ⊨^F t : □(∀ιs. T)   ⇒   Θ; Δ ⊨^F force t : T[xs/ιs]
E-Weak      Θ; Δ ⊨^F t : U   ⇒   Θ; Δ, x : □T ⊨^F t : U
E-Contract  Θ; Δ, x : □T, y : □T ⊨^F t : U   ⇒   Θ; Δ, x : □T ⊨^F t[x/y] : U
E-Conv      Θ; Δ ⊨^F t : T,   T ≈ T′   ⇒   Θ; Δ ⊨^F t : T′

P-Term      prim T,   Σ, Θ_B; · ⊨^∅_W t : T,   Θ_B both ends of C₀
            ⇒   Σ ⊨_W (C₀, {t}) : T
            proof: chain argument over C₀ inside one thread
P-Connect   prim T,   Σ₁, Σ_C ⊨_{W₁} (C₁, E₁) : T,   Σ₂, Σ_C′ ⊨_{W₂} (C₂, E₂) : ∗,
            Σ_C ⊥ Σ_C′ over C₀,   C₁ # dom Σ₂,   C₂ # dom Σ₁,   W₁ ⊔ W₂ strict
            ⇒   Σ₁, Σ₂ ⊨_{W₁ ⊔ W₂} (C₁ ⊍ C₂ ⊍ C₀, E₁ ⊎ E₂) : T
            proof: ready by the chain argument across C₀;  τ steps by the Internalizing lemmas,
                   a message instantiates Q-Recv with W₁ ⊔ W₂ (the sender's alias names the payload),
                   new by Fresh extension,  link by Renaming along an alias

P-Connectⁿ  (corollary, by induction on n using P-Connect; every partial amalgam is a subset of the full one)
            Σᵢ, Σ_Cᵢ ⊨_{Wᵢ} (Cᵢ, Eᵢ) : Tᵢ  (i = 1 … n),  exactly one Tᵢ = T, all others ∗,
            the Σ_Cᵢ together hold both ends of every channel in C₀, each end once, dual,
            W₁ ⊔ … ⊔ Wₙ strict
            ⇒   Σ₁, …, Σₙ ⊨_{W₁ ⊔ … ⊔ Wₙ} (C₁ ⊍ … ⊍ Cₙ ⊍ C₀, E₁ ⊎ … ⊎ Eₙ) : T
```

## 12  Main results

```
Fundamental     Θ; Δ ⊢^F_G t : T   ⇒   Θ; Δ ⊨^F_{W_G} t : T
                Σ ⊢_G p : T        ⇒   Σ ⊨_{W_G} p : T
Adequacy        · ⊨_W p : T   ⇒   p deadlock free         (paper's proof plus LTS renaming for fresh names)
Soundness       · ⊢_G p : T,  W_G strict   ⇒   p deadlock free
Decidability    W_G strict is decidable:  Kosaraju–Sullivan for edges with offsets,
                plus our lemma for schemas with a variable on one side only (free coordinates)
                (paper-level, not mechanized in this round)
```

## 13  Examples

```
sync            typable                       new and spawn instead of fork
cycle           typable (before: semantic)     P-Connect over {c, d},  (c,0) ≺ (d,0) in both threads
blocked         rejected                       (c,0) ≺ (d,0) and (d,0) ≺ (c,0)
load balancer   semantic                       races on c, unchanged
factory         typable                        repl and req via new, spawn and □∀
leader election semantic                       breaks linearity, unchanged
scheduler       typable (before: semantic)     r₁@0 ≡ r₀@0 from the link,  reversed ag₀ rejected
request/reply   typable, recursive             (a,κ) ≺ (b,κ),  (b,κ) ≺ (a,κ+1) under □∀κ          [new]
delegation      typable                        receiver: c[k][1] ≺ (c,k+1),  sender aliases d to it  [new]
bad link        rejected                       (c,0) ≺ (e,0) ≺ (d,0) ≡ (c,0)                         [new]
```

## 14  Open

- Deferred by the author: order that depends on the run (one W per component); slot positions must be finite schemas in G.
- To prove: free-coordinate extension of Kosaraju–Sullivan (paper level); chain arguments in P-Term and P-Connect; all frame-carrying lemmas.
- Mechanization: Θ (both ends) only at term level, counters in `senv`, worlds with aliases, amalgamation.

## 15  Lessons from the earlier mechanization (respect these)

An earlier order design was mechanized and abandoned. What it taught, and how this spec already accounts for it:

- Minimality ("my instant is minimal") is unsound as a gate. ready here compares every held entry with some offered entry, strictly, and compares entries, never sets of instants (equal instants must not collapse into one element; that is why no "distinct channels have distinct instants" premise is needed).
- The old cut only composed when the composite's external interface carried no ordering, because a leastness-shaped gate is not invariant under external steps. Here ready is checked per state by each component, and P-Connect combines them state by state with the chain argument. This is the central claim and the main risk; report early if it does not go through.
- Step preservation of the cut was left open in three cases: rendezvous with payload migration (handled here by Q-Recv stating its continuation with the returning channels restricted), link with an external survivor (handled here by the linker's alias and Renaming along an alias), mixed extrusion (no plain/ordered mix here). Report early if any of them resists.
- Term-level ∀-introduction got stuck (instantiation needed an order-indistinguishable world copy). Here ∀ appears only directly under □, on values, and is an intersection over instances.
- The frame/window condition holds for offered entries only; a condition on all pending heads is false (recv returns a continuation above its own instant).
- A closure without a lower bound must hold nothing (λ = ⊤ forces Σ = ∅).
- Unrolling under ≈ needs contractiveness (the paper already assumes it). Counters live in Σ, not in types, so unrolling never has to advance an annotation.
- Constants are typed through their signatures, one compositionality lemma per constant.
