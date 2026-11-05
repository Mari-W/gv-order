# Order-based GV♯: specification (state of 2026-11-05, end points: every channel end has its own point; before that sharp edges 149: choice at x[i] (K11), constants as constrained schemes, C₀ as creation constraint, absent bounds)

End points (2026-11-05, branch end-points). Each end of a channel has its own
point. new creates the two ends at the dual points ι and ῑ. A point carries a
polarity, x̄ flips it, and x̄̄ = x, x̄+n = (x+n)‾, x̄[i] = x[i] (Rocq `pt_dual`,
`pt_polar`, `pt_payload_dual`). The head of an end at x is its partner point
{x̄}, so a thread blocked at u that holds an end at v owes u ≺ v̄. The fact
theory gains x ≡ y ⇒ x̄ ≡ ȳ (`se_dual`) and x ≺ x̄+1 (`fl_dpo`). The two ends of
a channel are dual at dual points, x ≡ ȳ, where they were dual at aliased
points. Readiness compares an offered point with the partner points of the
held ends. A choice moves the selecting end to (x[i])‾ and the branching end
to x[i], and link asks x ≡ ȳ. The instance with x ≡ x̄ for every point is the
old system with one point per channel. The sections below are updated to end
points where they state a rule. Rocq: theories/types/Types.v,
static/FactTheory.v, static/Typing.v, relation/Worlds.v, Readiness.v,
LogicalRelation.v, Creation.v on branch end-points.

This file is the current design. It supersedes every earlier order design
(the old `orders` branch, `orders.lagda`, `orders-examples.txt`,
`paper/orders-plan.pdf`). Notation follows the paper (`paper/2-calculus.tex`,
`paper/3-logical-rel.tex`, `paper/4-extensions.tex`). Rules marked unchanged
are the paper's as they stand. The others add points, worlds or futures to the
paper's rule of the same name, or have no counterpart in the paper. The paper's
fork, P-Act-Fork, O-Fork, extrusion split (𝒯, T-Nil, T-Cons, Q-Twice),
P-Independent and P-Res have no counterpart here.

The future F is an input parameter of E. F = ∅ is exactly the paper's E. It is
part of E (not a separate relation) so that E and readiness use the same world
extension at every `new`.

Worlds speak about points only, never about channel names (sharp edges 37).
Every environment entry carries the point of its end's current instant,
c : S@x, and the other end of c sits at the partner point x̄. Renaming channels therefore never touches a world, link substitutes as
in the paper, and the paper's renaming and junk lemmas hold with the world fixed.

## 1  Syntax

```
k  ::= new | spawn | recv | send | close | link | force | select₁ | select₂ | branch      (choice: K4, sharp edges 72)
v  ::= ∗ | k | c | λx.t | ⟨v, v⟩ | inj₁ v | inj₂ v | !(x = t)
t  ::= x | v | t t | ⟨t, t⟩ | inj₁ t | inj₂ t | let () = t in t | let (x, y) = t in t
     | case t of inj₁ x ⇒ t | inj₂ x ⇒ t
𝒦  ::= □ | 𝒦 t | v 𝒦 | ⟨𝒦, t⟩ | ⟨v, 𝒦⟩ | injᵢ 𝒦 | let () = 𝒦 in t | let (x, y) = 𝒦 in t | case 𝒦 of …

σ  ::= c?v | c!v | c! | c↔d | c◁i | c▷i      (i = 1, 2)                 session labels
λ  ::= β | σ | (νc) | ⇑v term labels
fc(β) = fc((νc)) = fc(⇑v) = ∅    fc(c?v) = fc(c!v) = fc(c!) = fc(c◁i) = fc(c▷i) = {c}    fc(c↔d) = {c, d}
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
T-Act-New       new ∗                      —(νc)→   ⟨c, c⟩
T-Act-Spawn     spawn v                    —⇑v→     ∗
T-Act-Recv      recv c                     —c?v→    ⟨v, c⟩
T-Act-Send      send ⟨v, c⟩                —c!v→    c
T-Act-Close     close c                    —c!→     ∗
T-Act-Link      link ⟨c, d⟩                —c↔d→    ∗            (c = d allowed)
T-Act-Select    selectᵢ c                  —c◁i→    c
T-Act-Branch    branch c                   —c▷i→    injᵢ c       (for both i: branch takes either pick)
T-Act-Ctx       t —λ→ t′   ⇒   𝒦[t] —λ→ 𝒦[t′]
```

## 3  Process LTS   p = (C, E),  π ::= τ | σ

```
P-Act-New       c fresh    t —(νc)→ t′      (C, E ⊎ {t}) —τ→ (C ⊍ {c}, E ⊎ {t′})
P-Act-Spawn     t —⇑v→ t′                   (C, E ⊎ {t}) —τ→ (C, E ⊎ {t′, v ∗})
P-Act-Beta      t —β→ t′                    (C, E ⊎ {t}) —τ→ (C, E ⊎ {t′})
P-Act-Msg       t —c!v→ t′   u —c?v→ u′     (C, E ⊎ {t, u}) —τ→ (C, E ⊎ {t′, u′})
P-Act-Close     t —c!→ t′    u —c!→ u′      (C ⊍ {c}, E ⊎ {t, u}) —τ→ (C, E ⊎ {t′, u′})
P-Act-Choice    t —c◁i→ t′   u —c▷i→ u′     (C, E ⊎ {t, u}) —τ→ (C, E ⊎ {t′, u′})     (like P-Act-Msg)
P-Act-Link      t —c↔d→ t′                  (C ⊍ {c}, E ⊎ {t}) —τ→ (C, (E ⊎ {t′})[d/c])      unchanged
P-Act-Session   t —σ→ t′   fc(σ) # C        (C, E ⊎ {t}) —σ→ (C ∖ sent(σ), E ⊎ {t′})      unchanged
```

Link substitutes in the whole soup, as in the paper. With c = d it releases c. Worlds
mention no channel names, so the substitution never has to move a fact (sharp edges 37).

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

## 4  Types and environments

```
T, U ::= ∗ | T ⊗ U | T + U | T ⊸^u_ℓ U | S@ι | □(∀ιs. C. ∗ ⊸^u T)      term types (sharp edges 52, 63, 65)
                          A box is a polymorphic thunk. Its upper point u lives on the arrow,
                          under the binder, and may mention ιs. The box former carries no point.
C    ⊆ { x ≺ y,  x ≡ y }  constraint of a box: any set of positive facts, finite or infinite,   (sharp edges 65)
                          between points whose roots are ιs, point variables of enclosing boxes
                          or point constants. □(∀ιs. ∗ ⊸^u T) abbreviates C = ∅.
                          C holds at xs in W when every fact of C[xs/ιs] holds in W.
                          Written with set-builder notation, e.g.
                            { ι+k ≺ ι′+k,  ι′+k ≺ ι+k+1  ∣  k ∈ ℕ }          request and reply
                          Only positive facts: they persist along W ⊑ W′, so V-Box is monotone.
                          A fact x ⊀ y would not persist. An unsatisfiable C is harmless, its box
                          is never forced.
           | □(∀ιs αs. C. ∗ ⊸^u T) | ∃ιs≽ℓ. C. T          (K6, K7, sharp edges 73)
                          A box binds session variables αs next to its ιs. αs occur in session
                          positions only. The existential binds points, carries a lower bound ℓ
                          (heads(∃ιs≽ℓ. C. T) = {ℓ} for a point ℓ, ∅ otherwise, with the ⊥ flag
                          for ℓ = ⊥) and a positive constraint C as for boxes. ∃ιs. C. T leaves
                          an absent bound out.
                          Rocq: TBox n k C T, TEx ℓ n C T.
u    ::= ι, optional      upper point: the call blocks at most at u. An arrow without u never
                          blocks. A function that may block anywhere gets a point variable.
ℓ    ::= ι, optional      lower point: the closure holds only at or above ℓ. An arrow without ℓ
                          holds nothing. T ⊸^u U, T ⊸_ℓ U and T ⊸ U leave the absent bounds out.
                          Rocq: option point for both (sharp edges 149).
lower bound of ∃          absent (holds nothing, Rocq LNone), a point ι (Rocq LPt), or ⊥
                          (Rocq LBot). ⊥ is the unknown point: the value holds channels at points
                          not known from outside, and no point lies below ⊥. ⊥ has no other meaning.
S    ::= Skip | S;S | ?P | !P | ⊕(S, S) | &(S, S) | Close | μX.S | X | X̄
                                                                       session types, unannotated (K1, sharp edges 72)
                          Send and receive have no continuation, choice is binary.
                          The relation reads only the head normal form unr(S) (Thiemann and Vasconcelos,
                          Lemma 3.8): Skip | !P;S′ | ?P;S′ | ⊕(S₁, S₂) | &(S₁, S₂) | Close | X;S′ | X̄;S′.
                          !P reads as !P;Skip, ⊕(S₁, S₂);S as ⊕(S₁;S, S₂;S), Close;S as Close (K2).
                          unr counts fuel (Rocq unfoldS). A type without a head (not contractive)
                          relates nothing, as μX.X did before.
                          ≈ is bisimilarity on heads: Skip;S ≈ S, S;Skip ≈ S, (S₁;S₂);S₃ ≈ S₁;(S₂;S₃),
                          ⊕(S₁, S₂);S ≈ ⊕(S₁;S, S₂;S), μX.S ≈ S[μX.S/X] for contractive types (K3).
                          Duality is pointwise: !P ↔ ?P, ⊕ ↔ &, dual(S₁;S₂) = dual S₁; dual S₂, X ↔ X̄.
P    ::= ∃ιs. T           payload, all points of T bound                sugar: !(S₁ ⊗ S₂).S binds them implicitly
x, ι ::= (p, s, b)        a point, the instant b of the end of polarity s at root p (end points)
x̄    ≔ (p, ¬s, b)        the partner point; x̄̄ = x, (x+n)‾ = x̄+n, x̄[i] = x[i]
p    ::= a | ι-variable | x[i]        root: point constant, bound point variable, payload point
x[i]                       i ≥ 0: the payload point, the point of the i-th channel (from 0) carried by
                          the message of the action that leaves x. A choice at x continues at x[i]
                          for branch i (K11, sharp edges 142): the branching end at x[i], the
                          selecting end at its partner (x[i])‾. As a point, x[i] also stands for
                          (x[i], +, 0). Both ends compute the same payload point, x̄[i] = x[i].
x + n ≔ (p, b + n)  for x = (p, b)
         (c,k)[0] reads "the first channel carried by c's message at its action k", and
         (c,k)[0] + 2 is that channel after two of its own actions.
         Why x[i] exists (sharp edges 5): a receiver plans the order of a channel it has
         not received yet, without knowing which channel the sender picks. It names the arriving
         channel by its position in the message. The sender must put the channel it sends at
         that point, by aliasing its point there or by creating it there with new. The world
         records both sides, so P-Connect checks that they agree.
         Neither types nor worlds mention channel names (sharp edges 27, 37). Channels occur only
         as keys of environments. Renaming channels changes no type and no world.

Σ    ::= · | c : S@x | Σ, Σ                       process level, a finite map,  x a ground point,
                                                  c's current instant; each action on c moves x to x+1
Θ    ::= Σ | Θ, c : S@x, c : S′@x̄                  term level, may hold both ends,  S ⊥ S′, at dual points
Δ    ::= · | x : T | Δ, Δ
prim ∗,  prim T ⊗ U,  prim T + U,  prim □T if prim T     (as in the paper)

heads(∗) = heads(□σ) = ∅      heads(S@ι) = {ῑ}      heads(T ⊸^u_ℓ U) = {ℓ}, ∅ without ℓ
heads(T ⊗ U) = heads(T + U) = heads(T) ∪ heads(U)
heads(c : S@x) = {x̄}         heads(Σ, Δ) = ⋃ heads of the entries
                             (end points: the head of an end is its partner point)
```

- ∀ appears only directly under □ (never on linear functions, never inside session types).
- Points are the only names in the order. Facts may place them anywhere. A value c of type S@ι needs ι ≡ the point of c's entry.

## 5  Worlds

```
carrier     instants (p, b),  p a point constant or a payload point x[i] of one. No channel names.
W = (≡, ≺)  ≡ equivalence (aliases),  ≺ strict partial order on ≡-classes
            ⊇ program order (p, b) ≺ (p, b+1) for every name p
            ⊇ x ≺ x̄+1 for every point x (end points: an end acts before its partner's next action)
successor congruence   x ≡ y  ⇒  x+1 ≡ y+1     (aliased instants stay aliased)
payload congruence     x ≡ y  ⇒  x[i] ≡ y[i]      (equal instants carry the same message)
dual congruence        x ≡ y  ⇒  x̄ ≡ ȳ           (end points, wf_eq_dual)
x ≼ y       x ≺ y or x ≡ y
F ≺ F′      every element of F is ≺ every element of F′       (no point lies below ⊥)

W ⊑ W′      ≡ ⊆ ≡′,  ≺ ⊆ ≺′,  W′ strict                        (Kripke order)
W ⊑ₒ W′     W ⊑ W′ and W′ adds nothing between old instants    (only at new)
W₁ ⊔ W₂     (≡₁ ∪ ≡₂)* with (≺₁ ∪ ≺₂)⁺ on the classes
```

## 6  Readiness and futures

```
entries(Θ)   one entry per end:  c : S@x  (twice for a channel whose both ends Θ holds)
offered(x)   = the entries selected by the labels of x's transitions     x a term or a process
               c!v selects the entry of c whose type unfolds to !…,  c?v the one with ?…,
               c◁i the one with ⊕…,  c▷i the one with &…,
               c! the first Close entry (Rocq),  c↔d the entries of c and d
stable(t)    = no t —λ→ t′ with λ ∈ {β, (νc), ⇑v}        stable(p) = no p —τ→ p′
link(t)      = some t —c↔d→ t′                            link(p) = some p —c↔d→ p′

ready_W(Θ ∣ F, t) ≔ stable(t) ⇒                                          terms (sharp edges 63, 68)
                      (offered(t) = ∅  ⇒  t is a value)
                    ∧ (link(t)  ∨  ∀o ∈ offered(t).  ∀y ∈ heads(entries(Θ) ∖ offered(t)) ∪ F.  head(o) ≺_W y)
                      (heads of entries are partner points: head(o) ≺_W x̄ for a held c : S@x)

ready_W(Σ, p) ≔ stable(p) ⇒                                              processes (sharp edges 68)
                  link(p)
                ∨ ((offered(p) = ∅  ⇒  p is terminated)
                   ∧ ∀e ∈ entries(Σ) ∖ offered(p).  ∃o ∈ offered(p).  head(o) ≺_W (head(e))‾)
```

Link does not block (sharp edges 68). P-Act-Link fires it as a τ once one of
its channels is restricted, and a closed process restricts every channel. So a
term or process with a link redex is ready and compares nothing. A link label
still selects its entries, so the first conjunct of the term form asks an
entry of Θ for the link. The process form exempts the whole process. A thread
K[link ⟨c, d⟩] that also holds e gives P-Term no offered entry below e, so an
exemption of the link entries alone would fail P-Term. In a stable composite a
component's link redex touches no restricted channel, or it would fire. It is
therefore a link redex of the composite, and without one the components meet
the old condition.

A term offers the entries of one redex, so its readiness can ask every offered
head below every other head and below the future F, the points the context still
has to use. A process offers the redexes of all its threads at once, and two
threads may offer at unrelated points. Its readiness therefore asks only some
offered head below each held one, and it has no future (sharp edges 63).

The future F of a thread is the set of partner points of the ends it still
holds, and the future variables of its callers. A blocking action at u checks
u ≺ F. A deadlock is a cycle of threads, each blocked at the point of one end
while it holds another end whose partner the next thread blocks on, and the
check u ≺ F turns such a cycle into a cycle of ≺. With end points the
blocked end with the least point u has its partner at ū. If that partner is
blocked at w it owes w ≺ u, against the choice of u, and otherwise it offers
the dual action (ReadyChain.v).

ready counts entries, not names: a thread holding both ends of c, at x and
x̄, and blocking on the first must hold the second entry not offered, so it
needs x ≺ x̄̄ = x, which fails. Two threads holding one end each are both
offered and can synchronize, so that state is not stable.

## 7  Logical relation   V^W_n⟦Σ ⊢ T⟧,  E^W_n⟦Θ ⊢ T ≺ F⟧,  P^W_n⟦Σ ⊢ T⟧

```
V-Unit    ∗ ∈ V^W_n⟦· ⊢ ∗⟧
V-Chan    c ∈ V^W_n⟦c : S@x ⊢ S′@y⟧            if S ≈ S′ and x ≡_W y
V-Const   k ∈ V^W_n⟦· ⊢ T⟧                     if k : T₀ (instance of its signature) and T₀ ≈_W T
          (≈_W: ≈ with ground points compared up to ≡_W; needed for Type point conversion)
          (new's ι must be known to W, its root in the support, so that O-New can alias
           the created point to it; sharp edges 49)
V-Pair    v₁ ∈ V^W_n⟦Σ₁ ⊢ T⟧   v₂ ∈ V^W_n⟦Σ₂ ⊢ U⟧   ⇒   ⟨v₁, v₂⟩ ∈ V^W_n⟦Σ₁, Σ₂ ⊢ T ⊗ U⟧
V-Inj     v ∈ V^W_n⟦Σ ⊢ Tᵢ⟧   ⇒   injᵢ v ∈ V^W_n⟦Σ ⊢ T₁ + T₂⟧
V-Abs     fchans(t) = dom Σ        {ℓ} ≼_W heads(Σ)
          ∀W′ ⊒ W, j < n, Σ′, v ∈ V^{W′}_j⟦Σ′ ⊢ T⟧, F with {u} ≺_{W′} F.
              t[v/x] ∈ E^{W′}_j⟦Σ, Σ′ ⊢ U ≺ F⟧
          ⇒   λx.t ∈ V^W_n⟦Σ ⊢ T ⊸^u_ℓ U⟧
V-Box     fchans(t) = ∅     ∀W′ ⊒ W, xs known to W′ with C[xs/ιs] holding in W′.
              λ_. fix x.t ∈ V^{W′}_n⟦· ⊢ (∗ ⊸^u T)[xs/ιs]⟧
          ⇒   !(x = t) ∈ V^W_n⟦· ⊢ □(∀ιs. C. ∗ ⊸^u T)⟧                  (sharp edges 58, 63, 65)
          (V of the thunk at every admissible instance. Unfolded by V-Abs, this is fix x.t in
           E^{W′}_j at every j < n and every F with {u[xs/ιs]} ≺_{W′} F, the box of sharp edges 52.
           Rocq: Vrel_box_iff, unfolded in Vrel_box_thunk_iff)
          (C[xs/ιs] in W′: every fact x ≺ y of C holds as x[xs/ιs] ≺_{W′} y[xs/ιs], every fact
           x ≡ y as x[xs/ιs] ≡_{W′} y[xs/ιs]. Monotone along ⊑ because C is positive)
          (≈_W relates two constraints when each fact of one has a fact of the other with
           points up to ≡_W)
V-Box with αs  as V-Box, and in addition at every list ss of hereditarily contractive session
          types for the αs, with the thunk in V at (∗ ⊸^u T)[xs/ιs][ss/αs]. The instances need
          not be closed. Box bodies with αs compare by ≈_W with session types on the nose
          (teqW_r), because ≈ of open session types is not closed under instances (sharp edges 73)
V-Ex      {ℓ} ≼_W heads(Σ)    xs known to W,  C[xs/ιs] holds in W,  v ∈ V^W_n⟦Σ ⊢ T[xs/ιs]⟧
          ⇒   v ∈ V^W_n⟦Σ ⊢ ∃ιs≽ℓ. C. T⟧                                       (K7, sharp edges 73)
          (Rocq: Vrel_ex_iff. Vdef carries a point substitution so that the clause stays
           structural)

payload at x           P[x] ≔ T[x[0], …, x[m−1] / ι₀, …, ιₘ₋₁]  for P = ∃ι₀ … ιₘ₋₁. T and c : S@x.
                       A plain substitution, no quantifier on either side. The sender's channels
                       satisfy it up to ≡ (V-Chan), so the sender must have put them at the payload points.
names                  one sort, points. Worlds and environments use ground points (constants and their
                       payload points x[i]). Static types also use bound point variables.

E-Zero    t ∈ E^W_0⟦Θ ⊢ T ≺ F⟧
E-Stop    v ∈ V^W_{n+1}⟦Θ ⊢ T⟧   ⇒   v ∈ E^W_{n+1}⟦Θ ⊢ T ≺ F⟧
E-Step    ¬irred t    ready_W(Θ ∣ F, t)
          ∀λ, t′.  t —λ→ t′  ⇒  Θ ⊩ⁿ_W t —λ→ t′ : T ≺ F
          ⇒   t ∈ E^W_{n+1}⟦Θ ⊢ T ≺ F⟧

Giving steps keep the index (sharp edges 45)
          send, select, close and link are giving steps. Their obligations (O-Send, O-Select,
          O-Close, O-Link, Q-Send, Q-Select, Q-Close, Q-Link, and Q-Tau for the τ of P-Act-Link)
          state the successor at n+1, the index of the step itself. β, new, spawn, receive,
          branch and a synchronization
          (τ of P-Act-Session or P-Act-Close) cost one. E_{n+1} and P_{n+1} are least fixpoints over giving
          steps at fixed n+1, over E_n and P_n. Giving steps are well founded because each lowers
          the syntactic size of the term (summed over the soup for processes, Rocq).
          In the clauses below, read the continuation index of a giving step as n+1.
          The giving clause for the τ of P-Act-Link keeps the world (W′ = W), because a link
          creates no points. Rocq encodes E_{n+1} and P_{n+1} as inductive predicates (Eind, Pind)
          over the level-n relations, with induction principles Erel_S_ind and Prel_S_ind.

O-Beta    t′ ∈ E^W_n⟦Θ ⊢ T ≺ F⟧
O-New     ∃a ∉ names(W) ∪ points(Θ, T, F), S ⊥ S′, W′ ⊒ₒ W placing a.   t′ ∈ E^{W′}_n⟦Θ, c : S@a, c : S′@ā ⊢ T ≺ F⟧
          (the created channel name needs no condition, only its point is fresh)
O-Spawn   Θ = Θ₁, Θ₂     v ∈ V^W_{n+1}⟦Θ₁ ⊢ ∗ ⊸^u_ℓ ∗⟧     t′ ∈ E^W_n⟦Θ₂ ⊢ T ≺ F⟧
          (Every "Θ = Θ₁, c : S@x" below reads the head unr(S); c : (!P;S′)@x means unr(S) = !P;S′.)
O-Send    Θ = Θ₁, Θ₂, c : (!P;S)@x     v ∈ V^W_{n+1}⟦Θ₂ ⊢ P[x]⟧
          t′ ∈ E^W_n⟦Θ₁, c : S@(x+1) ⊢ T ≺ F⟧
O-Recv    Θ = Θ₁, c : (?P;S)@x
          ∀W′ ⊒ W, j ≤ n, Σ₂, v ∈ V^{W′}_j⟦Σ₂ ⊢ P[x]⟧,  (Θ₁, c : S@(x+1)), Σ₂ defined.
              t′ ∈ E^{W′}_j⟦(Θ₁, c : S@(x+1)), Σ₂ ⊢ T ≺ F⟧
          (the payload is composed with the continuation, so a returning end of c must be
           dual to it at a dual point; sharp edges 43)
          (Θ may then hold both ends of a received channel; Θ₁, Σ₂ is defined when every
           overlap is a pair of dual ends at ≡_{W′} points. Every overlap condition of the
           relation reads ≡_W, never equality of points: sharp edges 40)
O-Close   Θ = Θ₁, c : Close@x      t′ ∈ E^W_n⟦Θ₁ ⊢ T ≺ F⟧
O-Select  Θ = Θ₁, c : ⊕(S₁, S₂)@x   t —c◁i→ t′   t′ ∈ E^W_{n+1}⟦Θ₁, c : Sᵢ@(x[i])‾ ⊢ T ≺ F⟧   (giving, like send; sel_pt)
O-Branch  Θ = Θ₁, c : &(S₁, S₂)@x   t —c▷i→ t′   t′ ∈ E^W_n⟦Θ₁, c : Sᵢ@x[i] ⊢ T ≺ F⟧     (bra_pt)
          (costs one, like receive. No payload arrives, so it is stated at W, not at every W′ ⊒ W.
           A choice continues at the payload point x[i] of branch i (K11, sharp edges 142), every
           other action at x+1. Skip and ; move nothing, because unr removes them before a clause
           reads the head. K4, K5, sharp edges 72)
O-Link    Θ = Θ₁, c : S@x, d : S′@y    S ⊥ S′    x ≡_W ȳ    t′ ∈ E^W_n⟦Θ₁ ⊢ T ≺ F⟧
          (c = d allowed: a self-link, Θ holds both ends of c, both entries leave Θ.
           Matches P-Act-Link with c = d, which releases c. `link (new ∗)` is typable.)
          (Θ₁ may keep the other end of c or d. A link compares nothing in readiness, so the
           context of a link may hold that end, and Erel_bind passes it through by
           comp_ext_gen. `let (c₁, c₂) = new ∗ in let () = link ⟨c₁, d⟩ in close c₂` is typable.
           Sharp edges 68)

P-Zero    p ∈ P^W_0⟦Σ ⊢ T⟧
P-Stop    v ∈ V^W_{n+1}⟦Σ ⊢ T⟧   ⇒   (∅, {v, ∗, …, ∗}) ∈ P^W_{n+1}⟦Σ ⊢ T⟧
P-Step    ¬irred p    ready_W(Σ, p)
          ∀π, p′.  p —π→ p′  ⇒  Σ ⊩ⁿ_W p —π→ p′ : T
          ⇒   p ∈ P^W_{n+1}⟦Σ ⊢ T⟧

Every clause is stated for the successor itself. Restricted channels carry no facts,
because worlds speak about points only, so the environment's world cannot pin anything on
them.

Q-Tau     p —τ→ p′    p′.1 # dom Σ  ⇒  ∃W′ ⊒ₒ W.   p′ ∈ P^{W′}_n⟦Σ ⊢ T⟧
          (W′ places the points N of channels the step creates, N # names(W) ∪ points(Σ, T).
           The paper's Q-Tau is W′ = W.)
          (The τ of P-Act-Link keeps W. Before it fires, p is ready by its link redex alone,
           so no fact about the link's channels is ever asked. Sharp edges 68)
Q-Recv    Σ = Σ₁, c : (?P;S)@x     p —c?v→ (C′, E′)
          ∀W′ ⊒ W, j ≤ n, Σ₂ # p.1, v ∈ V^{W′}_j⟦Σ₂ ⊢ P[x]⟧,  Σ₂ dual to (Σ₁, c : S@(x+1)) on their overlap B.
              (C′ ∪ B, E′) ∈ P^{W′}_j⟦(Σ₁, c : S@(x+1)) ∖ B, Σ₂ ∖ B ⊢ T⟧
          (B = channels whose other end the receiver already holds. The obligation is stated
           for the successor with B restricted; the LTS itself does not restrict. If the carrier c
           itself is in B (an end of c was sent over c), its continuation entry leaves Σ as well.
           Σ₂ is a term-level environment: a payload may carry both ends of one channel; such a
           channel also belongs to B and is restricted in the continuation.
           The guard c ∉ dom Σ₂ of the paper is dropped (c may be in B).
           Lemma needed: restricting B only removes external steps on channels no environment holds.)
Q-Send    Σ = Σ₀, Σ_v, c : (!P;S)@x      dom Σ_e = fchans(v) ∩ C
          ∃Σ_e, Σ_e′ (points chosen by the obligation).
          v ∈ V^W_{n+1}⟦Σ_v, Σ_e′ ⊢ P[x]⟧      p′ ∈ P^W_n⟦Σ₀, Σ_e, c : S@(x+1) ⊢ T⟧
          Σ_e′ = ends of dom Σ_e that leave with v,   Σ_e = ends that stay,
          the two dual at dual points (send_split)
          (both ends of a restricted channel may leave with v; then it has no entry in Σ_e)

Obligations whose continuation environment cannot be formed (e.g. Θ already holds both
ends of c) fail; such a thread is never ready anyway.
Q-Close   Σ = Σ₁, c : Close@x      p′ ∈ P^W_n⟦Σ₁ ⊢ T⟧
Q-Select  Σ = Σ₁, c : ⊕(S₁, S₂)@x   p —c◁i→ p′   p′ ∈ P^W_{n+1}⟦Σ₁, c : Sᵢ@(x[i])‾ ⊢ T⟧   (giving)
Q-Branch  Σ = Σ₁, c : &(S₁, S₂)@x   p —c▷i→ p′   p′ ∈ P^W_n⟦Σ₁, c : Sᵢ@x[i] ⊢ T⟧
Q-Link    c ≠ d    Σ = Σ₁, c : S@x, d : S′@y    S ⊥ S′    x ≡_W ȳ    p′ ∈ P^W_n⟦Σ₁ ⊢ T⟧
          (c = d cannot reach the interface: process-level Σ holds one end per channel)
          (a process waiting at an interface link is ready by link(p), sharp edges 68)
```

## 8  Semantic judgments

```
Θ; Δ ⊨^F_W t : T   ≔   ∀n, W′ ⊒ W, Θ′, γ ∈ G^{W′}_n⟦Θ′; Δ⟧, (Θ, Θ′) defined in W′.   tγ ∈ E^{W′}_n⟦Θ, Θ′ ⊢ T ≺ F⟧
                       (Θ, Θ′ composes, dual ends at dual points up to ≡_{W′} allowed: a bound value may hold
                        the other end of a channel of Θ; sharp edges 50)
Σ ⊨_W p : T        ≔   ∀n.  p ∈ P^W_n⟦Σ ⊢ T⟧
Θ; Δ ⊨_W t : T     ≔   Θ; Δ ⊨^∅_W t : T                  (the paper's judgement, plus ready)
```

## 9  Static typing   Θ ; Γ ; Δ ⊢_F t : T

There is one term judgment (`typed`, static/Typing.v). Its fact context
Γ = (W, Ψ, Φ) holds the ground facts W between point constants, the
hypotheses Ψ and the future hypotheses Φ. A source program is the instance
Θ = ∅, W = ∅ (`styped`, static/Source.v, the definition
`typed wnil Φ Ψ ∅ Δ F t T`), so its Γ mentions no constant. P-Term types a
running thread with the world of the configuration as the ground part of Γ,
and E-Ch reads Θ. Soundness asks the ground part acyclic (strictness of W,
or C₀ a creation constraint against ∅ for a source program). The hypotheses
Ψ may be inconsistent in dead code. `typed_world_transfer` moves a
derivation with Θ = ∅ between a world of empty support and any world.

```
W          a well-formed world over point constants, the index of the judgment
Ψ          hypotheses (C, xs) of the enclosing boxes (E-Exp below)
Φ          future hypotheses u ≺ φ of the enclosing λs and boxes (E-Abs, E-Exp)
Γ ⊢ a ≺ b, Γ ⊢ x ≡ y
           the one fact theory, Γ = (W, Ψ, Φ), a and b points or future variables (sharp edges 64, 65).
           Generators: the facts of W,  every fact of C[xs/ιs] for a hypothesis (C, xs) in Ψ,
           u ≺ φ for every future hypothesis. ≡ is the least congruence (successor, payload and
           partner point, se_dual) containing the ≡ generators. ≺ contains program order,
           x ≺ x+1 and x ≺ x̄+1 (fl_po, fl_dpo), and the ≺ generators, and is
           closed under ≡ and under transitivity through points. With Ψ = Φ = ∅ it is W
           (the ground case). Side conditions are entailments, with no decision procedure
           asked for (§16).
           One lemma carries a derivation along a map of the generators. It gives point
           substitution (typed_pinst) and future instantiation into a world (typed_sem_rules).
≺_Γ, ≡_Γ   Γ ⊢ x ≺ y and Γ ⊢ x ≡ y between points. They do not depend on Φ. Every comparison
           of points in the static system reads them: E-Ch, link, E-Conv (which moves the payload
           of send and recv), duality of composed ends.
{u} ≺ F    Γ ⊢ u ≺ a for every point and the future variable a of F.
known      a point is known when W knows it or its root is a root of an instance point of a
           hypothesis in Ψ (sharp edges 59).

Constants are constrained type-indexed schemes (sharp edges 147). An instance of a
signature is a type T, a constraint G and a list of points that must be known. G is a set of
facts over ≺ and ≡ that the meta level computes from T. heads stays a meta-level function.
No signature reads the order.

            type                                                 constraint G
spawn  : (∗ ⊸^u_ℓ ∗) ⊸ ∗                                       ∅
send   : (P[ι] ⊗ (!P;S)@ι) ⊸^ι S@(ι+1)                        {ι ≺ h ∣ h ∈ heads(P[ι])}, no instance
                                                                 when P[ι] carries the ⊥ flag
recv   : (?P;S)@ι ⊸^ι P[ι] ⊗ S@(ι+1)                          ∅
selectᵢ : ⊕(S₁, S₂)@ι ⊸^ι Sᵢ@(ι[i])‾                          {ι ≺ ι[i]}              (K11, end points)
branch : &(S₁, S₂)@ι ⊸^ι S₁@ι[0] + S₂@ι[1]                     {ι ≺ (ι[0])‾, ι ≺ (ι[1])‾}    (case dispatches)
         (each constraint puts ι below the heads of the result; the selecting end continues
          at the partner of the branching end, as in the encoding of choice)
close  : Close@ι ⊸^ι ∗                                          ∅
link   : S@ι ⊗ dual S@ι′ ⊸ ∗                                    {ι ≡ ι̅′}  (the two ends at dual points)
         (link never blocks, so E-App asks no future fact for it. The paper's link has no
          order at all, sharp edges 68)
force  : □(∀ιs αs. C. ∗ ⊸^u T) ⊸^{u[ιs′/ιs]} T[ιs′/ιs][ss/αs]   C[ιs′/ιs], with ιs′ known and
                                                                 every s ∈ ss hereditarily contractive
         (force applies the thunk. Its upper point is the thunk's, instantiated. sharp edges 58, 63, 65, 73)

new is the one constant outside the schemes. It creates a fresh point and has no witness to
instantiate, so its premise is that C is a creation constraint over the context with known
outer points (sharp edges 97, 103, 105).

new    : ∗ ⊸ ∃ι≽⊥. C. S@ι ⊗ dual S@ῑ        creation_ok 1 Γ C: C is acyclic and conservative over Γ,
                                             every outer point of C known

Rocq: konst_sig k T G xs is the table of schemes, konst_ty has the constructors KTSig (a scheme
whose G holds and whose xs are known) and KTNewEx. KTSpawn, …, KTForce are the instances as
lemmas, and konst_ty_case is case analysis by constant.

E-Unit     ·; · ⊢^F ∗ : ∗
E-Const    (T, G, xs) an instance of k    Γ ⊢ G    xs known   ⇒   ·; · ⊢^F k : T
           (Γ ⊢ G asks every fact of G, as force asks C[ιs′/ιs]. For new the premise is creation_ok)
E-LVar     ·; x : T ⊢^F x : T
E-Ch       c : S@ι; · ⊢^F c : S@ι′       with ι′ ≡_Γ ι
E-Abs      Θ; Δ, x : T ⊢^{{μ}} t : U      μ a fresh future variable, only hypothesis u ≺ μ (sharp edges 56)
           {ℓ} ≼_Γ heads(Θ, Δ)  (Rocq asks no freshness of ℓ)
           ⇒   Θ; Δ ⊢^F λx.t : T ⊸^u_ℓ U
E-App      Θ₁; Δ₁ ⊢^{F ∪ heads(Θ₂, Δ₂)} t₁ : T ⊸^u_ℓ U     Θ₂; Δ₂ ⊢^{F ∪ {ℓ}} t₂ : T     {u} ≺_Γ F
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
E-Exp      ·; □Δ, x : □(∀ιs. C. ∗ ⊸^u T) ⊢^{μ}_{Ψ, (C,ιs)} t : T   (μ a fresh future variable, only u ≺ μ)
           ⇒   ·; □Δ ⊢^F_Ψ !(x = t) : □(∀ιs. C. ∗ ⊸^u T)                   (sharp edges 57, 58, 63, 65)
           Ψ: the constraints of the enclosing boxes with their instances, hypotheses (C, xs).
           Every side condition of the static system is read in Γ (58, 64, 65).
           Recursion needs no rule of its own. A recursive call is a force of x at some ιs′,
           and Γ ⊢ C[ιs′/ιs] holds whenever C[ιs′/ιs] ⊆ C, through the body's own hypothesis
           (C, ιs). C is then an invariant of the recursion: it states the facts of every
           round at once, because the body cannot derive the facts of the next round from
           those of the current one. ι ≺ ι′ does not give ι+1 ≺ ι′+1 (rr_call_underivable).
           ιs are point variables in the premise, typed once (57). E-Const at send and recv asks
           the payload ∃ιs.T to have no free point variable beyond ιs, the "all points of T bound" of §4 (57)
E-Exp with αs  the premise of E-Exp at every list ss of hereditarily contractive session types,
           at type T[ss/αs], infinitary in ss (sharp edges 73). force instantiates the αs at such
           an ss and returns T[ιs′/ιs][ss/αs]
E-Pack     Θ; Δ ⊢^F t : T[xs/ιs]    xs known    Γ ⊢ C[xs/ιs]    Γ ⊢ {ℓ} ≼ heads(T[xs/ιs])
           ⇒   Θ; Δ ⊢^F t : ∃ιs≽ℓ. C. T                                         (sharp edges 73)
E-Open     Θ; Δ, x : T, Δ′ ⊢^F_{Ψ, (C,ιs)} t : U    ιs fresh    T not unlimited
           ⇒   Θ; Δ, x : ∃ιs≽ℓ. C. T, Δ′ ⊢^F_Ψ t : U                             (sharp edges 73)
           (a rule on the environment, no term former. Rocq: t_open shifts Φ, Ψ, Θ, Δ, F and U)
E-Weak, E-Contract   as in the paper, with ⊢^F
E-Conv     Θ; Δ ⊢^F t : T     T ≈_Γ T′   ⇒   Θ; Δ ⊢^F t : T′               (sharp edges 67)
           (≈ on session types is the bisimilarity of §4, so E-Conv applies the laws of ; and μ)
           ≈_Γ is ≈ with the points of session types and the points u, ℓ of arrows compared
           by ≡_Γ. Boxes are compared by ≈ with their points unchanged, because their points
           live under the binder of their ιs. With ≡_Γ replaced by equality it is the paper's
           rule. Soundness: under an instance whose hypotheses hold in W₁, ≡_Γ maps into ≡ of W₁,
           and type point conversion (§10) transports V, E and P along ≈_W₁.

P-Term     prim T    Σ, Θ_B; · ⊢^∅ t : T    Θ_B = both ends of every channel in C₀, dual at dual points
           ⇒   Σ ⊢_W (C₀, {t}) : T
P-Connect  Σ₁, Σ_C ⊢_W (C₁, E₁) : T    Σ₂, Σ_C′ ⊢_W (C₂, E₂) : ∗    Σ_C ⊥ Σ_C′ over C₀ (possibly ∅),
           dual at dual points: x ≡_W ȳ for c : S@x ∈ Σ_C and c : S′@y ∈ Σ_C′
           ⇒   Σ₁, Σ₂ ⊢_W (C₁ ⊍ C₂ ⊍ C₀, E₁ ⊎ E₂) : T
```

## 10  Lemmas: LTS and worlds

```
Harmony                          p —τ→ p′  ⇔  p ⟶ p′                       unchanged
Internalizing communication      the paper's, generalized to a cut C₀
Restriction of returning channels
                  in the P-Connect proof the composite's successor equals the receiving component's
                  successor with B restricted, because B already lies in the cut C₀
Internalizing a close            unchanged
Internalizing a link             unchanged (the paper's, world fixed)

Amalgamation      W₁, W₂ strict  ⇒  (W₁ ⊔ W₂ strict  ⇔  (W₁|_A ⊔ W₂|_A) strict),   A = points W₁ and W₂ share
Fresh extension   W₁ ⊑ₒ W₁′ placing points N,  N # names(W₂),  W₂ strict,  W₁ ⊔ W₂ strict
                  ⇒   W₁′ ⊔ W₂ strict
Monotonicity      W ⊑ W′  ⇒  V/E/P^W ⊆ V/E/P^{W′}      (needs world_wf W. P needs no
                  restriction, because no fact can mention a restricted channel)
Renaming channels the paper's invariance/ChannelRenaming.v and invariance/JunkRenaming.v, with the world fixed                       unchanged
Renaming points   a bijective renaming of point constants applied to the world, the environment
                  and the types preserves V, E and P (P-Connect's new case renames a component's
                  fresh point away from the other world)
Type point conversion  ι ≡_W ι′ ⇒ V/E/P with ι in a type ⇔ with ι′ in its place
                  (send and recv use it to move between P[x] and the sender's own points)
Entry conversion  x ≡_W y  ⇒  (t ∈ E^W_n⟦Θ, c : S@x ⊢ T ≺ F⟧ ⇔ t ∈ E^W_n⟦Θ, c : S@y ⊢ T ≺ F⟧),
                  likewise for P (P-Term's link case; uses payload congruence for payloads)
Future weakening   F′ ⊆ F  ⇒  E^W_n⟦Θ ⊢ T ≺ F⟧ ⊆ E^W_n⟦Θ ⊢ T ≺ F′⟧
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
E-Exp       ∀xs known with C[xs/ιs], F′ with {u[xs/ιs]} ≺ F′.
                ·; □Δ, x : □(∀ιs. C. ∗ ⊸^u T) ⊨^{F′} t : T[xs/ιs]
            fchans(t) = ∅     fv(t) ⊆ dom(□Δ, x)
            ⇒   ·; □Δ ⊨^F !(x = t) : □(∀ιs. C. ∗ ⊸^u T)                  (sharp edges 58, 63, 65)
E-Force     Θ; Δ ⊨^F t : □(∀ιs. C. ∗ ⊸^u T)    xs known, C[xs/ιs]    {u[xs/ιs]} ≺ F
            ⇒   Θ; Δ ⊨^F force t : T[xs/ιs]
            (with αs, E-Exp and E-Force take every hereditarily contractive ss as well,
             sem_typed_box and sem_typed_force)
E-Pack      Θ; Δ ⊨^F t : T[xs/ιs]    xs known, C[xs/ιs]    {ℓ} ≼ heads(T[xs/ιs])
            ⇒   Θ; Δ ⊨^F t : ∃ιs≽ℓ. C. T                     (sem_typed_pack, via Erel_Vsub)
E-Open      Δ(x) = ∃ιs≽ℓ. C. T    ∀W′ ⊒ W, xs known to W′ with C[xs/ιs].
                Θ; Δ[x : T[xs/ιs]] ⊨^F_{W′} t : U
            ⇒   Θ; Δ ⊨^F t : U                                (sem_typed_open)
E-Weak      Θ; Δ ⊨^F t : U   ⇒   Θ; Δ, x : □T ⊨^F t : U
E-Contract  Θ; Δ, x : □T, y : □T ⊨^F t : U   ⇒   Θ; Δ, x : □T ⊨^F t[x/y] : U
E-Conv      Θ; Δ ⊨^F t : T,   T ≈_W T′   ⇒   Θ; Δ ⊨^F t : T′          (sharp edges 67)
            Rocq: the elimination rules go through Erel_bind (rules/Bind.v, sharp edges 48). The hole runs
            under future F ∪ H, where every entry of the context's environment lies at or above H.
            The semantic condition behind H: the environment of v ∈ V⟦Θ ⊢ T⟧ lies at or above
            heads(T) (Vrel_heads_above, rules/TermRules.v), and a grounding's environment at or above
            heads(Δ) (grounding_heads). Typing then needs nothing extra.
            H keeps a redex of the hole off the context's channels (subjs_free) for every redex
            but a link. A link may act on the other end of a channel the context holds, and the
            link case moves that end with comp_ext_gen (sharp edges 68). Erel_app_link proves the
            constant without an upper point and asks nothing of F.
            Proved in rules/TermRules.v: sem_typed_unit, sem_typed_konst, sem_typed_var, sem_typed_chan,
            sem_typed_lam (E-Abs; premise for every later world W₁ and F′ with {u} ≺_{W₁} F′),
            sem_typed_inj1/2, sem_typed_letu, sem_typed_letp, sem_typed_case, sem_typed_pair,
            sem_typed_wk, and E-App as sem_typed_app_gen from app_good, which Erel_app_noforce
            gives for every function value but force. E-Conv is sem_typed_tconv (invariance/PointConversion.v),
            with sem_typed_teq (invariance/EquivInvariance.v) its case T ≈ T′.
            Proved in rules/BoxRules.v: Erel_app_force, hence app_good_all and E-App for
            every function (sem_typed_app); E-Force (sem_typed_force, at an instance xs with
            {u[xs/ιs]} ≺_W F); E-Exp (sem_typed_box, premise for every later world, xs and F′
            with {u[xs/ιs]} ≺ F′, by induction on the index); E-Contract (sem_typed_contract,
            the two most recent bindings, t[x/y] = rename pred t).

P-Term      prim T,   Σ, Θ_B; · ⊨^∅_W t : T,   Θ_B both ends of C₀
            ⇒   Σ ⊨_W (C₀, {t}) : T
            proof: chain argument over C₀ inside one thread (a thread at a link of an interface
            channel gives link(p), a link of a channel of C₀ fires, sharp edges 68)
            Rocq (sharp edges 47): induction on n, inside on the size of the thread. Proved as
            Prel_term (composition/PTerm.v). Implicit side conditions made explicit there: W strict,
            dom Θ_B = C₀, Θ_B only both-ends entries, dual at dual points up to ≡_W, dom Σ # C₀.
P-Connect   prim T,   Σ₁, Σ_C ⊨_{W₁} (C₁, E₁) : T,   Σ₂, Σ_C′ ⊨_{W₂} (C₂, E₂) : ∗,
            Σ_C ⊥ Σ_C′ over C₀,   C₁ # dom Σ₂,   C₂ # dom Σ₁,   W₁ ⊔ W₂ strict
            ⇒   Σ₁, Σ₂ ⊨_{W₁ ⊔ W₂} (C₁ ⊍ C₂ ⊍ C₀, E₁ ⊎ E₂) : T
            proof: ready by the chain argument across C₀ (a component's link redex is one of the
                   stable composite, else both components meet the old condition, sharp edges 68);
                   τ steps by the Internalizing lemmas,
                   a message instantiates Q-Recv with W₁ ⊔ W₂ (the sender's alias names the payload),
                   new by Fresh extension and Renaming points,  link by Internalizing a link and Entry conversion

            Rocq (sharp edges 46): induction on n, inside on the size of the composite's soup;
            both components in one world W ⊒ W₁, W₂ (monotonicity), one at T, the other at ∗.
            Proved as Prel_connect (composition/PConnect.v). Implicit side conditions made explicit there:
            dom Σ_C = dom Σ_C′ = C₀, cut ends dual at dual points up to ≡ of W₁ ⊔ W₂, W₁ and W₂ well formed,
            Σ₁, Σ₂, Σ_C pairwise disjoint as maps, C₁ # dom Σ₁, C₂ # dom Σ₂, C₁, C₂, C₀ disjoint.
            index (sharp edges 45): components in P at n give the
            composite in P at n. A synchronization of the composite is a giving step of one component
            (free) and a receive, branch or close of the other. A selection meeting a branch across
            the cut moves both cut ends to the chosen branch (cross_choice, sharp edges 72). A link of two cut channels fuses the other ends
            inside one component by Internalizing a link.
Internalizing a link (component level)
            prim T,  p ∈ P^W_n⟦Σ, c : S̄@x, d : S@y⟧,  x ≡_W ȳ   ⇒   (C ∪ {d}, E[d/c]) ∈ P^W_n⟦Σ ⊢ T⟧
            proof: a synchronization on d of the fused process is c!v (free) then d?v of p, a choice
            on d is c◁i (free) then d▷i of p, and a close on d is two closes of p (both free); induction on n, inside on the giving-step
            fixpoint of p; readiness by the chain argument (the two ends are never both offered in a
            stable fused process); prim T rules out a terminated p that returns the two ends.
            A link redex of p on c or d fires in the fused process, any other stays a link redex
            of it (fused_ready, sharp edges 68).

P-Connectⁿ  (corollary, by induction on n using P-Connect; every partial amalgam is a subset of the full one)
            Σᵢ, Σ_Cᵢ ⊨_{Wᵢ} (Cᵢ, Eᵢ) : Tᵢ  (i = 1 … n),  exactly one Tᵢ = T, all others ∗,
            the Σ_Cᵢ together hold both ends of every channel in C₀, each end once, dual,
            W₁ ⊔ … ⊔ Wₙ strict
            ⇒   Σ₁, …, Σₙ ⊨_{W₁ ⊔ … ⊔ Wₙ} (C₁ ⊍ … ⊍ Cₙ ⊍ C₀, E₁ ⊎ … ⊎ Eₙ) : T
            Rocq (sharp edges 55): Prel_connect_n (composition/PConnectN.v). The components move to the
            full amalgam first (monotonicity), then P-Connect folds at that one world
            (Prel_connect_list). The cut ends are dual at ≡ of the full amalgam.
```

## 12  Main results

```
Fundamental     Θ; Δ ⊢^F_W t : T   ⇒   Θ; Δ ⊨^F_W t : T
                Σ ⊢_W p : T        ⇒   Σ ⊨_W p : T
Adequacy        · ⊨_W p : T   ⇒   p deadlock free         (the paper's proof)
Soundness       · ⊢_W p : T,  W strict   ⇒   p deadlock free
Source          creation_ok n ∅ C₀,  prim T,  ·; · ⊢^∅_{(C₀, ιs)} t : T   ⇒   (∅, {t}) deadlock free
```

soundness_source starts a program with n top-level point variables ιs under one constraint
C₀ over them. C₀ is a creation constraint against the empty context, the premise of new at
n variables (sharp edges 148). The empty context knows no point, so C₀ has no outer point, and
it has no fact beyond equality and program order, so conservativity holds for free and
creation_ok n ∅ C₀ is the acyclicity of C₀ with program order (c0_creation_ok).

Rocq state, branch cfst (sharp edges 72). The session types are those of K1, read through
unfoldS = unr with fuel. select₁, select₂ and branch are the schemes KSSel1, KSSel2 and KSBra, the
labels SSel and SBra, the obligations O-Select, O-Branch, Q-Select and Q-Branch (Pchoice_case).
Every composition lemma, adequacy and the fundamental theorems keep their statements. theories/pgv
and theories/pn are out of the build (K9).

Rocq state. Rocq implements sharp edges 65 (sharp edges 66, 297c45f, d3dfbe4). A constraint
is a closure BCs env P, a predicate P on facts over variables closed by its outer points env,
and substitution acts on env. Its roots are the finitely many roots of env. The static ≡ is
seqs W Ψ, and fl_map transfers it together with the static ≺. Rocq writes the payload point x[i]
as pt_payload x i, with positions from 0 as in this file. The paragraphs below
describe the earlier refactors. Where they mention steps and words, sharp edges 66 replaces
them by bcs_open and bcs_hold_sub.

Rocq (static/, sharp edges 53, 56): typed W Φ Θ Δ F e T and ptyped W Σ p T, indexed by the
world W. The fresh μ of E-Abs and E-Exp is a future variable φ with the hypothesis u ≺ φ
in Φ, at the same W. E-Exp types the body once with ιs as point variables 0, …, m−1 and Φ, □Δ
and the recursive binding shifted past them (57). E-Const asks kscoped of send and recv. The
other rules as in §9. typed_pinst substitutes points for point variables. typed_ityped does that
and instantiates φ at any later world into the infinitary judgment of 53. Every well-formed W
is closed under the substitutions at recursive calls, because W knows constants only and
relates points with a variable root by reflexivity and program order.
fundamental (terms), fundamental_proc (processes, P-Connect by Prel_connect with W₁ = W₂ = W),
soundness (strict W, ptyped W ∅ p T ⇒ deadlock_free p, via adequacy). All closed under the
global context.
A future variable needs no lemma about dropping a fresh conservative extension, which is false
at V-Const (sharp edges 54, 56, DropCounter.v).
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
Free constraints (65, 66): a recursive call gets C at its instance ys from the body's
hypothesis by bcs_hold_sub, or by bcs_hold_self when C[ys] ⊆ C. soundness, fundamental,
fundamental_proc, Prel_connect_n and the ten deadlock_free examples of §13 are closed under
the global context.
E-Conv up to ≈_Γ (67): t_conv asks steq W Ψ T T′, and teq_steq gives the old premise.
steq_teqW maps it to ≈_{W₁} under an instance, sr_conv takes ≈_W, and sem_typed_tconv is
rel_tconv in every later world. The forwarder types (fw_deadlock_free). Its world relates
payload points by ≡, so its strictness uses wgen_strict_cong, whose name map respects x ↦ x[i]
without commuting with it. The eleven deadlock_free examples and the four theorems stay closed.
Non-blocking link (68): Readiness.v adds link_t and link_p and the link disjuncts of §6.
konst_ty types link as TLolli None None, and Erel_app_link is ready by its link redex.
ReadyChain.v proves the old chain argument as ready_connect_core for components without a
link redex, and ready_connect lifts a component's link redex by link_l and link_r. ready_term,
fused_ready (Internalize.v) and Prel_S_ready, conn_stop (ConnectCut.v) take the new disjunct.
Bind.v splits subjs_free into subjs_free_br, which reads the comparisons, and subjs_free for
redexes other than a link, and its link case uses comp_ext_gen. The invariance lemmas carry
link_t and link_p along renaming, conversion and monotonicity. No statement of soundness, of
the fundamental theorems, of adequacy or of a composition lemma changed.


## 13  Examples

(c, k) below is the point of c's entry after k actions. The table predates end points.
With end points the second end of c sits at (c, k)‾, and the facts read: cycle has the
thunk's γ̄ ≺ ε and the main thread's γ ≺ ε̄ (examples/Cycle.v), blocked asks γ ≺ ε̄ and
ε̄ ≺ γ, delegation asks the five facts of its creation constraint
{ι ≺ ι[0], ι ≺ (ι[0])‾, ι[0]+1 ≺ ι+1, (ι[0])‾+1 ≺ ῑ+1, ι[0]+1 ≺ ῑ+1}
(examples/Delegation.v), and the reduced scheduler creates r₀ under {γ ≺ γ̄}
(examples/Scheduler.v). The other rows wait for the port of their files.

```
sync            typable                       new and spawn instead of fork
cycle           typable                        P-Connect over {c, d},  (c,0) ≺ (d,0) in both threads
blocked         rejected                       (c,0) ≺ (d,0) and (d,0) ≺ (c,0)
load balancer   semantic                       races on c, unchanged
factory         typable                        new at ι under □∀ι, two sessions at (a,0), (b,0) held at once (61)
leader election semantic                       breaks linearity, unchanged
scheduler       typable                        (r₁,0) ≡ (r₀,0) from the link,  reversed ag₀ rejected
request/reply   typable, recursive             C = {ι+k ≺ ι′+k, ι′+k ≺ ι+k+1 ∣ k ∈ ℕ}, call at (ι+1, ι′+1)
relay           typable, recursive             C over ι+k and (ι+k)[1], call at (ι+1, ι[1]+1),
                                               producer creates its payload at the payload point
delegation      typable                        receiver: (c,k)[1] ≺ (c,k+1),  sender aliases d to (c,k)[1]
bad link        rejected                       (c,0) ≺ (e,0) ≺ (d,0) ≡ (c,0)
```

Rocq types request/reply and the relay with these infinite constraints (sharp edges 66).
The three programs below are the ones 65 expected. Rocq types all three.

```
tail call       typable, no spawn              □(∀ι ζ. {ι+k ≺ ζ ∣ k ∈ ℕ}. ∗ ⊸ (S@ι ⊸^ζ ∗)),
                                               the tail call at (ι+1, ζ) asks ζ ≺ μ, a future hypothesis,
                                               the world has (a,k) ≺ (z,0) for every k (tc_deadlock_free)
forwarder       typable, recursion by spawn    receives d on one channel and sends it on another inside a box,
                                               C ∋ (ι+k)[1] ≡ (ι′+k)[1], E-Conv moves d from D@ι[1] to D@ι′[1]
                                               (sharp edges 67, fw_deadlock_free)
received chain  typable, recursion by spawn    call at ι[1], C = {ι[1]ⁿ + 1 ≺ ι[1]ⁿ⁺¹ ∣ n ∈ ℕ},
                                               ι[1]ⁿ = ι[1]…[1] (n times), upper point ι+1 (ch_deadlock_free)
```

The forwarder failed at send before sharp edges 67. recv gives d the type D@ι[1] and send at ι′
asks D@ι′[1]. E-Conv compared points by equality then, so the fact ι[1] ≡ ι′[1] of C was never read.
E-Conv up to ≈_Γ reads it. In the closed program a producer sends fresh channels on a, the
forwarder passes them from a to b, and a consumer closes them. The producer and the consumer
share C = {ι+k ≺ (ι+k)[1], (ι+k)[1] ≺ ι+k+1 ∣ k ∈ ℕ}, and the world has (a,k)[1] ≡ (b,k)[1] for
every k.

## 14  Open

- Deferred by the author: order that depends on the run (one W per component, docs/history/DESIGN-REVIEW.md C2).
- A constraint has finitely many roots in Rocq (the roots of its outer points). §4 does not say so. O-New needs it, because a type with infinitely many constant roots leaves no fresh point.
- Rocq admits box bodies that are not thunks. Their V is empty, but the grammar of §4 has only the thunk form.

## 15  Lessons from the earlier mechanization (respect these)

An earlier order design was mechanized and abandoned. What it taught, and how this spec already accounts for it:

- Minimality ("my instant is minimal") is unsound as a gate. ready here compares every held entry with some offered entry, strictly, and compares entries, never sets of instants (equal instants must not collapse into one element; that is why no "distinct channels have distinct instants" premise is needed).
- The old cut only composed when the composite's external interface carried no ordering, because a leastness-shaped gate is not invariant under external steps. Here ready is checked per state by each component, and P-Connect combines them state by state with the chain argument. This is the central claim and the main risk; report early if it does not go through.
- Step preservation of the cut was left open in three cases: rendezvous with payload migration (handled here by Q-Recv stating its continuation with the returning channels restricted), link with an external survivor (the paper's substitution, plus Entry conversion; worlds name no channels), mixed extrusion (no plain/ordered mix here). Report early if any of them resists.
- Term-level ∀-introduction got stuck (instantiation needed an order-indistinguishable world copy). Here ∀ appears only directly under □, on values, and is an intersection over instances.
- The future/window condition holds for offered entries only; a condition on all pending heads is false (recv returns a continuation above its own instant).
- A closure without a lower bound must hold nothing (an absent ℓ forces Σ = ∅).
- Unrolling under ≈ needs contractiveness (the paper already assumes it). Counters live in Σ, not in types, so unrolling never has to advance an annotation.
- Constants are typed through their signatures, one compositionality lemma per constant.

## 16  Out of scope for now

Neither item is part of the current Rocq round, and neither is on the progress page.
The design first aims at a constraint language that expresses many programs (sharp edges 65).
Decidability comes later, for an algorithmic system over a fragment of the constraints.

Decidability. A candidate fragment is the counter language of docs/extensions/algorithmic.md (section on decidability): facts
∀κ̄. x ≺ y whose coordinates are constants or κ + n, with each counter at most once per side.
That document decides strictness of the generated world under further side conditions and
shows undecidability without them. It writes forced invariants as C = ⋃ₖ C₀[σᵏ(ιs)] and payload points as x[i].

An algorithmic type system. The static system of §9 is declarative. Missing for an algorithm:
- choosing facts: rules emit facts instead of checking them
- checking facts: entailment for the chosen fragment of constraints
- choosing C: constraints of recursive boxes as invariants, given or inferred
- fresh points (E-Abs μ, ℓ; new ι): generate fresh point variables
- ∀ instantiation (E-Force): unification over points
- payload points (send's ∃xs): determined by the aliases to the payload points x[i]
- environment splitting (E-App, E-Let*): input/output contexts
- conversion (E-Conv): ≈ on regular session types is decidable; apply at application/ascription
- annotations: ∀ schemes under □ and recursive types are given, not inferred
