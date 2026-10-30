# D.1 Adequacy for Priority GV

Goal. Every closed program of a PGV fragment is deadlock free, proved by
translating PGV derivations into the static system (route 1 of
[subsumption.md](subsumption.md)). Source is Kokke and Dardha, "Prioritise the
Best Variation", LMCS 19(4):28 = arXiv 2103.14466v6. Page numbers are pdf pages.

State of 2026-10-30. The paper study is done. The Rocq part has not started and
waits for the findings below. PGV as printed is unsound. Two side conditions are
missing, and section 3 gives one deadlocking program for each.

## 1  How PGV's priorities work

Every connective of a session type carries a priority o ∈ ℕ (p4). Duality keeps
priorities (p5). pr(S) is the priority of the top connective. On other types it
is the minimum over the session types and arrows inside, with pr(T ⊸^{p,q} U) = p
and ⊤ for 1 and ∅ (p5). The arrow carries a lower bound p, the minimum priority
of the captured endpoints, and an upper bound q on the priorities of the actions
the call performs (p4 to p5).

The term judgment Γ ⊢^p M : T has one bound, an upper bound on the priorities of
M's actions (p10). The lower bound is not on the sequent. PGV reads it off pr(Γ),
because a term cannot act before the earliest of the endpoints it holds (p10).
Values have bound ⊥ (Lemma 3.1, p15). The schemas give send, recv, close and wait
the type _ ⊸^{⊤,o} _ for an action at o, and new, spawn and link are pure (p9).

The order checks sit in the sequencing rules (p9).

```
T-App      Γ ⊢^p M : T ⊸^{p′,q′} U    Δ ⊢^q N : T    p < pr(Δ)    q < p′
T-LetUnit  Γ ⊢^p M : 1                Δ ⊢^q N : T    p < pr(Δ)
T-Pair     Γ ⊢^p M : T                Δ ⊢^q N : U    p < pr(Δ)
T-LetPair  Γ ⊢^p M : T × T′           Δ, x : T, y : T′ ⊢^q N : U    p < pr(Δ, T, T′)
T-CaseSum  Γ ⊢^p L : T + T′           Δ, x : T ⊢^q M : U   Δ, y : T′ ⊢^q N : U    p < pr(Δ)
T-Lam      Γ, x : T ⊢^q M : U   ⇒   Γ ⊢^⊥ λx.M : T ⊸^{pr(Γ),q} U
```

Each check says that whatever runs first stays below the top priorities of what
is still held. `let x = M in N` is sugar for (λx.N) M (p6). Under T-App it checks
M's bound against the closure's captured environment and never against the type
of x itself.

## 2  Non-increasing sessions (question a)

PGV admits session types whose priorities fall along the session. The grammar
has no condition (p4), and no schema or rule constrains the continuation (p9).
The sentence "the type system guarantees that the top-most connective always
holds the smallest priority" (p5) has no rule behind it.

Such a type is also usable. T-LetPair would reject a receiver that continues
lower, because it checks pr(T′). The let sugar goes through T-App and skips that
check.

```
x : !⁵1.?⁰1.end⁶?     let x = send ((), x) in let (u, x) = recv x in u; wait x
y : ?⁵1.!⁰1.end⁶!     let z = recv y in let (u, y) = z in u; let y = send ((), y) in close y
```

Both threads type in PGV. A falling session is harmless for deadlock freedom.
Every check compares the action under way with the top priorities of the other
endpoints held at that moment, and the progress argument needs nothing more
(section 4). The priority of an endpoint is therefore a property of the current
instant. It is no rank of the endpoint over time.

For us the falling session is the obstacle. Program order (y, 0) ≺ (y, 1) holds in
every world. A world that ranks instants by their PGV priority puts (y, 1) below
(y, 0), so it is not strict. Section 5 says what this leaves open.

## 3  Two missing side conditions (question b, and T-Pair)

### 3.1  send with a lower-priority payload

The send schema T × !ᵒT.S ⊸^{⊤,o} S asks nothing of T (p9), and Lemma 3.1 gives
the payload value bound ⊥, so T-App adds no check either. PCP, which PGV follows,
asks o < pr(Γ, A, B) for both payload A and continuation B (Fig. 8, p28). Without
it the following closed program types in PGV and deadlocks.

```
let (c, c′) = new () in        c : ?¹1.end⁴?          c′ : !¹1.end⁴!
let (d, d′) = new () in        d : !³(!¹1.end⁴!).end⁵!  d′ : the dual
let (e, e′) = new () in        e : !²1.end⁶!          e′ : ?²1.end⁶?
spawn (λ(). let d = send (c′, d) in close d);
spawn (λ(). let (u, e′) = recv e′ in u;
            let z = recv d′ in let (c′, d′) = z in
            let c′ = send ((), c′) in close c′; wait d′; wait e′);
let (u, c) = recv c in u; let e = send ((), e) in wait c; close e
```

The side conditions all hold. Main receives on c at 1 while it holds e at 2. The
second child receives on e′ at 2 while it holds d′ at 3. It receives on d′ at 3
through the let sugar, whose closure captures only e′ at 6, and it then uses c′ at
1. The first child sends c′, priority 1, over d at 3. After the news and spawns,
main waits on c, whose other end sits in the first child's payload. The first
child waits for d′, the second child waits for e, and only main sends on e. No
rule of Fig. 1 applies and main is no value, which contradicts Theorem 3.13 (p24).

With o < pr(T) required for !ᵒT.S, the program fails at the first child. That
condition is exactly our send premise {ι} ≺ heads(P[ι]). Our system rejects the
program by a cycle (d,0) ≺ (c,0) ≺ (e,0) ≺ (d,0), from the send, from main and from
the second child.

### 3.2  T-Pair

Pairs evaluate left to right (p7). While N runs in (M, N), the value of M is held.
T-Pair compares only M's bound with N's environment (p9). It never asks q < pr(T).
The following program types and deadlocks. All its session types rise and every
payload is 1, so it is independent of 3.1 and of section 2.

```
let (c, c′) = new () in        c : !¹1.end⁷!   c′ : ?¹1.end⁷?
let (v, v′) = new () in        v : !²1.end⁸!   v′ : ?²1.end⁸?
let (w, w′) = new () in        w : !⁵1.end⁹!   w′ : ?⁵1.end⁹?
spawn (λ(). let (u, c′) = recv c′ in u; let (u, v′) = recv v′ in u; wait c′; wait v′);
spawn (λ(). let v = send ((), v) in let (u, w′) = recv w′ in u; close v; wait w′);
let z = (c, send ((), w)) in let (c, w) = z in let c = send ((), c) in close c; close w
```

Main sends on w at 5 while the pair already holds c at 1. T-Pair checks ⊥ < 5,
and the let sugar's closure captures nothing. Main waits for the second child on
w, the second child waits for the first on v, and the first waits for main on c.

With q < pr(T) added to T-Pair the program fails at main. Our E-Pair types the
right component under F ∪ heads(T), which is the same condition, and rejects the
program by the cycle (w,0) ≺ (c,0) ≺ (v,0) ≺ (w,0).

## 4  The progress proof

Theorem 3.13 picks the ready term L with the smallest priority bound and lets L′
be the thread that uses the dual endpoint y′ (p24). It concludes that L′ is ready
on y′, "otherwise the action y′ would be guarded by another action with priority
smaller than pr(S)". Lemma 3.12 shows only that the bound of a ready term is a
number (p24).

Three steps fail as written.

1. The bound of L = E[M] is the maximum over M and all of E (proof of Lemma 3.12,
   p24). It is the priority of L's last action, and "the priority of L is pr(S)"
   does not follow. Minimality of bounds then says nothing about the action L′
   is blocked on. The argument works with the priority of the current action in
   place of the bound.
2. L′ may hold y′ inside the payload of the send it is blocked on. Nothing guards
   y′ there (3.1).
3. L′ may hold y′ in the evaluated left component of a pair whose right
   component it runs (3.2).

With both side conditions added and the minimum taken over current actions, the
argument goes through. Take the blocked action of least priority o, on y. The
holder of y′ sees y′ at top priority o by duality. Every other action it could be
blocked on is guarded by a check against pr(y′) = o, so it lies below o, which
contradicts minimality. The argument reads only top priorities at the current
instant, so falling sessions need no extra care.

## 5  One static order

PGV orders the instants that are held at the same time. It says nothing about an
instant and a later instant of the same endpoint, and a falling session puts the
later one lower. Our worlds order all instants at once and always contain program
order.

For sessions whose priorities rise along the session and above their payloads,
PGV's priority is a rank of instants and one static world exists, the
protocol-point world of section 6. For falling sessions that world is not strict.
Whether every repaired PGV program still has some strict world is open. A cycle
would need a falling program-order edge closed by facts that each raise the PGV
priority. In one run each fact "act on a while holding b" puts a before b in time,
so such a cycle cannot come from one run. It could come only from facts that two
exclusive branches state about the same instants. Every instance tried so far
needs the same endpoint at both priorities at the same moment, which PGV rejects,
or two different instants, which a world keyed by instants keeps apart. No
counterexample to subsumption has turned up.

## 6  Proposed fragment and plan for the Rocq part

Fragment v1, "repaired monotone PGV". All of PGV except 0 and absurd and link,
with three restrictions.

- Every session type is monotone and payload-bounded. In !ᵒT.S and ?ᵒT.S,
  o < pr(T) and o < pr(S), recursively. This is PCP's T-Send condition read on
  types, and it covers 3.1 and section 2.
- T-Pair asks q < pr(T) (3.2).
- link is left out. PGV's link is pure, with upper bound ⊥ (p9). Ours blocks at the
  point of its first end, so the context must lie above that point, and PGV gives
  no such bound.

The world needs one root constant. The protocol point of S is a slot of (a,0)
indexed by a code of S, the same for S and its dual. The bound points ℓ_p and u_q
are slots of (a,1) and (a,2). The generators make (S's point)+1 ≡ the point of the
continuation, and they order points by rank 3·pr(S)+1 for protocols, 3p for ℓ_p
and 3q+2 for u_q. A payload needs no carried points. Its points are constants,
which E-Const at send allows (kscoped only bounds point variables). Strictness
comes from a denotation of points that respects successor and slots, with the rank
read on denotations. A canonical map into points, as in ExampleTools.v, cannot
serve. It has to commute with successor, so it would identify any two protocols
with the same continuation, whatever their priorities.

The translation keeps the term except that an unapplied send, recv, close or
wait becomes λz.k z, because the constant's own upper point is the channel point
and not u_o. PGV's bound p corresponds to frames. The lemma states typed at every
frame F with {u_p} ≺ F. Monotonicity of {u} ≺ F along u′ ≼ u covers the joins.
