# D.1 Adequacy for Priority GV

Notation: this file predates 2026-11-04 and writes p.j for the point now written p[j]; 'slot' and 'carried root' mean that point.

Goal. Every closed program of a PGV fragment is deadlock free, proved by
translating PGV derivations into the static system (route 1 of
[adequacy.md](adequacy.md)). Source is Kokke and Dardha, "Prioritise the
Best Variation", LMCS 19(4):28 = arXiv 2103.14466v6. Page numbers are pdf pages.

State of 2026-10-30. The paper study is done and the fragment of section 6 is
mechanized with link (section 7, theories/pgv/). PGV as printed is unsound.
Two side conditions are missing, and section 3 gives one deadlocking program for
each.

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

This section keeps the plan as written before the mechanization. Section 7 is
authoritative. Link is included there (sharp edges 68), and the ranks are
3·pr(S)+2, 3n+1 and 3n+3 with (0, 0) for ℓ_⊥ and (1, 0) for u_⊤.

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

The translation keeps the term except in two places. An unapplied send, recv,
close or wait becomes λz.k z, because the constant's own upper point is the
channel point and not u_o. new becomes λz. let ∗ = z in let ⟨a, b⟩ = new ∗ in
⟨a, b⟩ on the encoded let of new, because our new has the existential signature
alone (sharp edges 104). PGV's bound p corresponds to frames. The lemma states typed at every
frame F with {u_p} ≺ F. Monotonicity of {u} ≺ F along u′ ≼ u covers the joins.

## 7  What is mechanized

theories/pgv/ proves the following theorems, closed under the global context.

```
Theorem pgv_deadlock_free M p :
  pgv_frag [] p M PUnit → deadlock_free (∅, {[+ pgv_eta M +]}).
Theorem pgv_deadlock_free_applied M p :
  pgv_frag [] p M PUnit → pgv_eta M = M → deadlock_free (∅, {[+ M +]}).
Theorem pgv_deadlock_free_source M p :
  pgv_frag [] p M PUnit → deadlock_free (∅, {[+ M +]}).
```

The judgment. `pgv_typed ok Γ p M T` (PGVTyping.v) is Fig. 2 on our terms. Its
priorities are ℕ ∪ {⊥, ⊤} on arrows and bounds, ℕ on session types (p4). pr(·)
and duality follow p5, the schemas p9. PGV's close and wait are both our close.
T-Pair carries R2, q < pr(T). The schemas of send and recv carry R1,
o < pr(T), and ask `ok` of the session type they act on. `pgv_rep` is
`ok = λ _, True`, which is repaired PGV. `pgv_frag` is `ok = pgv_mono`, the
monotone fragment of section 6 (PGVTypes.v). Environments are linear lists
with no weakening, as in PGV. 0 and absurd are left out. Runtime typing
is not modelled. A closed program creates its channels with new.

The world. `Wpgv` (PGVWorld.v) has one root constant. A protocol point is the
slot a[code S], with one code for S and its dual. ℓ_n, u_n, ℓ_⊥ and u_⊤ are
slots of (a,1), (a,2), (a,3) and (a,4). Its ≡ relates two points of the root
with the same denotation, and its ≺ relates two points of the root with rising
rank. The denotation commutes with successor and slots, and it sends the
successor of a protocol point of !ᵒT.S with o < pr(S) to the protocol point of
S. Ranks are 3·pr(S)+2 for protocols, 3n+1 for ℓ_n, 3n+3 for u_n, (0, 0) for ℓ_⊥
and (1, 0) for u_⊤, read lexicographically. u_⊤ lies above every u_n and so has
no rank in ℕ. Strictness follows because ranks rise along program order.

The translation. `pgv_translate` maps Γ ⊢^p M : T to
typed Wpgv Φ [] ∅ ⟦Γ⟧ F (pgv_eta M) ⟦T⟧ for every Φ and every frame F with
{u_p} ≺ F. T ⊸^{p,q} U becomes ⟦T⟧ ⊸^{u_q}_{ℓ_p} ⟦U⟧ and S becomes ⟦S⟧@a[code S].
The rules map as follows.

| PGV | ours | how the side condition is met |
|---|---|---|
| T-Var, T-Unit | E-LVar, E-Unit | none |
| T-Const new | E-Abs over E-Let* and `t_new_at` (`new_tr_typed`) | the point a[code S] is known, new takes the alias ι ≡ a[code S] |
| T-Const spawn | E-Const | none |
| T-Const link | E-Const | both ends sit at a[code S], so ι ≡ ι′ by reflexivity |
| T-Const send, recv, close, wait | E-Abs over E-App of E-Const | `pgv_eta` makes λz. k z, upper point u_o |
| T-Lam | E-Abs | ℓ_{pr(Γ)} ≼ every head of Γ (`lbp_below_hd`) |
| T-App | E-App | q′ ≤ p⊔q⊔q′, p < pr(Δ) puts u_p below heads(Δ), q < p′ puts u_q below ℓ_p′ |
| T-App of send, recv, close, wait | E-App of E-Const, then E-Conv | the channel point lies below u_o, R1 gives {ι} ≺ heads(T), o < pr(S) gives ι+1 ≡ point of S |
| T-LetUnit, T-LetPair, T-CaseSum | E-Let*, E-LetPair, E-Case | p < pr(Δ) puts u_p below heads(Δ) |
| T-Pair with R2 | E-Pair | q < pr(T) puts u_q below heads(T) |
| T-Inl, T-Inr | E-Inj | none |

An applied send, recv, close or wait stays applied. new never stays, so no
program with new is its own translation, and `pgv_deadlock_free_applied`
covers only programs without new. `pgv_deadlock_free_source`
(PGVSimulation.v) needs no such premise. Its relation `rel` is the congruence
generated by k ~ k and k ~ `kon_eta k` on constants, which relates M to
`pgv_eta M`. A step of M is matched by the same step of the translation after
the β step of λz. k z, and new by two β steps, the channel and three β steps
(`fwd`). When no thread of M takes a β, new or spawn step, β steps bring each
thread of the translation to the action of its thread in M (`norm`), so a step
of the translation is a step of M (`final`). The relation needs no typing and
no administrative forms.

Examples (PGVExamples.v). Each applies `pgv_deadlock_free_source`.
`pgv_ex21_deadlock_free` is Example 2.1 (p4), which
PGV types and GV does not. `pgv_deleg_deadlock_free` sends one end of a channel
over another and the child uses it. `pgv_link_deadlock_free` has a child that
links two channels, and two other threads talk through the link. `cx1_rejected` and `cx2_rejected` show for
every `ok` that the pair of program 1 and the send of program 2 of
pgv-counterexamples.txt have no typing in the repaired judgment.

What section 6 got wrong or left open.

- The proof needs monotonicity only at the session types that send and recv act
  on, and only at the top connective (`top_mono`). `pgv_mono` asks it
  recursively, as decided. R1 is a schema condition and no type
  well-formedness.
- The ranks of section 6 leave no room for the bounds ⊥ and ⊤ on arrows. ℓ_⊥
  needs a rank below ℓ_0, and u_⊤ needs one above every u_n, which takes a pair.
- The world does not list generators one by one. It is generated by "same
  denotation" and "rising rank" on the root, which makes strictness immediate.
- link is in since sharp edges 68 made our link non-blocking, with upper point
  ⊥ like PGV's. The objection of section 6 to link no longer applies.


## 8  Falling sessions (2026-11-04, branch pgv-falling)

Falling sessions are still outside the mechanized result. The point of a
channel cannot be a function of its PGV session type once sessions fall, and
every translation that gives each channel its own point needs one acyclicity
theorem that is open. No counterexample to subsumption turned up.

### 8.1  Two falling programs that PGV types

theories/pgv/PGVFalling.v types two closed programs in repaired PGV
(`fall2_typed`, `fallxy_typed`, both `pgv_rep`). `S1_not_mono` shows that
they lie outside `pgv_frag`. `fall2` is the program of section 2. `fallxy`
uses S1 = !⁵1.?⁰1.end⁶? and S2 = !³1.end⁸! twice each.

```
let (x, x̄) = new () in let (b, b̄) = new () in let (c, c̄) = new () in
spawn (λ(). let b = send ((), b) in let x = send ((), x) in
            let ((), x) = recv x in wait x; close b);
spawn (partner x̄); spawn (partner b̄); spawn (partner c̄);
let c = send ((), c) in let (d, d̄) = new () in spawn (partner d̄);
let z = recv c in let ((), c) = z in let d = send ((), d) in wait c; close d
```

Thread X sends on b at 3 while it holds x at 5. Main receives on c at 0 while
it holds d at 3, after its send on c at 5. Every thread holds at most two
channels and talks only to its partners, so the program is deadlock free.

### 8.2  Points read off the session type fail

Let pt(S) be the point of a session type S in any translation, with
pt(S1) + 1 ≡ pt(S1′) for the continuation S1′ = ?⁰1.end⁶?, as the type of x
after its send requires. X needs pt(S2) ≺ pt(S1) and main needs
pt(S1′) ≺ pt(S2). Program order closes the cycle

```
pt(S1) ≺ pt(S1) + 1 ≡ pt(S1′) ≺ pt(S2) ≺ pt(S1).
```

So no world, fixed or built per program, types `fallxy` through a
translation of types alone. `Wpgv` is one such translation. The point has to
depend on the channel, for example on the occurrence of new that created it.
Each new runs at most once, because PGV has no recursion and every function
is linear.

This is no gap of our system. With a fresh point per new, creation
constraints {ι_b ≺ x} at b and {c + 1 ≺ ι_d} at d state the four facts
without a cycle. That derivation is believed and not mechanized.

### 8.3  What a translation with a point per channel needs

The translation of types then carries points as annotations that flow through
the derivation, into function types, payloads and the two branches of a case.
Two channels that reach one position, such as the results of the two
branches, get one point or an existential. The facts go into a world built
per program or into the creation constraints of the news. Either way the
proof needs one theorem.

> The facts that the derivation states, over all branches, together with
> program order, contain no cycle.

The statement has to cover branches that never run. A fact between two points
that both exist before a case is global in our system. A creation constraint
is conservative, so no later new adds it. E-Open adds only facts that already
hold at the witness. The two branches of a case therefore have to agree on
every fact between older points. The argument of section 5, that one run
orders its facts in time, says nothing about a branch the run skips.

### 8.4  Why no counterexample turned up

A counterexample needs a cycle through a falling step (y, i) ≺ (y, i+1). Some
thread acts on (y, i+1) while it holds a point a, and somewhere a fact leads
from a back to (y, i). Three properties of repaired PGV blocked every
construction tried.

1. A thread that holds two channels acts on them in the order of their
   current priorities. The order is the same in both branches of a case.
2. After a thread acts at priority o, every channel it receives has priority
   above o. The carrier lies above o by the check, and R1 puts the payload
   above the carrier. A closure that the thread holds at that moment
   captures only channels above o, by its lower bound.
3. After a thread acts at o on a falling session, it holds the continuation
   at some priority o′ below o. Until it acts on or gives away that
   continuation, every action of the thread lies below o′. A spawned thread
   that takes the continuation can talk only through channels that the
   parent held above o or created after the action.

The attempts tried were two branches that hand x and y to other threads in
opposite orders, a round trip of y through a second thread, and a fresh
channel created after the falling step to carry y back. Each failed at one of
the three properties, with some instant that would have to lie both above and
below one priority. These properties are the shape a proof of the theorem of
8.3 would take, but they are no proof.

### 8.5  The decision this leaves

Two routes stay open. One is a translation with a point per channel that
takes the acyclicity of 8.3 as a premise, which gives subsumption relative
to that premise. The other is a proof of the theorem, which is a research
question because it must reason about branches that no run takes. Both
rewrite `tr_ty`, `pgv_translate` and the world of PGVWorld.v. Neither touches
the core.
