# Session choice from sums and delegation

Session choice is a derived form of the core. A selection sends the injection of
a fresh continuation channel, and the payload type puts the left arm at the
point self[0] and the right arm at self[1]. Each branch of a choice then has a
point of its own, which is what the branch points x◁i of K10 added as a new
name (data-dependent.md, sharp edges 76). The program T1 ∥ T2 ∥ T3 that
motivated branch points types with the encoding and is deadlock free. K11
(sharp edges 142) later dropped x◁i and lets the native choice continue at
x[i] as well.
Everything is in theories/examples/ChoiceEnc.v, and no rule, constant or
definition of the core changes.

## The encoding

PGV encodes S₁ ⊕ S₂ as !(S₁ + S₂).end (Kokke and Dardha, Prioritise the Best
Variation, p. 6). Here the payload of the carrier binds two points.

```
Sch S₁ S₂ = !(∃ι₀ ι₁. (dual S₁)@ι₀ ⊕ (dual S₂)@ι₁).Close        (Sch)
Sbr T₁ T₂ = ?(∃ι₀ ι₁. T₁@ι₀ ⊕ T₂@ι₁).Close                      (Sbr)
dual (Sch S₁ S₂) = Sbr (dual S₁) (dual S₂)                       (dual_Sch)
```

At a carrier point x, arm i of the sum lies at x[i]. The terms use new, send,
recv, close, the sum and its case.

```
sel₁ = λc. let (k, k′) = new ∗ at x[0] in let () = close (send ⟨inj₁ k′, c⟩) in k
sel₂ = λc. let (k, k′) = new ∗ at x[1] in let () = close (send ⟨inj₂ k′, c⟩) in k
branch c e₁ e₂ = let (p, c) = recv c in let () = close c in case p e₁ e₂
```

The typing rules are lemmas. `sel1_typed` and `sel2_typed` give

```
sel_i : Sch S₁ S₂@x ⊸^{x+1}_⊤ S_i@x[i]
  if x is known, Δ is unlimited, x ≺ x[0], x ≺ x[1], x+1 ≺ x[i]
```

The send asks x ≺ x[0] and x ≺ x[1] (KTSend orders the carrier below every
point of the payload). The close of the carrier at x+1 asks x+1 ≺ x[i], because
sel_i holds k at x[i] at that moment. `sel_typed` proves both cases at once.

`branch_typed` receives the sum at x while the context holds Δ₂, closes the
carrier at x+1 while it holds the sum and Δ₂, and continues in arm i with the
continuation at x[i]. The sum has the heads x[0] and x[1], so the close asks
x+1 ≺ x[0] and x+1 ≺ x[1] in both arms. The two arms are typed in the same
context, as E-Case demands, and each sees its continuation at its own point.

## T1 ∥ T2 ∥ T3

The program is T2 of mordido-perez.md §9.5, as data-dependent.md writes it.

```
c : ⊕{A: !∗.Close, B: !∗.Close}      d : Close
T1 = select A c; send ∗ c; close c
T2 = branch c { A ⇒ close d; recv c; close c  |  B ⇒ recv c; close d; close c }
T3 = close d
```

`choice_main` creates c at the top-level variable a and d at the top-level
variable δ, spawns T1 and T3, and runs T2 itself. The facts each step asks are
these.

| Thread | Step | Facts |
|---|---|---|
| T1 | send on c at a | a ≺ a[0], a ≺ a[1], and a ≺ a[0] because it holds k |
| T1 | close c at a+1 | a+1 ≺ a[0] because it holds k |
| T2 | recv c′ at a | a ≺ δ because it holds d |
| T2 | close c′ at a+1 | a+1 ≺ δ, a+1 ≺ a[0], a+1 ≺ a[1] |
| T2, branch A | close d at δ | δ ≺ a[0] because it holds k |
| T2, branch A | recv k at a[0], close k at a[0]+1 | program order |
| T2, branch B | recv k at a[1] | a[1] ≺ δ because it holds d |
| T2, branch B | close d at δ | δ ≺ a[1]+1 because it holds k |
| T2, branch B | close k at a[1]+1 | none |

Branch A needs δ ≺ a[0] and branch B needs a[1] ≺ δ. The two facts name
different points, so together they close no cycle. The program starts under the
top-level constraint

```
Cch = {a+1 ≺ a[1], a[1] ≺ δ, δ ≺ a[0], δ ≺ a[1]+1}
```

and program order and transitivity give the other facts. Cch is acyclic
(`ch_rank_ok`), with the rank 10k for a+k, 15+10k for a[1]+k, 17+10k for δ+k and
20+10k for a[0]+k. The order it describes is a ≺ a+1 ≺ a[1] ≺ δ ≺ a[0], with
δ ≺ a[1]+1. `choice_typed` states `styped` of the program under Cch, and
`choice_deadlock_free` is deadlock freedom of `choice_main` by
`soundness_source`.

Cch is the top-level constraint C₀ of `soundness_source`, because `t_new_at`
creates c and d at the top-level variables a and δ. `ch_rank_ok` is the premise
that makes the start world `wc0 2 Cch` strict.

## Negative control

The same program with one point for both arms types c with

```
Sch₀ = !(∃ι₀. (?∗.Close)@ι₀ ⊕ (?∗.Close)@ι₀).Close
```

Both arms then receive k at a[0]. Branch A closes d while it holds k and asks
δ ≺ a[0]. Branch B receives on k at a[0] while it holds d and asks a[0] ≺ δ.
E-Case types both arms in one context and the type of k comes from the payload,
so the two facts speak of the same two points. E-Conv keeps points and E-Weak
drops only unlimited bindings, so every derivation asks both facts.

Two lemmas make the cycle formal. `same_slot_cycle` says that δ ≺ k and k ≺ δ
cannot both hold where ≺ is irreflexive, for every k the two arms share.
`same_slot_not_acyclic` says that a top-level constraint holding δ ≺ a[0] and
a[0] ≺ δ fails `c0_acyclic`, so `soundness_source` accepts no such constraint.
The step from the program to the two facts is the argument above and is not a
theorem. An underivability proof in the style of examples/Rejected.v would need
inversion over the derivation of the whole term.

## A recursive choice

The server answers Next by sending ∗ and recursing, and Stop by closing.

```
R = μX. &{Next: !∗.X, Stop: Close} = μX. Sbr (!∗.X) Close
srv : □(∀ι. C. ∗ ⊸^⊥_⊤ (R@ι ⊸^{ι[1]}_⊤ ∗))
srv = !(f = λc. branch c { k ⇒ spawn (λw. let () = w in (force f) (send ⟨∗, k⟩))
                         | k ⇒ close k })
```

The client of `loop_main` spawns `(force f) c`, selects Next twice and then
Stop. Round n runs at p_n with p_0 = a and p_{n+1} = p_n[0] + 1. Next hands
over k at p_n[0], the server sends ∗ on it, and the continuation lies at
p_n[0]+1.

The body receives at ι and closes the carrier at ι+1 while it holds the sum, so
it asks ι+1 ≺ ι[0] and ι+1 ≺ ι[1]. Stop closes k at ι[1], which is the upper
point of the body. Next sends at ι[0] in a thread that then forces f at
ι[0]+1, so the call asks the constraint at ι[0]+1 and the thread asks
ι[0] ≺ (ι[0]+1)[1]. The box constraint states the two facts for every round.

```
C = {p_n + 1 ≺ p_n[0], p_n + 1 ≺ p_n[1] ∣ n ∈ ℕ}
```

It is infinite, as in examples/ReceivedChain.v. C at ι := p_1 is C without its
first round (`lp_sub`), so the recursive call meets C (`lp_call`). The program
starts under C as its top-level constraint. Its rank is the offset plus a
depth that grows at each carried point by the offset of its base plus 2
(`lp_acyclic`).
`srv_typed` types the box, `loop_typed` states `styped` of `loop_main`, and
`loop_deadlock_free` follows by `soundness_source`.

## Theorems

| Theorem | Statement | Assumptions |
|---|---|---|
| `sel_typed`, `sel1_typed`, `sel2_typed` | typing of sel_i | closed |
| `branch_typed` | typing of branch | closed |
| `ch_rank_ok` | Cch is acyclic | closed |
| `choice_typed` | `styped` of T1 ∥ T2 ∥ T3 under Cch | closed |
| `choice_deadlock_free` | T1 ∥ T2 ∥ T3 is deadlock free | closed |
| `same_slot_cycle` | the two facts of one shared point close a cycle | closed |
| `same_slot_not_acyclic` | no acyclic top-level constraint states them | closed |
| `srv_typed` | typing of the recursive server | closed |
| `lp_acyclic` | the infinite constraint C is acyclic | closed |
| `loop_typed` | `styped` of the client with the server under C | closed |
| `loop_deadlock_free` | the client with the server is deadlock free | closed |

"closed" means Print Assumptions answers "Closed under the global context".

## Cost against branch points

Branch points add the name former x◁i (NBr), the two world laws x ≡ y ⇒ x◁i ≡
y◁i and x ≺ x◁i with their counterparts in generated worlds, and the session
types ⊕ and & with O-Select, O-Branch, Q-Select and Q-Branch. The encoding needs
none of them. x[i] already exists, and its laws are those of carried points.

The price is paid at run time and in the derivation. Each selection runs one
extra `new` and one extra close of the carrier, so a choice creates a channel
and the continuation is a different channel from the carrier. Each selection
also asks x+1 ≺ x[i] and each branch asks x+1 ≺ x[0] and x+1 ≺ x[1], facts that
a native choice at x◁i does not ask because program order gives x ≺ x◁i. In the
two programs above these facts went into the constraint or followed from it. Under
K11 the native choice continues at x[i] too and asks x ≺ x[i] as a side
condition of select and branch (sharp edges 142).
