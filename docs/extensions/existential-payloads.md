# Existential payloads

A message whose payload introduces facts at the send is a derived form. The
payload of a send is a type, and an existential ∃^ℓ ι⃗. C. T is a type. The
sender packs with E-Pack and proves C at its instance. The receiver opens with
E-Open and assumes C about fresh points. No rule, constant or definition of the
core changes. The example is theories/examples/ExPayload.v, with the closed
theorems `ex_typed` and `ex_deadlock_free`.

## The derived rules

Write the payload as P = ∃κ⃗. ∃^ℓ ι⃗. C. T, where κ⃗ are the m payload
binders of the message and ι⃗ the n binders of the existential. At the carrier
point x the payload is P[x] = ∃^{ℓ[x]} ι⃗. C[x]. T[x], with κⱼ ↦ x[j]
(`payload_at`). The send of a packed value is E-Pack followed by the send
signature.

```
ys known    Γ ⊢ C[x][ys/ι⃗]    Γ ⊢ ℓ[x] ≼ heads(T[x][ys/ι⃗])
Δ₁ ⊢ v : T[x][ys/ι⃗]    Γ ⊢ x ≺ ℓ[x]    c : (!P;S)@x ∈ Δ₂
───────────────────────────────────────────────────────── Send-∃
Δ₁, Δ₂ ⊢ send ⟨v, c⟩ : S@(x+1)
```

The first four premises are E-Pack at the instance ys. The fifth is the fact
set of `KSSend`, x ≺ h for every h ∈ heads(P[x]), and heads(P[x]) = {ℓ[x]}.
The send does not ask x below the channels inside the packed value. It asks
x ≺ ℓ[x], and E-Pack asks ℓ[x] at or below every head of the value.

The receive is the receive signature, E-LetPair and E-Open on the bound
payload.

```
Γ, C[x][ι⃗′/ι⃗] ; Δ, y : T[x][ι⃗′/ι⃗], c : S@(x+1) ⊢ e : U      ι⃗′ fresh
───────────────────────────────────────────────────────── Recv-∃
Γ ; Δ, c : (?P;S)@x ⊢ let (y, c) = recv c in e : U
```

E-Open adds C[x][ι⃗′/ι⃗] as a hypothesis with the ι⃗′ as its instance, so
the receiver also knows the ι⃗′. With n = 0 the existential binds no point and
C speaks of payload points only, so the message carries facts among x[0], …,
x[m-1].

Three side conditions come from the core and not from the derivation.
- C, ℓ and T mention payload binders only. `kscoped` asks the payload of a
  send and a receive to be closed under κ⃗ (`pscoped`).
- ℓ is a payload point or absent. A payload with ℓ = ⊥ sets the ⊥ flag, and
  the send signature has no instance at the flag (sharp edges 103).
- ℓ absent means that the value holds no channel.

## The example

```
Pay = ∃κ₀. Close@κ₀ ⊗ ∃^{κ₀} ι. {κ₀ ≺ ι}. (!∗.Close)@ι
Sx  = !Pay.Close

server = let (k₁, k₁′) = new ∗ at a[0] in
         let (k₂, k₂′) = new ∗ with {a[0] ≺ ι} in
         let () = spawn (λu. let () = u in recvclose k₂) in
         let () = close (send ⟨⟨k₁′, pack k₂′⟩, c⟩) in close k₁
client = let (p, c′) = recv c′ in let () = close c′ in
         let (k₁′, q) = p in
         let () = close k₁′ in close (send ⟨∗, k₂′⟩)        (q opened as k₂′ at v′)
ex_main = let (c, c′) = new ∗ at a in
          let () = spawn (λu. let () = u in server) in client
```

The server creates the signal channel k₁ at the payload point a[0] and the
data channel k₂ at a fresh point v with the creation constraint {a[0] ≺ v}
(`t_newfresh_lh_open`). It sends both ends to the client in one message, the
end of k₂ packed with the instance v. The client closes k₁′ while it holds
k₂′, and that asks a[0] ≺ v′ for the point v′ that E-Open gives k₂′. The fact
is the opened hypothesis. No constraint written before the receive can state
it, because v′ is bound by the open.

| Thread | Step | Facts |
|---|---|---|
| server | send on c at a | a ≺ a[0] (heads of the payload and k₁ held) |
| server | pack k₂′ | C at v is a[0] ≺ v, and a[0] ≼ v for the lower bound |
| server | close c at a+1 | a+1 ≺ a[0] (k₁ held) |
| server | close k₁ at a[0] | none |
| receiver of k₂ | recv at v, close at v+1 | program order |
| client | recv on c′ at a | none |
| client | close c′ at a+1 | a+1 ≺ a[0] (the pair has the heads a[0] and ℓ = a[0]) |
| client | close k₁′ at a[0] | a[0] ≺ v′ (k₂′ held), from E-Open |
| client | send and close on k₂′ | program order |

The top-level constraint is {a+1 ≺ a[0]} (`C0x`), acyclic by the rank 10k for
a+k and 15+10k for a[0]+k (`ex_rank_ok`). `ex_typed` states `styped` of
`ex_main` under it, and `ex_deadlock_free` follows by `soundness_source`.

Two placements in the program follow from upper points. The receiver of k₂ is a
thread of the server spawned after the creation of k₂, so its upper point v+1
is a point of its context. The client runs in the main thread, whose future is
empty. A spawned client would declare its upper point before the open, and C
gives no point above v′. I did not try the spawned variant in Rocq.

## Derived form or rule

A derived form. Send-∃ and Recv-∃ are compositions of E-Pack, E-Open, E-LetPair
and the send and receive signatures, so a payload with facts over payload points
and over points bound in the payload needs no new rule. The semantic side needs
nothing new either, because `soundness_source` covers every `styped` derivation.

The boundary is the type language. A payload type mentions payload binders only,
and a session type carries no other point (types/Types.v, "point instantiation
never enters a session type"). So no message, derived or primitive, can carry a
fact about the carrier point x, about x+1, or about a channel that the receiver
holds outside the message. An example is a server that wants to tell the client
x+1 ≺ v for its fresh channel v, so that the client may close c while holding
the opened channel. In the example above that fact follows from a+1 ≺ a[0] and
the opened a[0] ≺ v′, because the lower bound a[0] is a payload point. A fact
about a point outside the payload in general would need outer points in session
types, which changes duality, payload instantiation and the session clauses of
the relation. That is a change to the type language, not a typing rule.
