# GV♯ with orders: a tour

Paper draft `paper-orders` (5bbf52a) and the mechanization on `exists`. Rocq names in `code`.

---

## 1. Syntax

$$
\begin{array}{lrl}
\text{names} & a ::= & \kappa \mid \iota \mid p[j] \\
\text{points} & p ::= & a + k \\
\text{facts} & f ::= & p \prec q \mid p \equiv q \qquad C \subseteq \text{facts (possibly infinite)} \\[4pt]
\text{types} & T ::= & \ast \mid T \otimes T \mid T \oplus T \mid T \multimap^{u}_{\ell} T \mid S@p \mid \Box(\forall \vec\iota.\, C.\ T) \mid \exists^{\ell} \vec\iota.\, C.\ T \\
\text{sessions} & S ::= & !T.S \mid ?T.S \mid \mathsf{Close} \mid \mu X.S \mid X \mid \overline{X} \\
\text{bounds} & u ::= & p \ \ (\text{or absent}) \qquad \ell ::= p \mid \bot \ \ (\text{or absent}) \\[4pt]
\text{nodes} & \nu ::= & p \mid \varphi \mid \bot \\
\text{futures} & F \subseteq & \text{nodes, finite} \\
\text{fact contexts} & \Gamma ::= & \text{facts} \ \cup\ \{\, u \prec \varphi \,\}
\end{array}
$$

- $S@p$ acts next at $p$, its $k$-th action is at $p+k$.
- $p[j]$ is the $j$-th channel carried by the message sent at $p$.
- $u$ = latest point a call blocks at, absent if it never blocks. $\ell$ = lower bound of the captured channels, absent if it captures none, ⊥ if they sit at points nobody knows. An absent bound is not written: $T \multimap^{u} U$, $T \multimap U$.
- a future $F$ = what the thread still acts on later. Its nodes are points, *future variables* φ, each standing for the unknown future of a caller (like an effect variable), and ⊥ for channels at points nobody knows
- the only facts about a future variable are hypotheses $u \prec \varphi$

**Comparing with a future.** A bound lies below a future when it lies below each of its nodes. No rule derives anything below ⊥, so a future containing ⊥ forbids every blocking call.

$$
\Gamma \vdash u \prec F \iff u \text{ absent} \ \lor\ \forall \nu \in F.\ \Gamma \vdash u \prec \nu
\qquad\qquad
\mathrm{heads}(\Delta) = \text{the nodes of the channels in } \Delta \ (\text{points, and } \bot \text{ for } \ell = \bot)
$$

**Signatures** (the ones that matter). Every constant has a constrained scheme $K : \forall \vec x.\ C \Rightarrow T$. E-Const instantiates $\vec x$ and proves the instance of $C$ from Γ, exactly as `force` proves a box constraint. Only `new` is different: it introduces a fresh point, so instead of proving $C$ it checks `cc_ok`(C).

$$
\begin{array}{lll}
\mathsf{new} & \mathsf{cc\_ok}(C) \Rightarrow & \ast \multimap \exists^{\bot}\iota.\,C.\ (S@\iota \otimes \overline{S}@\iota) \\
\mathsf{send} & \forall p.\ \{\, p \prec h \mid h \in \mathrm{heads}(T[p/\mathit{self}]) \,\} \Rightarrow & T[p/\mathit{self}] \otimes (!T.S)@p \multimap^{p} S@(p+1) \\
\mathsf{force} & \forall \vec p.\ C[\vec p/\vec\iota] \Rightarrow & \Box(\forall\vec\iota.\,C.\ \ast \multimap^{u} T) \multimap^{u[\vec p/\vec\iota]} T[\vec p/\vec\iota]
\end{array}
$$

`heads` is computed when the scheme is instantiated, so the constraint is a plain set of facts. A payload that hides an unknown point (⊥) has no instance.

<details>
<summary>All signatures, the fact theory, bounds</summary>

$$
\begin{array}{lll}
\mathsf{new} & \mathsf{cc\_ok}(C) \Rightarrow & \ast \multimap \exists^{\bot}\iota.\,C.\ (S@\iota \otimes \overline{S}@\iota) \\
\mathsf{spawn} & & (\ast \multimap^{u}_{\ell} \ast) \multimap \ast \\
\mathsf{send} & \forall p.\ \{\, p \prec h \mid h \in \mathrm{heads}(T[p/\mathit{self}]) \,\} \Rightarrow & T[p/\mathit{self}] \otimes (!T.S)@p \multimap^{p} S@(p+1) \\
\mathsf{recv} & \forall p. & (?T.S)@p \multimap^{p} T[p/\mathit{self}] \otimes S@(p+1) \\
\mathsf{close} & \forall p. & \mathsf{Close}@p \multimap^{p} \ast \\
\mathsf{link} & \forall p\,q.\ \{p \equiv q\} \Rightarrow & S@p \otimes \overline{S}@q \multimap \ast \\
\mathsf{force} & \forall \vec p.\ C[\vec p/\vec\iota] \Rightarrow & \Box(\forall\vec\iota.\,C.\ \ast \multimap^{u} T) \multimap^{u[\vec p/\vec\iota]} T[\vec p/\vec\iota]
\end{array}
$$

**Creation constraint** (`cc_ok`) over fresh $\iota$ under $\Gamma$:
acyclic ($\Gamma, C \nvdash p \prec p$) and conservative (no new $\prec$ or $\equiv$ between points whose root is not $\iota$).

**Aliasing** $\Gamma \vdash p \equiv q$: equivalence, closed under $p \mapsto p+1$ and $p \mapsto p[j]$, plus hypotheses.

**Precedence** $\Gamma \vdash p \prec q$:

$$
\frac{}{p \prec p+1}\;\text{O-Po}
\qquad
\frac{(p \prec q) \in \Gamma}{p \prec q}\;\text{O-Hyp}
\qquad
\frac{p \prec q \quad q \prec r}{p \prec r}\;\text{O-Trans}
\qquad
\frac{p \equiv p' \quad p' \prec q}{p \prec q}\;\text{O-EqL}
\qquad
\frac{p \prec q' \quad q' \equiv q}{p \prec q}\;\text{O-EqR}
$$

Program order relates points of **one name** only: $\iota \prec \iota[0]$ never holds for free.

**Bounds**

$$
\Gamma \vdash u \prec F \iff u \text{ absent} \ \lor\ \forall q \in F.\ \Gamma \vdash u \prec q
\qquad
\Gamma \vdash \ell \preceq N \iff (\ell \text{ absent} \land N = \emptyset) \ \lor\ \ell = \bot \ \lor\ \forall q \in N.\ \ell \equiv q \lor \ell \prec q
$$

$\mathrm{heads}(S@p) = \{p\}$, $\mathrm{heads}(T \multimap^u_\ell U) = \mathrm{heads}(\exists^\ell\ldots) = \{\ell\}$, $\mathrm{heads}(\Box\ldots) = \emptyset$, unions for $\otimes, \oplus$.

</details>

---

## 2. Example: one message

```
sync = let (c, c′) = new ι {} ∗ in                -- c : (!∗.Close)@ι,  c′ : (?∗.Close)@ι
       spawn (λ^{ι+1}_ι ∗. close (send ⟨∗, c⟩));   -- send at ι, close at ι+1
       let (x, c₁′) = recv c′ in                    -- recv at ι
       x; close c₁′                                 -- close at ι+1
```

- no constraint needed: program order ι ≺ ι+1 and the λ's hypothesis ι+1 ≺ φ do all the work

`sync_deadlock_free`

---

## 3. Points in payloads: `self`

- a channel type names only its next point: `S@p`
- a message sent at `p` carries its channels at `p[0], p[1], …`
- a payload type says where, relative to its own message: `self[j]`
- sending or receiving at `p` fills in `self := p`, that is `T[p/self]`
- both ends synchronize on the action at `p`, so both compute `p[j]`, and no point travels at run time
- `p[j]` is a name of its own: program order never relates `p` and `p[j]`, so a creation constraint has to

| point | meaning |
|---|---|
| `ι[0]` | the channel carried by the message sent at ι |
| `ι[0]+1` | that channel after one action of its own |
| `(ι+1)[0]` | the channel carried by the next message on the carrier |
| `ι[0]ⁿ` | `ι[0][0]…[0]` with n brackets: the channel carried by the channel carried by …, n levels deep. `ι[0]⁰ = ι` |

---

## 4. Example: handing over a channel

```
S⁰ = !∗.Close
S  = !(S⁰@self[0]).Close

deleg = let (c, c′) = new ι { ι ≺ ι[0],  ι[0]+1 ≺ ι+1 } ∗ in
        let (d, d′) = new κ { κ ≡ ι[0] } ∗ in
        spawn K;
        let c₁ = send ⟨d, c⟩ in              -- at ι, self := ι, d : S⁰@ι[0]
        let (x, d₁′) = recv d′ in            -- at ι[0]
        x; close d₁′;                        -- at ι[0]+1
        close c₁                             -- at ι+1

K = λ^{ι+1}_ι ∗. let (e, c₁′) = recv c′ in   -- at ι, e : S⁰@ι[0]
                  close (send ⟨∗, e⟩);       -- at ι[0], ι[0]+1
                  close c₁′                   -- at ι+1
```

```
carrier c :   ι ─────────────────────────── ι+1
payload d :      ι[0] ───── ι[0]+1
order     :   ι ≺ ι[0] ≺ ι[0]+1 ≺ ι+1
```

`deleg_typed`, `deleg_deadlock_free`

<details>
<summary>Every obligation</summary>

| action | blocks at | holds | owes |
|---|---|---|---|
| main `send ⟨d, c⟩` | ι | ι[0] | ι ≺ ι[0], also the payload condition |
| main `recv d′` | ι[0] | ι+1 | ι[0] ≺ ι+1 |
| main `close d₁′` | ι[0]+1 | ι+1 | ι[0]+1 ≺ ι+1 |
| main `close c₁` | ι+1 | – | – |
| K `recv c′` | ι | φ | ι ≺ φ |
| K `send ⟨∗, e⟩` | ι[0] | φ, ι+1 | ι[0] ≺ both |
| K `close (…)` | ι[0]+1 | φ, ι+1 | ι[0]+1 ≺ both |
| K `close c₁′` | ι+1 | φ | ι+1 ≺ φ |

From the first `new`: ι ≺ ι[0], ι[0]+1 ≺ ι+1. Program order: ι[0] ≺ ι[0]+1. E-Abs: ι+1 ≺ φ. Second `new`: κ ≡ ι[0].

</details>

---

## 5. Example: an optional channel

```
O = !((S⁰@self[0]) ⊕ ∗).Close

R = λ^{ι+1}_ι ∗. let (m, c₁′) = recv c′ in
                  case m { inj₁ e ⇒ close (send ⟨∗, e⟩); close c₁′
                         | inj₂ u ⇒ u; close c₁′ }

some = let (c, c′) = new ι { ι ≺ ι[0],  ι[0]+1 ≺ ι+1 } ∗ in
       let (d, d′) = new κ { κ ≡ ι[0] } ∗ in
       spawn R;
       let c₁ = send ⟨inj₁ d, c⟩ in
       let (x, d₁′) = recv d′ in x; close d₁′; close c₁

none = let (c, c′) = new ι { ι ≺ ι[0],  ι[0]+1 ≺ ι+1 } ∗ in
       spawn R;
       close (send ⟨inj₂ ∗, c⟩)
```

- `none` still owes ι ≺ ι[0]: `heads` reads the type, and a sum's heads include both arms
- `none` still needs ι[0]+1 ≺ ι+1: E-Case types the `inj₁` arm of `R` too
- facts about a point where nothing lives constrain nothing at run time

`some_deadlock_free`, `some_swapped_deadlock_free` (spawn before the creation of d), `none_deadlock_free`, `op_ok`

---

## 6. Example: a cycle, and its deadlock

```
cycle = let (c, c′) = new γ {} ∗ in
        let (d, d′) = new ε { γ ≺ ε } ∗ in
        spawn (λ^ε_γ ∗. close c′; close d′);
        close c; close d

blocked = let (c, c′) = new γ {} ∗ in
          let (d, d′) = new ε { ? } ∗ in
          spawn (λ ∗. close d′; close c′);
          close c; close d
```

- `cycle`: both threads close at γ while holding ε, so both owe γ ≺ ε
- `blocked`: main owes γ ≺ ε, the thread owes ε ≺ γ, so no acyclic `?` exists

`cycle_deadlock_free`, `blocked_main`

---

## 7. Example: recursion, a request/reply server

```
A = µα. ?∗.α        requests, server side
B = µα. !∗.α        replies, server side

C = { ι+k ≺ ι′+k,   ι′+k ≺ ι+k+1   ∣  k ∈ ℕ }

srv = box f ∀ι ι′ {C}. λ^{ι′} ⟨a : A@ι, b : B@ι′⟩.
        let (x, a₁) = recv a in                              -- at ι, holds b at ι′
        x;
        spawn (λ ∗. (force f [ι+1, ι′+1]) ⟨a₁, send ⟨∗, b⟩⟩)   -- send at ι′, holds a₁ at ι+1

cli = box f ∀ι ι′ {C}. λ^{ι′} ⟨a : Ā@ι, b : B̄@ι′⟩.
        let a₁ = send ⟨∗, a⟩ in                              -- at ι, holds b at ι′
        let (x, b₁) = recv b in                              -- at ι′, holds a₁ at ι+1
        x;
        spawn (λ ∗. (force f [ι+1, ι′+1]) ⟨a₁, b₁⟩)

main = let (a, a′) = new γ {} ∗ in
       let (b, b′) = new ε { γ+k ≺ ε+k,  ε+k ≺ γ+k+1  ∣ k ∈ ℕ } ∗ in
       spawn (λ ∗. (force srv [γ, ε]) ⟨a, b⟩);
       (force cli [γ, ε]) ⟨a′, b′⟩
```

```
order : γ ≺ ε ≺ γ+1 ≺ ε+1 ≺ γ+2 ≺ …        request k ≺ reply k ≺ request k+1
call  : force f [ι+1, ι′+1] owes C[ι+1/ι, ι′+1/ι′] ⊆ C
```

`rq_call`, `rr_typed`, `rr_deadlock_free`

<details>
<summary>One round is not enough</summary>

With only the facts of one round, C₁ = { ι ≺ ι′, ι′ ≺ ι+1 }, the recursive call at (ι+1, ι′+1) owes ι+1 ≺ ι′+1, which C₁ and program order do not derive. Countermodel: 10(k+1) for ι+k and 15+k for ι′+k. A box constraint is an invariant of the whole recursion. `rr_call_underivable`

</details>

---

## 8. Example: recursion over received channels, the received chain

```
R = µα. ?(α@self[0]).Close
C = { ι[0]ⁿ + 1 ≺ ι[0]ⁿ⁺¹  ∣  n ∈ ℕ }          ι[0]ⁿ = ι[0][0]…[0], n times

rch  = box f ∀ι {C}. λ^{ι+1} c : R@ι.
         let (d, c₁) = recv c in                     -- d : R@ι[0]
         close c₁;
         spawn (λ^{ι[0]+1}_{ι[0]} ∗. (force f [ι[0]]) d)

sch  = box g ∀ι {C}. λ^{ι+1} c : R̄@ι.
         let (e, e′) = new κ { κ ≡ ι[0] } ∗ in
         let c₁ = send ⟨e, c⟩ in
         close c₁;
         spawn (λ^{ι[0]+1}_{ι[0]} ∗. (force g [ι[0]]) e′)

main = let (c, c′) = new ι {C} ∗ in
       spawn (λ^{ι+1}_ι ∗. (force sch [ι]) c′);
       (force rch [ι]) c
```

```
order : ι ≺ ι+1 ≺ ι[0] ≺ ι[0]+1 ≺ ι[0]² ≺ ι[0]²+1 ≺ …
call  : force f [ι[0]] owes C[ι[0]/ι] ⊆ C
```

`ch_sub`, `ch_typed`, `ch_deadlock_free`


---

## 9. Typing rules

Judgment $\Gamma ; \Delta \vdash_F t : T$, read "t runs with future F". The future $F$ is the points this thread will still act on after $t$: channels used by the code after $t$, held by values already computed and waiting, and inside a λ the caller's future, written φ. Other threads are not in $F$. A deadlock is a cycle of "blocked on p while still needing q", so a call that blocks at $p$ owes $p \prec F$: it blocks before the thread's future.

```
close c; close d        while `close c` runs, F = {point of d}: blocking on c means sitting on d
```

**The future grows left to right**

$$
\frac{\Gamma \vdash u \prec F \qquad \Gamma ; \Delta_1 \vdash_{F \cup \mathrm{heads}(\Delta_2)} t_1 : T \multimap^{u}_{\ell} U \qquad \Gamma ; \Delta_2 \vdash_{F \cup \{\ell\}} t_2 : T}
{\Gamma ; \Delta_1 \cdot \Delta_2 \vdash_F t_1\,t_2 : U}\ \;\text{E-App}
$$

**Abstraction meets application at $u$**

$$
\frac{\varphi \text{ fresh} \qquad \Gamma \vdash \ell \preceq \mathrm{heads}(\Delta) \qquad \Gamma, u \prec \varphi ; \Delta, x : T \vdash_{\{\varphi\}} t : U}
{\Gamma ; \Delta \vdash_F \lambda x.\,t : T \multimap^{u}_{\ell} U}\ \;\text{E-Abs}
$$

**Recursion: the only rule binding ∀**

$$
\frac{\Delta \text{ only } \Box \qquad \vec\iota, \varphi \text{ fresh} \qquad \Gamma, C, u \prec \varphi ; \Delta, x : B \vdash_{\{\varphi\}} t : T}
{\Gamma ; \Delta \vdash_F \mathsf{box}\ x.\,t : B}\ \;\text{E-Exp}
\qquad B = \Box(\forall\vec\iota.\,C.\ \ast \multimap^{u} T)
$$

**Existentials**

$$
\frac{\Gamma \vdash C[\vec p/\vec\iota] \qquad \Gamma \vdash \ell \preceq \mathrm{heads}(T[\vec p/\vec\iota]) \qquad \Gamma ; \Delta \vdash_F t : T[\vec p/\vec\iota]}
{\Gamma ; \Delta \vdash_F t : \exists^{\ell}\vec\iota.\,C.\ T}\ \;\text{E-Pack}
\qquad
\frac{x : \exists^{\ell}\vec\iota.\,C.\ T \in \Delta \qquad \vec\iota \text{ fresh}, \notin U \qquad \Gamma, C ; \Delta[x : T] \vdash_F t : U}
{\Gamma ; \Delta \vdash_F t : U}\ \;\text{E-Open}
$$

`let (c, c′) = new ι {C} ∗ in t` unfolds to E-LetPair, E-Pair, E-App, E-Let*, E-Open, E-LetPair (`t_new_open`).

<details>
<summary>All term rules</summary>

$$
\frac{}{\Gamma ; \cdot \vdash_F \ast : \ast}\;\text{E-Unit}
\qquad
\frac{K : \forall \vec x.\ C \Rightarrow T \qquad \Gamma \vdash C[\vec p/\vec x]}{\Gamma ; \cdot \vdash_F K : T[\vec p/\vec x]}\;\text{E-Const}
\qquad
\frac{}{\Gamma ; x : T \vdash_F x : T}\;\text{E-Var}
$$

$$
\frac{\Gamma ; \Delta_1 \vdash_{F \cup \mathrm{heads}(\Delta_2)} t_1 : T \qquad \Gamma ; \Delta_2 \vdash_{F \cup \mathrm{heads}(T)} t_2 : U}
{\Gamma ; \Delta_1 \cdot \Delta_2 \vdash_F \langle t_1, t_2 \rangle : T \otimes U}\;\text{E-Pair}
\qquad
\frac{\Gamma ; \Delta_1 \vdash_{F \cup \mathrm{heads}(\Delta_2)} t_1 : U \otimes V \qquad \Gamma ; \Delta_2, x : U, y : V \vdash_F t_2 : T}
{\Gamma ; \Delta_1 \cdot \Delta_2 \vdash_F \mathsf{let}\ (x,y) = t_1\ \mathsf{in}\ t_2 : T}\;\text{E-LetPair}
$$

$$
\frac{\Gamma ; \Delta_1 \vdash_{F \cup \mathrm{heads}(\Delta_2)} t_1 : \ast \qquad \Gamma ; \Delta_2 \vdash_F t_2 : T}
{\Gamma ; \Delta_1 \cdot \Delta_2 \vdash_F t_1 ; t_2 : T}\;\text{E-Let*}
\qquad
\frac{\Gamma ; \Delta \vdash_F t : T_i}{\Gamma ; \Delta \vdash_F \mathsf{inj}_i\,t : T_1 \oplus T_2}\;\text{E-Inj}
$$

$$
\frac{\Gamma ; \Delta_1 \vdash_{F \cup \mathrm{heads}(\Delta_2)} t : T_1 \oplus T_2 \qquad \Gamma ; \Delta_2, x_1 : T_1 \vdash_F t_1 : U \qquad \Gamma ; \Delta_2, x_2 : T_2 \vdash_F t_2 : U}
{\Gamma ; \Delta_1 \cdot \Delta_2 \vdash_F \mathsf{case}\ t\ \{x_1.t_1 ; x_2.t_2\} : U}\;\text{E-Case}
$$

$$
\frac{\Gamma ; \Delta \vdash_F t : T \qquad \Delta' \text{ only } \Box}{\Gamma ; \Delta, \Delta' \vdash_F t : T}\;\text{E-Weak}
\qquad
\frac{\Gamma ; \Delta, x : \Box T, y : \Box T \vdash_F t : U}{\Gamma ; \Delta, x : \Box T \vdash_F t[x/y] : U}\;\text{E-Contract}
\qquad
\frac{\Gamma ; \Delta \vdash_F t : T \qquad T \approx T' \text{ up to } \Gamma \vdash \equiv}{\Gamma ; \Delta \vdash_F t : T'}\;\text{E-Conv}
$$

plus E-App, E-Abs, E-Exp, E-Pack, E-Open above. $\Delta_1 \cdot \Delta_2$ copies □ entries to both sides.

**Processes** (runtime only, the proof uses them)

P-Term reads the *world-carrying* term judgment $\Theta ; \Delta \vdash^{W}_{F} t : T$ (`typed`). It has the same rules as the term rules above, with two differences:

- every side condition $\Gamma \vdash f$ is read as $W, \Gamma \vdash f$: the facts of the world are available as extra hypotheses (in Rocq `seqs W Ψ`, `slt W Ψ`). A running thread mentions channels created earlier, whose points are constants, and only W knows facts about them
- a channel environment Θ types the channel constants the thread mentions, with one more rule

$$
\frac{S_0 \approx S \qquad W, \Gamma \vdash q \equiv p}{c : S_0@q \,;\, \cdot \vdash^{W}_{F} c : S@p}\;\text{E-Chan}
$$

A source program has no channel constants, so `styped_typed` embeds every source derivation into this judgment with Θ = ∅, at any world. In other words: typing under W is typing with W added to Γ.

$$
\frac{\mathsf{prim}\,T \qquad \Theta_B \text{ both ends, dual at aliased points} \qquad \Sigma, \Theta_B ; \cdot \vdash^{W}_{\emptyset} t : T}
{\Sigma \vdash^{W} (\mathrm{dom}\,\Theta_B, \{\!\{t\}\!\}) : T}\;\text{P-Term}
\qquad
\frac{\Sigma_1, \Sigma_C \vdash^{W} (\chi_1, \pi_1) : T \qquad \Sigma_2, \overline{\Sigma_C} \vdash^{W} (\chi_2, \pi_2) : \ast }
{\Sigma_1, \Sigma_2 \vdash^{W} (\chi_1 \uplus \chi_2 \uplus \mathrm{dom}\,\Sigma_C,\ \pi_1 \uplus \pi_2) : T}\;\text{P-Connect}
$$

A process is a pair (χ, π): χ the restricted (internal) channels, π the soup of threads. P-Connect puts two soups side by side, and the channels of Σ_C, on which they talk, become internal.

</details>

<details>
<summary>Derivation of cycle</summary>

After both opens: $\Gamma = \{\gamma \prec \varepsilon\}$, $\Delta = c, c' : \mathsf{Close}@\gamma,\ d, d' : \mathsf{Close}@\varepsilon$.

**Spawned body**, under $\Gamma' = \Gamma, \varepsilon \prec \varphi$ and future $\{\varphi\}$:

$$
\dfrac{
  \dfrac{\Gamma' \vdash \gamma \prec \{\varphi, \varepsilon\}}{\Gamma' ; c' \vdash_{\{\varphi,\varepsilon\}} \mathsf{close}\ c' : \ast}\;\text{E-App}
  \qquad
  \dfrac{\Gamma' \vdash \varepsilon \prec \{\varphi\}}{\Gamma' ; d' \vdash_{\{\varphi\}} \mathsf{close}\ d' : \ast}\;\text{E-App}
}{
  \Gamma' ; c', d' \vdash_{\{\varphi\}} \mathsf{close}\ c' ; \mathsf{close}\ d' : \ast
}\;\text{E-Let*}
$$

$$
\dfrac{\Gamma \vdash \gamma \preceq \{\gamma, \varepsilon\} \qquad \Gamma, \varepsilon \prec \varphi ; c', d' \vdash_{\{\varphi\}} \mathsf{close}\ c' ; \mathsf{close}\ d' : \ast}
{\Gamma ; c', d' \vdash_F \lambda^{\varepsilon}_{\gamma}\ast.\ \mathsf{close}\ c' ; \mathsf{close}\ d' : \ast \multimap^{\varepsilon}_{\gamma} \ast}\;\text{E-Abs}
$$

**All obligations**

| action | blocks at | future | owes | from |
|---|---|---|---|---|
| main `close c` | γ | {ε} | γ ≺ ε | hyp |
| main `close d` | ε | ∅ | – | |
| `spawn` | never (no upper bound) | {γ, ε} | – | |
| thread `close c′` | γ | {φ, ε} | γ ≺ ε, γ ≺ φ | hyp, trans |
| thread `close d′` | ε | {φ} | ε ≺ φ | E-Abs hyp |
| `new ε {γ ≺ ε}` | never | | acyclic, conservative | `cc_ok` |

$C_0 = \emptyset$, $T = \ast$ ⟹ `soundness_source`.

</details>

---

## 10. The logical relation

**What the letters are.**

| symbol | in typing | in the relation |
|---|---|---|
| Γ | facts assumed (from C₀, boxes, opens, the λ hypothesis u ≺ φ) | replaced by W |
| W | – | a ground Γ: facts over the point constants created so far (its *support*), closed under the fact rules and strict |
| F | the future: points this thread will still act on after t (code after t, waiting values, the caller's future φ) | the same |
| Δ | variables in scope | closed by a substitution of values (grounding) |
| Θ | – | a term's channels: each channel with one end or with both ends (a thread owns both after `new`) |
| Σ | – | a process's interface: exactly one end per channel, the end it shows the outside |
| n | – | step index: how many steps the relation still looks at |

- Θ and Σ differ because a component shows only one end of each external channel, while inside a thread both ends of a fresh channel may sit together. `Θ(Σ)` reads Σ as a Θ.
- an *entry* is one end a term holds, `hd(e)` its point
- p is *known* to W when the name under p (its root: `root(κ+k) = root(κ[j]) = κ`) is in W's support. Values only use known points, so a later `new` can always pick a name nobody mentions
- W is used for two things: readiness compares points in W, and `new` grows W by a fresh extension
- Γ and W are the same kind of thing: statics assumes symbolic facts freely, semantics holds ground facts that must form a strict order and grow only freshly

**World** $W$: support (finite set of constants), relations $\equiv$, $\prec$. Well formed: congruence, transitivity, program order. **Strict**: $\prec$ irreflexive.

- $W \sqsubseteq W'$: $W'$ strict and contains $W$
- $W \sqsubseteq^{\mathrm{fresh}}_N W'$: additionally adds names $N$ and no fact between old points
- only `new` grows a world, and only freshly

**Readiness** (term, `below_rest`): a stuck term offers entries $O$, and

$$
\forall e \in O,\ e' \notin O.\ W \vdash \mathrm{hd}(e) \prec \mathrm{hd}(e')
\qquad\land\qquad
\forall e \in O,\ q \in F.\ W \vdash \mathrm{hd}(e) \prec q
$$

Process (`above_offered`): every unoffered entry lies above some offered one.

**Key clauses**

$$
\frac{\mathit{fchans}(t) = \mathrm{dom}\,\Theta \quad W \vdash \ell \preceq \mathrm{heads}(\Theta) \quad
\forall W' \sqsupseteq W,\, j < n,\, v \in \mathcal{V}^{j}_{W'}\llbracket \Theta' \vdash T \rrbracket,\, F \text{ with } W' \vdash u \prec F.\ \ t[v/x] \in \mathcal{E}^{j}_{W'}\llbracket \Theta \cdot \Theta' \vdash U \rrbracket_F}
{\lambda x.\,t \in \mathcal{V}^{n}_{W}\llbracket \Theta \vdash T \multimap^{u}_{\ell} U \rrbracket}\;\text{V-Abs}
$$

$$
\frac{\mathit{fchans}(t) = \emptyset \quad \forall W' \sqsupseteq W,\, \vec p \text{ known},\, W' \vdash C[\vec p/\vec\iota].\ \ \lambda\ast.\,t[\mathsf{box}\,x.t/x] \in \mathcal{V}^{n}_{W'}\llbracket \cdot \vdash (\ast \multimap^u T)[\vec p/\vec\iota] \rrbracket}
{\mathsf{box}\ x.\,t \in \mathcal{V}^{n}_{W}\llbracket \cdot \vdash \Box(\forall\vec\iota.\,C.\ \ast \multimap^u T) \rrbracket}\;\text{V-Box}
$$

$$
\frac{\neg\,\mathrm{irred}\,t \Rightarrow \mathrm{ready}_W(\Theta \mid F, t) \qquad \mathrm{irred}\,t \Rightarrow t \in \mathcal{V}^{n+1}_{W}\llbracket \Theta \vdash T \rrbracket \qquad \forall t \xrightarrow{\lambda} t'.\ \mathrm{obl}^{n+1}_{W;\Theta\mid F}(t \xrightarrow{\lambda} t' : T)}
{t \in \mathcal{E}^{n+1}_{W}\llbracket \Theta \vdash T \rrbracket_F}\;\text{E-Intro}
$$

$$
\frac{\exists\,\kappa \text{ fresh},\ W \sqsubseteq^{\mathrm{fresh}}_{\{\kappa\}} W'.\ \ t' \in \mathcal{E}^{n-1}_{W'}\llbracket \Theta, c : S@\kappa \cdot \overline{S}@\kappa \vdash T \rrbracket_F}
{\mathrm{obl}^{n}_{W;\Theta\mid F}(t \xrightarrow{\mathsf{new}\,c} t' : T)}\;\text{O-New}
$$

- step index $n$; send, close, link keep $n$ (they give a resource away), all else costs 1
- the only syntactic conditions: $\mathit{fchans}$ in V-Abs, V-Box, Q-Send

<details>
<summary>All clauses</summary>

**Values**

$$
\frac{}{\ast \in \mathcal{V}\llbracket\cdot \vdash \ast\rrbracket}\;\text{V-Unit}
\qquad
\frac{S_0 \approx S \quad W \vdash q \equiv p}{c \in \mathcal{V}^n_W\llbracket c : S_0@q \vdash S@p\rrbracket}\;\text{V-Chan}
\qquad
\frac{K : T_0 \text{ instance under } W \quad T_0 \approx_W T}{K \in \mathcal{V}^n_W\llbracket \cdot \vdash T\rrbracket}\;\text{V-Const}
$$

$$
\frac{v_1 \in \mathcal{V}\llbracket\Theta_1 \vdash T\rrbracket \quad v_2 \in \mathcal{V}\llbracket\Theta_2 \vdash U\rrbracket}{\langle v_1, v_2\rangle \in \mathcal{V}\llbracket\Theta_1 \cdot \Theta_2 \vdash T \otimes U\rrbracket}\;\text{V-Pair}
\qquad
\frac{v \in \mathcal{V}\llbracket\Theta \vdash T_i\rrbracket}{\mathsf{inj}_i\,v \in \mathcal{V}\llbracket\Theta \vdash T_1 \oplus T_2\rrbracket}\;\text{V-Inj}
$$

$$
\frac{W \vdash \ell \preceq \mathrm{heads}(\Theta) \quad \vec p \text{ known} \quad W \vdash C[\vec p/\vec\iota] \quad v \in \mathcal{V}^n_W\llbracket\Theta \vdash T[\vec p/\vec\iota]\rrbracket}{v \in \mathcal{V}^n_W\llbracket\Theta \vdash \exists^\ell\vec\iota.\,C.\ T\rrbracket}\;\text{V-Ex}
$$

plus V-Abs, V-Box.

**Term obligations**

$$
\frac{t' \in \mathcal{E}^{n-1}_W\llbracket\Theta \vdash T\rrbracket_F}{\mathrm{obl}(t \xrightarrow{\beta} t')}\;\text{O-Beta}
\qquad
\frac{v \in \mathcal{V}^n_W\llbracket\Theta_1 \vdash \ast \multimap^u_\ell \ast\rrbracket \quad t' \in \mathcal{E}^{n-1}_W\llbracket\Theta_2 \vdash T\rrbracket_F}{\mathrm{obl}_{W;\Theta_1\cdot\Theta_2\mid F}(t \xrightarrow{\mathsf{spawn}\,v} t')}\;\text{O-Spawn}
$$

$$
\frac{v \in \mathcal{V}^n_W\llbracket\Theta_2 \vdash U[p/\mathit{self}]\rrbracket \quad t' \in \mathcal{E}^{n}_W\llbracket\Theta_1, c : S@(p+1) \vdash T\rrbracket_F}{\mathrm{obl}_{W;(\Theta_1, c : (!U.S)@p)\cdot\Theta_2\mid F}(t \xrightarrow{c!v} t')}\;\text{O-Send}
$$

$$
\frac{\forall W' \sqsupseteq W,\, j \le n-1,\, v \in \mathcal{V}^j_{W'}\llbracket\Theta_2 \vdash U[p/\mathit{self}]\rrbracket.\ \ t' \in \mathcal{E}^j_{W'}\llbracket(\Theta_1, c : S@(p+1))\cdot\Theta_2 \vdash T\rrbracket_F}{\mathrm{obl}_{W;\Theta_1, c : (?U.S)@p\mid F}(t \xrightarrow{c?v} t')}\;\text{O-Recv}
$$

$$
\frac{t' \in \mathcal{E}^n_W\llbracket\Theta_1 \vdash T\rrbracket_F}{\mathrm{obl}_{W;\Theta_1, c:\mathsf{Close}@p\mid F}(t \xrightarrow{\mathsf{end}\,c} t')}\;\text{O-Close}
\qquad
\frac{S_d \bowtie S_c \quad W \vdash p \equiv q \quad t' \in \mathcal{E}^n_W\llbracket\Theta_1 \vdash T\rrbracket_F}{\mathrm{obl}_{W;\Theta_1, c : S_c@p, d : S_d@q\mid F}(t \xrightarrow{\mathsf{link}\,c\,d} t')}\;\text{O-Link}
$$

**Processes**

$$
\frac{\mathrm{irred}\,P \Rightarrow P = (\emptyset, \{\!\{v, \ast, \ldots\}\!\}),\ v \in \mathcal{V}^{n+1}_W\llbracket\Sigma \vdash T\rrbracket \quad \neg\mathrm{irred}\,P \Rightarrow \mathrm{ready}_W(\Sigma, P) \quad \forall P \xrightarrow{\pi} P'.\ \mathrm{obl}^{n+1}_{W;\Sigma}(P \xrightarrow{\pi} P' : T)}{P \in \mathcal{P}^{n+1}_W\llbracket\Sigma \vdash T\rrbracket}\;\text{P-Intro}
$$

$$
\frac{(\chi'\cap\mathrm{dom}\,\Sigma = \emptyset) \Rightarrow \exists N \text{ fresh},\ W \sqsubseteq^{\mathrm{fresh}}_N W'.\ \ (\chi',\pi') \in \mathcal{P}^{n\ominus\pi}_{W'}\llbracket \Sigma \vdash T \rrbracket}
{\mathrm{obl}^{n}_{W;\Sigma}((\chi,\pi) \xrightarrow{\tau} (\chi',\pi') : T)}\;\text{Q-Tau}
$$

(for the τ of a `link` additionally $(\chi',\pi') \in \mathcal{P}^{n}_{W}\llbracket \Sigma \vdash T \rrbracket$, same world, same index)

$$
\frac{\forall W' \sqsupseteq W,\ j \le n-1,\ \Theta_2 \text{ with } \mathrm{dom}\,\Theta_2 \cap \chi = \emptyset,\ v \in \mathcal{V}^{j}_{W'}\llbracket \Theta_2 \vdash U[p/\mathit{self}] \rrbracket.\ \ (\chi' \cup B,\ \pi') \in \mathcal{P}^{j}_{W'}\llbracket (\Sigma_1, c : S@(p+1)) \triangleright \Theta_2 \vdash T \rrbracket}
{\mathrm{obl}^{n}_{W;\,\Sigma_1, c : (?U.S)@p}((\chi,\pi) \xrightarrow{c?v} (\chi',\pi') : T)}\;\text{Q-Recv}
$$

(B: the channels the message brings both ends of, or the partner end of; they become restricted, ▷ removes their entries)

$$
\frac{\mathrm{dom}\,\Theta_e = \mathit{fchans}(v) \cap \chi \quad \Theta_e,\Sigma_e \text{ dual at aliased points} \quad v \in \mathcal{V}^{n}_{W}\llbracket \Sigma_v, \Theta_e \vdash U[p/\mathit{self}] \rrbracket \quad (\chi',\pi') \in \mathcal{P}^{n}_{W}\llbracket \Sigma_0, \Sigma_e, c : S@(p+1) \vdash T \rrbracket}
{\mathrm{obl}^{n}_{W;\,\Sigma_0, \Sigma_v, c : (!U.S)@p}((\chi,\pi) \xrightarrow{c!v} (\chi',\pi') : T)}\;\text{Q-Send}
$$

(the message carries restricted channels Θ_e out; their partner ends Σ_e stay and join the interface. No condition on topology)

$$
\frac{(\chi',\pi') \in \mathcal{P}^{n}_{W}\llbracket \Sigma_1 \vdash T \rrbracket}
{\mathrm{obl}^{n}_{W;\,\Sigma_1, c : \mathsf{Close}@p}((\chi,\pi) \xrightarrow{\mathsf{end}\,c} (\chi',\pi') : T)}\;\text{Q-Close}
\qquad
\frac{c \ne d \quad S_d \bowtie S_c \quad W \vdash p \equiv q \quad (\chi',\pi') \in \mathcal{P}^{n}_{W}\llbracket \Sigma_1 \vdash T \rrbracket}
{\mathrm{obl}^{n}_{W;\,\Sigma_1, c : S_c@p, d : S_d@q}((\chi,\pi) \xrightarrow{\mathsf{link}\,c\,d} (\chi',\pi') : T)}\;\text{Q-Link}
$$

$n \ominus \pi$: the index stays for send, close and link (a resource is given away), it drops by one otherwise.

</details>

---

## 11. Statements

**Soundness** (`soundness`).

$$
W \text{ strict},\quad \cdot \vdash^{W} P : T \;\Longrightarrow\; P \text{ deadlock free}
$$

**Soundness for source programs** (`soundness_source`).

$$
\mathsf{cc\_ok}_{\emptyset}(C_0),\quad \mathsf{prim}\,T,\quad C_0 ; \cdot \vdash_{\emptyset} t : T
\;\Longrightarrow\; (\emptyset, \{\!\{ t \}\!\}) \text{ deadlock free}
$$

$C_0$ is the program's creation constraint over its top-level points: `cc_ok` against the empty context, which is acyclicity (nothing old exists, so conservativity is trivial). It gives a strict world (`wc0_strict`), `styped_typed` embeds the derivation, then `soundness`.

**Fundamental property** (`fundamental`, `fundamental_proc`). At every strict world:

$$
\Theta ; \Delta \vdash^{W}_F t : T \Rightarrow \Theta ; \Delta \models^{W}_F t : T
\qquad
\Sigma \vdash^W P : T \Rightarrow \Sigma \models^W P : T
$$

One compositionality lemma per rule (`sem_typed_app`, `sem_typed_lam`, `sem_typed_box`, `sem_typed_pack`, `sem_typed_open`, …, `Prel_term`, `Prel_connect`).

**Adequacy** (`adequacy`). $\cdot \models^W P : T \Rightarrow P$ deadlock free.
Via `Prel_steps` (the relation survives $n$ reductions at some world) and `Prel_safe` (index ≥ 1 and empty interface ⟹ safe).

**Amalgamation** (`amalgamation`). For strict $W_1, W_2$ and $A = \mathrm{supp}\,W_1 \cap \mathrm{supp}\,W_2$:

$$
\mathrm{strict}(W_1 \sqcup W_2) \iff \mathrm{strict}(W_1|_A \sqcup W_2|_A)
$$

**Fresh extension** (`fresh_extension`).

$$
W_1 \sqsubseteq^{\mathrm{fresh}}_N W_1',\ \ \mathrm{supp}\,W_2 \cap N = \emptyset,\ \ W_2,\ W_1 \sqcup W_2 \text{ strict}
\;\Longrightarrow\; W_1' \sqcup W_2 \text{ strict}
$$

**Cut** (`Prel_connect`). Interfaces dual at aliased points, $W \sqcup W$ strict:

$$
(\chi_1, \pi_1) \in \mathcal{P}^n_W\llbracket\Sigma_1, \Sigma_C \vdash T\rrbracket,\ \ (\chi_2, \pi_2) \in \mathcal{P}^n_W\llbracket\Sigma_2, \overline{\Sigma_C} \vdash \ast\rrbracket
\;\Longrightarrow\; (\chi_1 \uplus \chi_2 \uplus \mathrm{dom}\,\Sigma_C,\ \pi_1 \uplus \pi_2) \in \mathcal{P}^n_W\llbracket\Sigma_1, \Sigma_2 \vdash T\rrbracket
$$

Readiness of the composite: walk from an unoffered entry along cut channels, each step strictly descending in $W$. Strictness bounds the walk. **No tree topology needed.**

<details>
<summary>Compositionality of E-Abs and E-Exp</summary>

**`sem_typed_lam`**

$$
\Theta ; \Delta, x : T \models^{W}_{\{\varphi\}} t : U,\ \ W \vdash \ell \preceq \mathrm{heads}(\Theta) \cup \mathrm{heads}(\Delta),\ \ \mathit{wf}
\;\Longrightarrow\; \Theta ; \Delta \models^{W}_F \lambda x.\,t : T \multimap^u_\ell U
$$

**`sem_typed_box`** ($\Delta$ only □, $B = \Box(\forall\vec\iota.\,C.\ \ast \multimap^u T)$)

$$
\cdot ; \Delta, x : B \models^{W}_{\{\varphi\}} t : T,\ \ \mathit{wf}
\;\Longrightarrow\; \cdot ; \Delta \models^{W}_F \mathsf{box}\ x.\,t : B
$$

Proof by well-founded induction on the index: V-Abs reads its argument at a strictly smaller index, so the box is available for its own recursive call.

</details>

---

## 12. Extensions

### Choice

```
S ::= … | ⊕{S₁, S₂} | &{S₁, S₂}

select_i : ⊕{S₁, S₂}@x ⊸^x S_i@x[i]              owes x ≺ x[i]
branch   : &{S₁, S₂}@x ⊸^x S₁@x[0] ⊕ S₂@x[1]     owes x ≺ x[0], x ≺ x[1]
```

**Semantics.** Two new labels, `c◁i` (select branch i) and `c▷i` (offer, branch i taken):

$$
\mathsf{select}_i\ c \xrightarrow{c\triangleleft i} c
\qquad
\mathsf{branch}\ c \xrightarrow{c\triangleright i} \mathsf{inj}_i\ c
\qquad
\frac{t \xrightarrow{c\triangleleft i} t' \quad u \xrightarrow{c\triangleright i} u'}{(\chi, \pi \uplus \{\!\{t, u\}\!\}) \xrightarrow{\tau} (\chi, \pi \uplus \{\!\{t', u'\}\!\})}\;\text{P-Act-Choice}
$$

**Relation.** Selecting gives like a send (index kept), branching waits like a receive (index − 1, no payload, so no later world):

$$
\frac{t' \in \mathcal{E}^{n}_W\llbracket \Theta, c : S_i@x[i] \vdash T \rrbracket_F}
{\mathrm{obl}^{n}_{W;\,\Theta, c : \oplus\{S_1,S_2\}@x \mid F}(t \xrightarrow{c\triangleleft i} t' : T)}\;\text{O-Select}
\qquad
\frac{t' \in \mathcal{E}^{n-1}_W\llbracket \Theta, c : S_i@x[i] \vdash T \rrbracket_F}
{\mathrm{obl}^{n}_{W;\,\Theta, c : \&\{S_1,S_2\}@x \mid F}(t \xrightarrow{c\triangleright i} t' : T)}\;\text{O-Branch}
$$

plus Q-Select and Q-Branch for processes, and readiness treats `c◁i` like a send and `c▷i` like a receive.

- branch i continues at the payload point `x[i]`: same channel, a point of its own per branch
- no new name, no new fact rule: two constants, two labels, two relation clauses
- encodable from sums and delegation (`ChoiceEnc.v`), which allocates a channel per selection

```
c : ⊕{A: !∗.Close, B: !∗.Close}      d : Close
T1 = select_A c; send ∗ c; close c
T2 = branch c { A ⇒ close d; recv c; close c
              | B ⇒ recv c; close d; close c }
T3 = close d

branch A owes  δ ≺ a[0]          branch B owes  a[1] ≺ δ ≺ a[1]+1
```

- one shared continuation point would give a cycle, two points do not
- status: on `cfst` with every example (`bo_deadlock_free` for T1–T3), being merged into `exists`

### Context-free session types

```
S ::= Skip | S;S | !T | ?T | ⊕(S,S) | &(S,S) | Close | µX.S | X | X̄

sendTree : □(∀ι ζ α. C. (TreeC;α)@ι ⊸^ζ ∃ι′. C′. α@ι′)
C  = { q ≺ ζ,  q ≺ q[0],  q ≺ q[1]  ∣  q ∈ walks(ι) }
C′ = { ι ≺ ι′ } ∪ { q ≺ ζ,  q ≺ q[0],  q ≺ q[1]  ∣  q ∈ walks(ι′) }

walks(p) = { p w ∣ w ∈ (+1 | [0] | [1])* }      e.g.  ι[1]+1+1[0]
```

```
TreeC = µX. ⊕{ Leaf: Skip,  Node: !Int; X; X }

sendTree = box f ∀ι ζ α {C}. λ^ζ ⟨t : Tree, c : (TreeC;α)@ι⟩.
  case t {
    Leaf          ⇒ select_Leaf c                          -- at ι, result α@ι[0], pack ι′ := ι[0]
  | Node t₁ x t₂  ⇒ let c₁ = select_Node c in              -- at ι, c₁ : (!Int;TreeC;TreeC;α)@ι[1]
                   let c₂ = send ⟨x, c₁⟩ in                -- at ι[1]
                   let c₃ = (force f [ι[1]+1, ζ, TreeC;α]) ⟨t₁, c₂⟩ in   -- open: c₃ at κ, ι[1]+1 ≺ κ
                   (force f [κ, ζ, α]) ⟨t₂, c₃⟩            -- open at κ′, pack ι′ := κ′
  }
```

- every action happens at a walk of ι, so below ζ: the upper bound ζ is justified
- the first call owes C at ι[1]+1, a walk of ι, so C[ι[1]+1/ι] ⊆ C
- the second call owes C at κ, which the first call's C′ supplies
- `Tree` is not in the calculus: the mechanization types drain and copy, where the tree arrives on a channel (`TreeCopy.v`)

- new in types only: Skip, `;`, session variables α under □, conversion up to bisimilarity
- no new fact rule: ζ is an ordinary point variable, the ceiling an infinite set of ordinary facts
- a walk appends steps to a point, `+1` for an action and `[i]` for branch i of a choice, read left to right. In Rocq `pwalk ι w`
- typed: tree copy and drain, two streams, Milner's scheduler, treeSum, the arithmetic server; the classic deadlock rejected
- outside: `sendTree t c; close d; send v c`, where `d` must sit between the segment's end and the continuation. Mordido–Pérez cannot type it either
- `q ≺ q[i]` is what `select` owes at every walk point, so the box constraint states it once for all of them
- status: ported to the `exists` core on `cfst` (6cf4f54), being merged into `exists`. Mordido–Pérez v1–v3 translations closed (`mp3_deadlock_free_source`)

---

## 13. What we subsume, and how

| system | what types | how |
|---|---|---|
| PGV (Kokke–Dardha) | every closed program of PGV minus 0/absurd, with monotone payload-bounded sessions (`pgv_deadlock_free_source`) | one world ranks points by priority (`Wpgv`), translation plus simulation |
| Padovani–Novara | every closed program whose `fix` has the form `fix f. λx. t` (`pn_deadlock_free_source`) | one top-level constraint covers every level shift (`Crel`), translation plus simulation |
| Mordido–Pérez (context-free) | all their examples: tree channel, two streams, repaired classic deadlock; Milner's scheduler beyond their rules | informal; a priority becomes a point, `new`'s sequence n₁+k·n₂ the instants of a channel, their ⊤ effect our ceiling |

- deadlock freedom holds in each source semantics, not only for the image
- the PGV embedding found two programs PGV types that deadlock (`cx1_rejected`, `cx2_rejected`)
- Mordido–Pérez as printed accept programs that deadlock; we compare with their examples, not their rules
- priorities fix a witness in the program text, orders state only the facts
