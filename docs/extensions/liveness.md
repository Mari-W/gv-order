# Liveness: no τ-divergence, and the road to lock freedom

Branch `liveness`. The logical relation of ORDERS-SPEC §7 proves deadlock
freedom. This note changes the cost of steps so that adequacy also proves that
every maximal run of a closed program terminates or performs infinitely many
channel steps. It follows a suggestion of Emanuele D'Osualdo. Observable events
recur coinductively and τ steps recur inductively. Step indexing simulates the
coinduction, so the relation at n speaks about prefixes with n observations,
and a genuine least fixpoint over τ steps rules out infinite τ sequences inside
every prefix.

Rocq lives in `theories/liveness/`. Section 10 lists what is closed.

## 1  Results

Closed programs, `Σ = ∅`. The live semantic judgment is `⊨ˡ`, defined in §3.

```
Theorem live_adequacy W T p :
  (∀ n, LPrel n W ∅ T p) →
  deadlock_free p ∧ no_tau_divergence p.

no_tau_divergence p := ∀ q, pred_star p q → Acc (λ y x, padmin x y) q

Corollary live_runs W T p (f : nat → proc) :
  (∀ n, LPrel n W ∅ T p) → f 0 = p → (∀ i, preduction (f i) (f (S i))) →
  ∀ i, ∃ j, i ≤ j ∧ pchan (f j) (f (S j)).
```

`padmin` is a τ of P-Act-Beta, P-Act-New or P-Act-Spawn. `pchan` is a τ of
P-Act-Msg, P-Act-Close, P-Act-Choice or P-Act-Link. Every τ is one of the two
(`ptau_classify`). A finite maximal run ends in a terminated state by deadlock
freedom. An infinite run takes a channel step after every position. Together
this is "every maximal run terminates or performs infinitely many channel
steps".

Lock freedom under a fair scheduler does not follow from these two properties.
Section 9 gives the counterexample and the extra conditions that suffice.

## 2  Costs

A step taken at index n carries its obligation at n − cost. Cost 0 means the
same index, read inductively.

| Step | Today (sharp edge 45) | Live |
|---|---|---|
| β, let, let-pair, case, force (label `LBeta`) | 1 | 0, inductive |
| new | 1 | 0, inductive |
| spawn | 1 | 0, inductive |
| receive, branch | 1 | 1 |
| send, select, close, link | 0, inductive on size | 1 |
| process τ of β, new, spawn | 1 | 0, inductive |
| process τ of a message, a close, a choice | 1 | 2 |
| process τ of a link (P-Act-Link) | 1 and 0 | 1 |
| external process label (`PSess σ`) | as the thread label | 1 |

The payload of a send moves from index n to n − 1, the index of the
continuation. A receive still quantifies over j ≤ n − 1.

### Why a synchronization costs 2

The rule is that a composite pays at least what one component pays
sequentially for the same step. Components that run in parallel pay in
parallel.

Internalizing a link (`Internalize.v`) fuses the free ends c and d of one
process p into the restricted channel d of q. One synchronization of q on d is
a send of p on c followed by a receive of p on d, two observations of p. With
sends at cost 1 and a synchronization at cost 1, q would need `P_{n−1}` where p
offers only `P_{n−2}`. This is the halving budget of sharp edge 44, which sharp
edge 45 removed by making the send free. A synchronization at cost 2 restores
`P_n ⇒ P_n`. The successor of q needs `P_{n−2}`, p's send gives its successor
at n − 1 with the payload at n − 1, and p's receive at j = n − 2 takes the
payload by downward closure and gives `P_{n−2}`. A close of q on d is a close
of p on c and one on d, cost 1 + 1. A choice is a select and a branch, 1 + 1.
A link τ of q is one external link of p, cost 1.

P-Connect composes two components over a cut. A synchronization on a cut
channel is a send of one component and a receive of the other, each at cost 1,
in parallel. The composite pays 2, more than either component, so the
induction on n closes after one downward closure. A link τ of one component
fuses the other at its current index, which is downward closed to n − 1.

P-Term turns a thread into a one-thread process with the same costs. P-Join
and `Prel_indep` compose independently, so the composite pays the maximum.

The new costs also remove two devices. Giving steps no longer need to shrink
the term (`tstep_giving_size`, `esize`, `msize`, sharp edges 46 and 47),
because links and sends leave the inductive layer. The τ of P-Act-Link no
longer carries a second obligation at the same index (sharp edge 45,
encoding paragraph).

Feasibility verdict for point 2 of the plan. Sends at cost 1 are compatible
with every composition lemma once a synchronization costs 2. No lemma
statement changes. The assessment is a case analysis of the steps of q in
Internalize and of the composite in P-Connect, recorded above. The
composition proofs themselves are not ported on this branch (§10).

## 3  The relation

Levels by course-of-values recursion on n, as today. Inside level n the value
relation recurs on the type and the term and process relations are least
fixpoints over the τ steps of cost 0. Level 0 holds everything for E and P.

### V at level n

As today except the arrow, which now reads the argument and the body at every
j ≤ n, the current level included.

```
Vfunˡ_n W Θ (T ⊸^{ub}_{lb} U) (λ.e) :=
  fchans e = dom Θ ∧ lb ≼_W heads Θ ∧
  ∀ W' j Θ' Θ'' w F, W ⊑ W' → j ≤ n → Θ'' = Θ, Θ' → ub ≺_{W'} F →
    V_j W' Θ' T w → E_j W' Θ'' U F (e[w/0])
```

Here V_j and E_j are the lower levels when j < n, and V_n at T and the
inductive E_n at U when j = n. The quantification over j keeps V downward
closed, because the argument type sits in negative position.

V at level n refers to E at level n, and E at level n refers to V at level n
only at the type of its own term (E-Stop) and at ∗ ⊸ ∗ (spawn, inlined).
Every payload is read at n − 1, which is why sends at cost 1 matter for the
definition as well. The box reads the arrow at an instance of its body, which
is not a subterm. Instantiation of points and session variables keeps the
shape of a type, so V recurs on `tsize`, the number of type constructors
outside session types, with fuel (`Vdefˡ`).

### E at level n

`Eind below n VT T W Θ F e` is an inductive predicate with one constructor. VT
is the value relation at level n for the type T of the term, T itself is
needed for the lower levels. Both are indices, because the spawned thread is
read at ∗. The premises hold in every future world W1 ⊒ W (Kripke style, §4).

```
∀ W1, W ⊑ W1 →
  (irred e → VT W1 Θ e)                                         E-Stop
  ∧ (¬ irred e → ready_t W1 Θ F e)                               E-Step
  ∧ (∀ e', e --β--> e' → Eind VT T W1 Θ F e')                     O-Beta
  ∧ (∀ c e', e --νc--> e' → c ∉ dom Θ → ∀ L,
       ∃ a s s' W', a ∉ L ∪ roots(Θ, T, F) ∧ s ⊥ s' ∧ W1 ⊑ₒ W' ∧
         Eind VT T W' (Θ, c : (s@a, s'@ā)) F e')                  O-New
  ∧ (∀ w e', e --⇑w--> e' →
       ∃ Θ1 Θ2 ub lb, Θ = Θ1, Θ2 ∧ Vspawn_n W1 Θ1 ub lb w ∧
         Eind VT T W1 Θ2 F e')                                    O-Spawn
  ∧ (∀ σ e', e --σ--> e' → Eobl_σ (levels < n) W1 Θ T F σ e')     O-σ
```

`Vspawn_n` is `Vfunˡ_n` at ∗ ⊸ ∗ with `E_n` read as `Eind (λ _ Θ v, Θ = ∅ ∧
v = ∗) ∗`. `Eobl_σ` is today's obligation of the six session labels with every
successor at n − 1 and the payload of O-Send at n − 1.

O-New and Q-Admin quantify cofinitely over the fresh names. For every finite
set L the term finds a fresh point outside L. Today's O-New finds one point
fresh for Θ, T and F, and the bind lemma then renames it away from the
context's environment and the hole's type (`Erel_new_rename`). The cofinite
form lets the bind lemma and P-Connect pick L to cover the context, so the
τ layer needs no renaming lemma. E-New produces the cofinite form directly,
because its successor is a value.

### P at level n

`Pind below n VT T W Σ p`, one constructor, premises in every W1 ⊒ W.

```
P-Stop, P-Step                                       as today, at W1
∀ p', padmin p p' → p'.1 # dom Σ → ∀ L,
  ∃ N W', N # L ∪ roots(Σ, T) ∧ W1 ⊑ₒ W' ∧ Pind VT T W' Σ p'   Q-Admin
∀ p', pcomm p p' → Ptau_case (P_{n−2}) W1 Σ T p'          Q-Comm
∀ p', ptau_link p p' → Ptau_case (P_{n−1}) W1 Σ T p'      Q-Link
∀ σ p', p --σ--> p' → Pobl_σ (levels < n) W1 Σ T p σ p'    Q-σ, cost 1
```

## 4  Why Kripke-style premises

P-Connect and P-Term compose two derivations inside one level. With premises
at W only, the proof inducts on both fixpoints. When the second component
creates a channel at a fresh extension W'', the first must be moved to W'' by
monotonicity, and the moved derivation is not a subderivation of the first, so
the inner induction hypothesis does not reach it. With premises stated in
every future world, the first component keeps its derivation at its base world
W and is read at W'' ⊒ W directly. The composition statement quantifies over
the composite's world above both base worlds. Monotonicity in the world is then
the definition. Sharp edge 45 (encoding paragraph) met the same wall and avoided
world extension at the link τ. Fuel bounds `∃ k` with k kept by monotonicity
would also work, but they need uniform bounds over the name chosen at new.

## 5  β, Tait style

The fundamental case for application follows Tait. A value in `V_n(T ⊸ U)`
applied to `w ∈ V_n(T)` β-steps at cost 0 to a body in `E_n(U)`, which is an
inductive derivation and hence a termination certificate. `Erel_beta_det`
turns a term whose only step is a β to a related term into a related term at
the same index. E-App binds the function and the argument with Erel_bind as
today. Their channel steps lower the index, their τ steps stay inside the
fixpoint. At the β the indices meet at some m, and the j = m clause of the
arrow gives the body in `E_m`.

## 6  Recursion and guardedness

Forcing a box unrolls the recursion with a β, at cost 0. Today E-Exp is proved
by induction on the index, using the one step that the unrolling costs. Now
the self reference has to be paid for by a channel step.

Decision. The self variable of a box is a later hypothesis, and a channel step
discharges it.

```
Θ ; Δ, ▷x : □A ⊨ˡ e : T :=
  ∀ n W' Θ' γ, … , (∀ j < n, V_j W' ∅ (□A) (γ x)) →
    grounding_n of Δ … → E_n W' Θ'' T F (e[γ])

E-Exp-Live:  Δ unlimited ∧ (∀ instances, ∅ ; Δ, ▷x:□A ⊨ˡ e : A_inst)
             ⟹ ∅ ; Δ ⊨ˡ !e : □A                          (Löb on n)
```

The discharge is a semantic lemma about guarded terms. `Eg_n` is `Eind` with
E-Stop replaced by False, so a guarded term cannot return before its first
channel step, and that step leaves it at n − 1.

```
E-Guard-Let:  Θ1 ; Δ1 ⊨ˡ▷ e1 : U   and   Θ2 ; Δ2, Δ', y : U ⊨ˡ e2 : T
              ⟹ Θ ; Δ1, Δ2, ▷Δ' ⊨ˡ let y = e1 in e2 : T
E-Guard-Prim: send, recv, close, select, branch applied to values are guarded
E-Guard-Seq:  let y = e1 in e2 is guarded when e2 is guarded
E-Guard-Case: case is guarded when both branches are guarded
```

The condition is a property of the semantic relation, not a syntactic
premise. A static judgment `⊢▷` would be read off these lemmas.

Rejected. Instantiating the recursive call at strictly shifted points of a
channel the body acts on. The index counts channel steps, and a point records
the actions on a channel, not which thread performed them. A fresh extension
at new may alias the new channel's point to ι+1 (`wext_fresh` constrains only
facts between old names), so a body can call itself at ι+1 after a new and a
spawn, without a channel step, forever. Kobayashi's forwarder server below
is a second witness. Its recursive call sits at a different point and its run
diverges in τ.

The examples.

| Example | Self call after | Guarded |
|---|---|---|
| forwarder `fwd` (Forwarder.v) | recv a, send b | yes |
| producer `fprod` | send e | yes, needs sends at cost 1 |
| consumer `fcons` | recv c | yes |
| rounds `rbody` (SemRounds.v) | two sends | yes, needs sends at cost 1 |
| sendTree (SendTreeType.v, type only) | a select | yes |
| Kobayashi's server `fwsrv` (KobForwarder.v) | new and spawn only | no |

`fwsrv` takes the recursive branch on every run. Each call creates a reply
channel, spawns the next call and blocks. The spawned call does the same
before any channel step. The run is an infinite sequence of new, spawn and β
with no channel step, so the program τ-diverges and the live relation rightly
rejects it. It stays deadlock free, and the old relation accepts it.

## 7  Spawn

Spawn is a τ at both levels. At the term level O-Spawn inlines the spawned
closure at level n, so the spawned body's τ steps before its first channel step
belong to the parent's derivation. A chain of spawns in which every spawned
thread spawns again before acting is therefore finite, and infinite spawn
chains need recursion, which §6 guards. At the process level Q-Admin covers
P-Act-Spawn.

## 8  Adequacy

`LPrel_steps`. A run of m steps lowers the index by at most 2m.
`LPrel_safe` as today. `LPrel_acc`. At an index ≥ 1, Q-Admin is a least
fixpoint over the admin τ of the process, so the process is accessible for
admin steps. Combining the three gives `live_adequacy`. The corollary on runs
inducts on the accessibility of position i and classifies each τ.

## 9  Fairness and lock freedom

### Definitions

Threads get identities. A configuration is (C, M) with M a finite map from
thread identifiers to terms, and every step names the threads that take part
(one, or two for a synchronization). A thread is enabled at a state when some
step names it. A maximal run is weakly fair when no thread is enabled at every
position from some point on without taking part in a step from that point on.
A thread is pending at a position when its redex is a session primitive on c.
The run is lock free when every pending thread later takes part in a step.
`lock_free p` holds when every weakly fair maximal run from p is lock free.

A blocked thread stays enabled exactly as long as its partner offers the dual
action, and an offer persists until it fires, so weak fairness per thread is
enough. Strong fairness is not needed.

### The rank claim is not sufficient

Claim to check. Lock freedom needs every point to have finitely many points
below it, a rank into ℕ, because ω+1 starves. The ω+1 witness is right. Thread
A loops on a while holding b, its partner B serves a, and C waits on b. The
gate of A at its k-th action on a is ι+k ≺ b̄. With all ι+k below b̄ the
configuration is in the live relation, takes a channel step in every round,
and C starves under every fair scheduler.

A rank fixed per world does not repair it. A loops on fresh channels instead.

```
A = rec f. let (x, y) = new in spawn (λ_. recvclose y);
           sendclose x; f ()          holding b throughout
C = recv b̄ …
```

Each new places its fresh point (aᵢ, 0) below b̄. `wext_fresh` allows facts
between the new name and old ones. Every world of the run has finitely many
points below b̄, and a rank fixed at creation gives every (aᵢ, 0) rank 0. A
performs a channel step per round, never offers b, and C starves. A rank bounds
the length of descending chains below b̄, not the number of distinct points
below it.

### What suffices, on paper

Three conditions together give lock freedom under weak fairness.

1. No τ-divergence. Proved here.
2. A rank. Worlds carry rk into ℕ with x ≺ y ⇒ rk x < rk y, fixed for old names
   by every extension. It bounds the depth of a chain of waits. Without it a
   chain of threads, each blocking on a fresh point below its predecessor's
   after one channel step with an unrelated chatterbox, grows forever, and
   the first waiter starves.
3. Obligation fuel. Every entry of Θ and Σ carries d ∈ ℕ. A channel step of
   its holder on another entry decrements d, a delegation passes the remaining
   d, and at d = 0 the holder's next offered head is that entry. This is
   Padovani's tickets, which bound how often a channel travels, and the fuel
   of Trillium's Fuel(M), which bounds how long a thread postpones a role.

Proof sketch, by induction on rk of the waiting point x of a pending thread C.
The partner end x̄ is held by A. By condition 1 and weak fairness A leaves
every τ sequence. When A blocks at u, its gate gives u ≺ x and rk u < rk x, so
by induction A's offer fires. A therefore keeps taking channel steps until its
fuel for x̄ runs out, and then offers x̄. Both offers persist, C is enabled from
then on, and weak fairness fires the synchronization.

Padovani's lock freedom (padovani2014deadlock, p7) likewise requires a
well-founded order on priorities, natural numbers, and an upper bound on
delegations, tickets. The rank is condition 2, and the tickets are a special
case of condition 3 for a channel that travels without being used.

Kobayashi's server violates condition 2. Its constraint ι[0]ⁿ⁺¹ ≺ ι[0]ⁿ is an
infinite descending chain.

Conditions 2 and 3 are not mechanized on this branch. Fuel interacts with
recursion, because a session that recurs needs its fuel reset at each action,
a bound per action in the session type, and with existential payloads. That is
a separate design.

## 10  State of the mechanization

Closed, in `theories/liveness/`.

- `LiveRelation.v`. The definitions of §2 and §3, custom induction principles
  over the τ layer (`Eind_ind'`, `Pind_ind'`), monotonicity in the world,
  independence of the fuel of V, the relation reads only the levels below.
- `LiveUnfold.v`. Characteristic equations `LVrel_*_iff`, `LErel_S_iff`,
  `LPrel_S_iff`, induction over τ steps `LErel_S_ind`, `LPrel_S_ind`, downward
  closure of V, E and P, monotonicity of V in the world, `LVrel_LErel`,
  `Vspawn_LVrel`.
- `LiveAdequacy.v`. `live_adequacy`, `live_runs`, `live_finite_runs`.
- `LiveRules.v`. `LErel_app_lam` (Tait), `LErel_force` (unrolling at the
  index), `LVrel_box_lob` (E-Exp-Live), `LErel_spawn`.

Not ported. The bind lemma, the constants (send, receive, close, select,
branch, link, new), the invariance lemmas (renaming of points and channels,
equivalence), the composition lemmas (Internalize, P-Connect, P-Term, P-Join),
the semantic judgment with later hypotheses, the static fundamental theorem
and the examples. Their feasibility rests on the case analyses of §2, §4 and
§6. None of them has met a counterexample.
