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
Internalize and of the composite in P-Connect, recorded above. Branch
liveness-comp ports the composition proofs with these statements (§11).

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
       ∃ x s s' W', new_place W1 (L ∪ roots(Θ, T, F)) x W' ∧ s ⊥ s' ∧
         Eind VT T W' (Θ, c : (s@x, s'@x̄)) F e')                  O-New
  ∧ (∀ w e', e --⇑w--> e' →
       ∃ Θ1 Θ2 ub lb, Θ = Θ1, Θ2 ∧ Vspawn_n W1 Θ1 ub lb w ∧
         Eind VT T W1 Θ2 F e')                                    O-Spawn
  ∧ (∀ σ e', e --σ--> e' → Eobl_σ (levels < n) W1 Θ T F σ e')     O-σ
```

`Vspawn_n` is `Vfunˡ_n` at ∗ ⊸ ∗ with `E_n` read as `Eind (λ _ Θ v, Θ = ∅ ∧
v = ∗) ∗`. `Eobl_σ` is today's obligation of the six session labels with every
successor at n − 1 and the payload of O-Send at n − 1.

`new_place W N x W'` is the condition of branch no-eq (no-equality.md §7.2):
x is a constant a ∉ N and W' a fresh extension of W placing a, or x is a
point W knows and W' = W (new@x). O-New and Q-Admin quantify cofinitely over
the fresh names. For every finite
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
enough. Strong fairness is not needed. Padovani and Zavattaro assume full
fairness instead, a run is fair when it passes through finitely many weakly
terminating states (padovani2025fair, p7), and they prove fair termination, a
stronger property than lock freedom. Their weak termination proof uses a
lexicographic measure because the premises of their call and cut rules need
not have a smaller measure (p21), the same reason this relation pairs the
index with an inductive layer.

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
- `LiveKob.v`. `kob_tau_diverges`: Kobayashi's server has a reachable state
  from which new, spawn and β continue forever. `live_fundamental_false`:
  some statically typed closed program is not in the live relation. The live
  fundamental theorem therefore needs a restriction of the static E-Exp rule
  (a guarded self, §6). That is a change of the type system and waits for the
  author.
- `Guard.v`, `GuardEx.v`. The guarded fragment (sharp edges 160) and the
  examples against it.
- `LiveBind.v`. `LErel_bind`, the bind lemma, with the statement of
  `Erel_bind`.
- `LiveConv.v`. `LVrel_tconv`, `LErel_tconv`, `LPrel_tconv`, `LVrel_payload`:
  conversion along T ≈_W T'. Inside one level V and E convert together by
  induction on `tsize`. The alias handling is confined to the lemmas reused
  from PointConversion.v (`teqW_mono`, `lb_below_conv`, `ub_below_conv`,
  `bcs_hold_conv`, `pteqW_eq`, the teqW algebra). With equality for ≡_W they
  become rewriting, and the live proofs keep their shape.
- `LiveConsts.v`. `LErel_app_noforce` and one lemma per constant (new, spawn,
  receive, send, close, select, branch, link). Each proof first moves to a
  later world (`lmove`, `LErel_intro`, `LEnow`) and then reads the step there.
  The payload of a send is read one level down (`LVrel_down`).
- The comm and link τ of a process now place fresh names cofinitely as well
  (`LPtau_case`), so conversion and composition need no renaming of points.
- Branch no-eq. Since 2026-11-06 liveness sits on no-eq (rebased onto b4fcf35).
  ≡_W is equality, and O-New places the channel by `new_place`: a fresh
  constant outside L ∪ roots, or a point the world knows (new@x, world
  unchanged). `LErel_app_new` covers KTNewAt. The PN and MP2 guard checks of
  GuardEx.v are commented out (NO-EQ: translation pending). Trivial alias
  steps in LiveBind and LiveConsts are gone. The PointConversion lemmas in
  LiveConv stay.
- `LiveTermRules.v`. The live semantic judgment `lsem_typed` with
  `lgrounding`, and E-Unit, E-Const, E-Var, E-Ch, E-Abs, E-App (all function
  values, force included, `LErel_app`), E-Let*, E-LetPair, E-Pair, E-Inj,
  E-Case, E-Weak, E-Conv (≈_W), E-Contract, E-Force, E-Pack, E-Open
  (`LErel_Vsub`), and `lsem_rules` (sem_rules without E-Exp) with
  `lsem_rules_fundamental`.
- `LiveBind.v`. `LErel_bind_R`: the continuation is needed at the current
  index only for returns that satisfy a condition R closed under the τ steps
  of the hole (`tadmin`).
- `LiveGuard.v`. `gd_noret`: a term with `gd` reaches no value by β, new and
  spawn (purely syntactic). `LErel_bind_guarded`: a guarded hole binds with a
  continuation below the index. The judgment with one later variable
  `lsem_later` (`lgroundingL`, `later_val`). `lsem_typed_box_live`: E-Exp
  from a later judgment of the body, by Löb up to the index
  (`LVrel_box_lob_le`); when the body is a λ, the later hypothesis also says
  that the self is a box around a λ. `lsem_later_letu_guard`: E-Guard-Let.
  `lsem_later_drop`: a term judged without the later variable.
  `lsem_later_now`: with no later variable the judgment is `lsem_typed`.
  `lgroundingL_split`, `lgroundingL_lower` (a later variable is now one level
  down), monotonicity and downward closure of `lgroundingL`.
- `GuardCex.v`, sharp edge 161. The guard of entry 160 admitted a typed
  program that τ-diverges: a box whose body is not a λ forced its own self
  through the special case of `ok` for (force x) e before any channel step
  (`cx_gptyped0`, `cx_tau_diverges`, `live_guarded_unrepaired_false`).
  Decided 2026-11-07: `guarded` (Guard.v) now allows the special case only
  under the λs of a box body (`ok f`, `okv f`). It rejects the witness
  (`cx_not_guarded`) and keeps the forwarder, the tail call, first-action and
  the rounds box (`guarded_examples`).

- `GuardMarks.v`, sharp edge 162. The guard with a mark per variable
  (`okM`, `okR`, `gallM`). `L y = Some f` marks y as later, and f permits
  force of y applied to a guarded argument. `ok` and `okv` are its one-mark
  instances (`ok_okM`, `okv_okR`), `gall` implies `gallM` (`gall_gallM`), and
  the marked guard is invariant under renaming (`okR_rename`, `gallM_rename`).
- `LiveGuard.v`. The later judgment `lsem_later W Θ Δ Lm F e T` now takes a
  mark per variable with its own λ flag. `lsem_later_box_live`: E-Exp-Live with
  later variables around the box, whose body sees the self as one more later
  variable.
- `LiveGuardRules.v`. One rule per clause of the repaired guard. Weakening,
  contraction (the marks follow the renaming), open, conversion, pack, the
  injections, and let, let-pair, case, pair and application, each with the
  marks on both parts or with a guarded first part and the rest judged without
  marks (`lsem_later_elim`, `lsem_later_elim_guarded`, `lcont_*`). E-Abs with
  marks (`lsem_later_lam`). The applied λ with a guarded argument
  (`lsem_later_app_lam`) reads its closure in V at level 0 (`lsem_v0`), which
  the rules of E-Abs give without the body. Force of the self applied to a
  guarded argument (`lsem_later_app_force`) is one β to the closure of the
  self and a guarded bind.
- `LiveGuardFund.v`. `typed_live`: a typed term with `gallM` is in the later
  judgment for every marking with `okR`, and a λ is in `lsem_v0`, by one
  induction on the typing derivation that follows `typed_sem_rules`.
  `live_fundamental_guarded`: `gtyped W ∅ [] Θ Δ (F, None) e T → strict W →
  lsem_typed W Θ Δ F e T`. `live_fundamental_guarded_closed`: a closed guarded
  typed term is in the live E relation at every index. `fw_live`, `tc_live`:
  the forwarder and the tail call as live terms.

Next, in order.

1. Done: the term-level guarded live fundamental theorem.
2. Done on branch liveness-comp (§11). Invariance, Internalize, P-Connect,
   P-Term and P-Join.
3. `gptyped W ∅ p T → ∀ n, LPrel n W ∅ T p`, and the
   examples of GuardEx.v as live theorems. P-Term, P-Connect and P-Join of
   §11 are the process cases, and step 1 gives the term judgment.

## 11  Composition (branch liveness-comp)

Closed under the global context, in `theories/liveness/`. Every statement
is the old one with LPrel, LErel and LVrel in place of Prel, Erel and
Vrel, and with `∀ n, LPrel n …` in place of `sem_ptyped`. No premise is
added. The P-Term premise reads the live term judgment `lsem_typed` in
place of `sem_typed`.

| File | Theorems | Old proof |
|---|---|---|
| `LiveRenaming.v` | `LVrel_swap`, `LErel_swap`, `LPrel_swap`, `LPrel_swap_restricted` | ChannelRenaming.v |
| `LiveJunk.v` | `LPrel_junk` | JunkRenaming.v, `Prel_junk` |
| `LiveFuse.v` | `LVrel_fuse`, `LErel_fuse`, `LErel_junk`, `LErel_rename` | JunkRenaming.v, `rel_fuse` |
| `LiveEconv.v` | `LVrel_econv`, `LErel_econv`, `LPrel_sconv` | PointConversion.v |
| `LiveInternalize.v` | `LPrel_internalize` | Internalize.v |
| `LiveConnect.v`, `LivePConnect.v` | `LPrel_connect`, `LPrel_join` | ConnectCut.v, ConnectSteps.v, PConnect.v |
| `LivePTerm.v` | `LPrel_term`, `LPrel_indep` | PTerm.v |

Of EquivInvariance.v only type conversion remains nontrivial without ≡,
and LiveConv.v has it (`LVrel_teq`, `LErel_tconv`). Environment conversion
up to session equivalence is in `LiveEconv.v`, because the link cases of
Internalize and P-Connect read it.

How the proofs differ from the old ones.

- Inside one level V and E move together by induction on `tsize`, as in
  LiveConv.v. The arrow at j = n needs E at the result type, and E needs V
  at its own type for E-Stop. The spawned closure is read through the τ
  induction of E, so it needs no V at ∗ ⊸ ∗.
- Junk renaming, the move lemma, conversion and Internalize induct on the
  τ layer of the derivation (`LErel_S_ind`, `LPrel_S_ind`). β, new and
  spawn use the induction hypothesis at the same index. Every channel step
  goes one or two levels down, where the outer induction on n applies.
  The old proofs used the size of the soup for sends, closes and links.
  These now cost one and go down a level.
- Fresh names are cofinite, so no lemma renames points. Conversion of the
  interface passes the roots of the converted interface into the set L to
  avoid. P-Connect passes the roots of the other component.
- The move lemma (`LErel_fuse`) meets a new at the same index. The old
  proof moved the fresh name of the original to the image's name by a
  second move one level down. Here the original creates the image's name
  itself whenever that name is not c. When the image creates c, which
  the moved term no longer mentions, the original creates a fresh c0 and
  a swap of c0 and c finishes (sharp edge 170).
- Internalize. A synchronization of the fused process on d is a send of
  p at cost one and a receive at cost one, so the fused successor is read
  at n − 2, which is the cost of the synchronization. At n − 2 = 0 the
  obligation is trivial. Otherwise the second step is read from the first
  successor at n − 1 (`li_sync_case`, `li_choice_case`, `li_close_case`).
- P-Connect inducts on the τ layer of the first component and inside on
  that of the second (`lconn_level`). The goal is stated for the two base
  worlds and every composite world above both (`lconn_goal`). A component
  that creates a channel at a fresh extension is read there, and the other
  keeps its derivation at its base world. P-Join is `LPrel_connect` at two
  worlds, so the composite world is the join and no move by monotonicity
  is needed. A synchronization across the cut costs one in each component
  and two in the composite.
- P-Term inducts on the τ layer of the thread. A spawn composes the
  continuation and the spawned thread by P-Connect at the same index. The
  spawned closure is applied to ∗ and steps by β to its body, which the
  thread's derivation reads at the current index (`LPrel_spawned`).

All twelve theorems are in CheckAll.v.
