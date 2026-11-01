# Sharp edges

Every place where the order-based design turned out subtler than it looked,
in the order we hit them. Each entry gives the problem, a minimal witness, the
decision, and where it lives in ORDERS-SPEC.md. Entries 1 to 12 came up while
designing, entries 13 onward while mechanizing. Entries 18 to 36, except 26,
sit in the appendix at the end.

## Design

**1. Minimality is not enough.**
A thread may not block on an instant that is merely minimal among what it holds.
Witness: t₁ blocks on x and holds y, t₂ blocks on y and holds x, with x and y
unrelated. Both are minimal, and the two threads deadlock.
Decision: every held entry must lie strictly above some offered entry (§6).
The earlier mechanization hit the same wall.

**2. Readiness counts ends, not names or instants.**
Both ends of a channel share their instants. Counting names lets a thread that
holds both ends of c and blocks on one of them pass.
Decision: ready ranges over entries, one per end, so the thread needs
head(c) ≺ head(c) and fails (§6).

**3. Readiness needs a clause for "nothing offered".**
Without it a closed configuration has no external head and readiness is
vacuous.
Decision: a stable state that offers nothing must have terminated (§6).

**4. One world per component (deferred).**
A component that acts on two external channels in an order chosen at run time
needs both orders. Its composition with a matching partner is deadlock free but
not derivable.
Decision: deferred by the author (§14).

**5. A receiver must plan before the channel has a name.**
After receiving d, ready needs facts about d, but the receiver's world is fixed
before d exists.
Decision: slots c[k][i] name "what c carries at its k-th action". The sender
aliases the payload to the slot, the receiver states facts about the slot, and
P-Connect checks that they agree (§4, §7). An earlier version used swap
invariance instead of aliases and was unreadable.

**6. Closures hide the channels they capture.**
A sent closure shows no channels in its type, so they get no slot.
Decision: arrow types carry an upper and a lower point. A placeholder in a
payload names a point, not a channel (§4).

**7. The sequencing lemmas need an upper bound.**
In let () = t₁ in t₂, ready for the whole thread needs t₁ to block below the
channels t₂ holds, and E⟦t₁⟧ alone does not say where t₁ blocks.
Decision: E carries a frame F, an input, and F = ∅ is the paper's E. It is a
parameter of E, not a separate relation, so that E and the frame condition pick
the same world extension at new. Arrows keep two points (§6, §7, §9).

**8. fork imposed a tree.**
Decision: new and spawn instead of fork. new returns both ends under one name
(§1, §2).

**9. Channels can return to the holder of their other end.**
With multi-channel P-Connect (cycles) K₁ can send e to K₂ while K₂ holds the
other end of e. The paper never meets this, because its single-channel
P-Connect and its extrusion split rule it out.
Decision: the LTS stays the paper's. Q-Recv states its continuation for the
successor with the returning channels B restricted (§3, §7). An LTS rule
("back") was tried first and dropped.

**10. A carrier can be sent over itself.**
Decision: if c itself lands in B, its continuation entry leaves Σ too (§7).

**11. link (new ∗) is typable.**
new gives both ends at dual types, so a self-link type-checks.
Decision: O-Link allows c = d at term level, and both entries leave. At process
level it cannot reach the interface (§7).

**12. The static system needs a bound, but not where it first sat.**
The bound on terms became a frame passed down the derivation. Arrows keep their
two points (§9).

## Mechanization

**13. Amalgamation and fresh extension need more premises.**
Amalgamation needs both worlds strict, because a cycle among names only W₁
knows hides in the restriction. Fresh extension needs the placed names unknown
to the other world (§10).

**14. O-New needs the name unknown to the world.**
Otherwise no conservative extension placing it exists (§7).

**15. A message may carry both ends of one channel.**
Decision: Q-Send lets both ends leave, and a channel whose two ends both arrive
joins B (§7).

**16. An environment that cannot be formed fails the obligation.**
For example, Θ already holds both ends of c. Such a thread is never ready, so
nothing is lost (§7).

**17. prim □T keeps the premise prim T.** This is the paper's rule (§4).

**26. Deciding strictness of W_G.**
Uniform schemas fall under Kosaraju and Sullivan's zero-cycle algorithm. Facts
with a counter on one side only need a free-coordinate extension, which we
believe decidable but have to prove. Uniformity is not a restriction, because
the static system produces only equal or independent counters (§12).

**37. (N) Facts on channel names were the cause.**
With M1 the forwarder failed readiness: it reads before it writes, so it offers
one of its two entries while the other sits at the same instant. The relation
was right. link ⟨a, b⟩ ∥ link ⟨b, a⟩ over a P-Connect cut {a, b} deadlocks
under forwarders and terminates under substitution. A separate analysis traced
entries 18 to 36 (appendix) to one cause: worlds attached facts to channel names, and every
step that renames a channel had to move those facts.
Decision (author, 2026-10-29): worlds speak about points only. Each entry
carries its current point, c : S@x, new picks a fresh point, and V-Chan compares
points up to ≡. link substitutes as in the paper, Q-Tau is the paper's clause
plus a conservative extension, Q-Recv states the exact successor, and the
paper's renaming and junk lemmas hold with the world fixed. Gone: the forwarder,
link_S, invisible extension, the α-variant (E), received-name freshness, the
guard at new, P-monotonicity restrictions, the two sorts of F2. New: Renaming
points and Entry conversion (§10).

**38. Consequences of points-only worlds (Claude, delegated).**
Payloads become a plain substitution P[x] = T[x[1..m]/ιs]. The ∃xs at the sender
and ∀xs at the receiver existed only because slots of channel instants could not
occur in types. Successor congruence x ≡ y ⇒ x+1 ≡ y+1 becomes a world law,
because entries now move along their points and Entry conversion must survive an
action. It replaces the separate alias notation. Arrows are written T ⊸^u_ℓ U
again, because β and λ also name a label and abstraction. Found while updating
gvsharp-orders.lagda (§4, §5, §7, §9, §10).

**39. (O) A fresh point must also avoid the environment's points.**
O-New only asked a ∉ names(W). An environment may mention points outside W's
support, so in monotonicity (W ⊑ W′) the chosen a can be known to W′, and
renaming it away also renames its occurrences in Θ, T, F.
Decision (O1, Claude, delegated): the new point is fresh for W and for the
points of Θ, T, F (Q-Tau: of Σ, T). A prover can always pick a globally fresh
constant. Rejected: a scoping invariant roots(Θ, T, F) ⊆ names(W) (O2), which
threads through every statement. Also from this round: V-Const reads the
signature up to ≡_W, because payloads by substitution fix recv's payload at the
slots of the session point and Type point conversion must move them (§7).

**40. Overlaps of environments at aliased points, not equal ones.**
Θ₁, Σ₂ (and Θ = Θ₁, Θ₂, the both-ends condition of Θ, recv_ok and the
split of Q-Send) asked dual ends at equal points, with Entry conversion to
move between aliased ones. Entry conversion is not stable that way: a
conversion must keep every equality between the two ends of a channel, also
after later actions (x+1 against the other end's point), so it would need a
bijection of points that commutes with successors, which an alias between two
names does not give. Decision (Claude, delegated, overnight rules): every
overlap condition reads the world's ≡ instead of equality. Composition is then
closed under aliases by definition, and a link's survivor (ends at x and y with
x ≡ y) is a valid environment without any conversion. Type point conversion
stays, because P-Connect meets a payload typed at P[x] by the sender and at
P[y] by the receiver (§7, §10).

**41. Name hygiene of process steps: restricted names stay off the interface.**
Q-Tau had no guard, and Q-Recv no freshness of received channels against the
restricted set. A new step may then pick a name that the interface Σ holds
without any thread mentioning it, and a receive may deliver a channel whose
name is restricted inside the process. In P-Connect the composite's successor is
then a component whose restricted name is the other component's interface name,
and no renaming repairs it: renaming at the composite level also renames the
interface. Decision (Claude, delegated, overnight rules): Q-Tau constrains only
successors with p′.1 # dom Σ, and Q-Recv only received environments with
dom Θ₂ # p.1. These are the paper's implicit "Σ and C do not share channels",
not world conditions; adequacy (Σ = ∅) is unaffected (§7).

**42. (P) P-Connect over related components loses step indices at a linked cut pair.**
With a multi-channel cut, component 1 may link two cut channels c and d. Component 2
then holds both ends of d and must be related with d restricted. A synchronization on
d inside component 2 is one τ step of the composite but two steps (c̄!v, then d̄?v) of
component 2, so the index halves and the induction on n breaks. Q-Tau picks its world
per index, so stating the lemma for all indices does not help.
Decision (P1, Claude, delegated, overnight rules): the process relation is proved for
thread decompositions. A configuration (C, E) is decomposed when every thread is
E-related in one world W, the threads' environments compose (overlaps at ≡_W points)
to an environment that agrees with Σ on dom Σ and holds both ends of every channel of
C, dual and aliased. P-Term and P-Connect become lemmas that build decompositions, and
the fundamental theorem for processes goes through the decomposition. A link renames
or fuses keys inside single threads, one step each (an E-level substitution lemma that
generalizes the paper's junk collapse). V, E and P are unchanged (§11).
Rejected by the author: P-Connect stays a composition of two components, each in P
with its own world. No decomposition code was committed.
Adopted (plan A, author): an index budget. P-Connect is stated at ⊨ level; inside, the
components at index 4^n give the composite at n. A composite step costs each component
at most one step plus at most one halving, because a link fuses one pair. A budget that
grows with the cut size k fails, since delegating a restricted channel over the cut
enlarges k. It rests on Internalizing a link at component level: for prim T,
p ∈ P^W_{2n}⟦Σ, c : S̄@x, d : S@y⟧ with x ≡ y gives (C ∪ {d}, E[d/c]) ∈ P^W_n⟦Σ ⊢ T⟧.
prim T is needed: a terminated p returning ⟨c, d⟩ fuses into a stuck (C ∪ {d}, ⟨d, d⟩).

**43. O-Recv composes the payload with the carrier's continuation.**
O-Recv composed the received environment Θ₂ with Θ₁ (the environment without the
carrier's end) and only then added the carrier's continuation c : S@(x+1), with no
check between the two. A payload that carries an end of the carrier itself was
therefore merged with the continuation even when the two are not dual or aliased.
This breaks the fusion of two ends at a link (a value holding both ends of the fused
channel, where a closure later receives on one of them a payload naming that channel,
is in V before fusion and out of V after). Q-Recv already checks this overlap
(recv_ok reads the continuation's entry). Decision (Claude, delegated, overnight
rules): O-Recv quantifies over Θ₂ and over the composition Θ′ = (Θ₁, c : S@(x+1)), Θ₂,
so a returning end of the carrier must be dual to the continuation at an aliased point.
E becomes weaker (fewer payloads), the fundamental theorem only easier (§7).

**44. The halving budget breaks at an external receive.**
Internalizing a link is stated as P_{2n} ⇒ P_n, and P-Connect as components at 4^n
giving the composite at n. Both proofs go by induction on n. At an external receive of
the fused process q the obligation is, for every j ≤ n − 1 and every payload in V_j,
that the successor q′ is in P_j. The receive of p offers only the same thing, a
successor p′ in P_j for a payload in V_j, because the payload is given at j and V is
not upward closed. The induction hypothesis turns p′ ∈ P_{2j} into q′ ∈ P_j, so it
needs p′ ∈ P_{2j}, which the payload at j does not give. The same gap appears in
P-Connect, where the composite receives on a channel of one component and the
induction hypothesis asks for that component at 4^j. The statement itself is not
refuted. A fused process takes fewer steps than p, and the payload runs the same number
of steps in both, so q′ needs at most 2j steps of the part of p′ that is not the
payload. The budget P_{2n} ⇒ P_n cannot express this split between the two parts.
Open, for the author. Possible ways out are a relation in which session steps keep the
index (only β, new and spawn lower it, with a coinductive clause for session steps at
a fixed index), a budget that indexes the payload and the rest separately, or a
treatment of links in the cut that does not fuse.

**45. Giving steps keep the index (decided 2026-10-30, 01:50, replaces the budget of 42). Confirmed by the author 2026-10-30.**
Send, close and link keep the index in E and in P. β, new, spawn, receive and a
synchronization cost one. The budget of 44 came from Internalizing a link, where one
synchronization of the fused process is two external steps of p (c!v, then d?v). With a
free send this pair costs one step, as the synchronization does, so Internalizing a link
becomes P_n ⇒ P_n and P-Connect takes components at n to the composite at n. The receive
gap of 44 disappears with the budget, because the receive of p already gives p′ at the
index the fused process needs. E_{n+1} and P_{n+1} are least fixpoints over giving steps
at fixed n+1. Giving steps are well founded, because each removes a send, close or link
redex outside every λ or a channel from C ∪ dom Σ, so the fixpoint excludes no process.
Adequacy keeps its proof. A run of k steps contains at most k costly steps, and the free
steps between two costly ones are finitely many. The composition lemmas keep their
statements. Rejected are a two-index budget (more bookkeeping, same effect) and links that
do not fuse (forwarders deadlock in a cycle, decision N).
Encoding (Claude, routine). E_{n+1} and P_{n+1} are inductive predicates over the giving
steps, parameterised by the level-n relations. The giving clause for the τ of P-Act-Link
states the successor in the same world, because a link creates no points. With a world
extension there, monotonicity in the world would need a renaming of points at the same
index, which the induction over giving steps does not provide.

**46. P-Connect inducts on the soup size inside a level (Claude, routine, 2026-10-30).**
Nested induction on the two components' giving-step fixpoints does not close. A link of
two cut channels in component 1 fuses component 2, and a link of a cut channel with an
interface channel renames component 2. Neither result is a giving successor of
component 2, so the inner hypothesis does not reach it, whichever component is the
outer one. Inside the level S n the proof therefore inducts on the syntactic size of the
composite's soup. Every giving step removes a send, close or link redex together with
any payload, so the soup shrinks. Junk substitution, renaming and fusion of the other
component replace channel names only and keep the size. The relation and the statement
stay as they are. Inside, P-Connect is proved for components in one world W, with one
component at T and the other at ∗ in either order, so that each step case is proved once.
The spec's W₁ ⊔ W₂ enters through monotonicity.

**47. P-Term inducts on the thread size inside a level (Claude, routine, 2026-10-30).**
The plan was an inner induction on the giving fixpoint of E (Erel_S_ind). It does not
reach a link of a restricted channel c. The process step substitutes d for c in the
thread, and chsubst c d t′ is not a giving successor of t. As in entry 46 the proof
inducts on esize t inside the level S n′. Every giving step shrinks the thread, and the
substitution keeps its size. The substituted thread is related by rel_fuse (d restricted)
or by rel_fuse and Entry conversion (d in the interface). The spawn case composes the two
threads with conn_all at n′, one at T and the spawned one at ∗. Proved as Prel_term
(PTerm.v). Statement as in §11. Implicit side conditions made explicit there are W strict,
dom Θ_B = C₀, Θ_B holds only both-ends entries, dual at ≡_W points, and dom Σ # C₀.

**48. The bind lemma takes the context's heads as part of the hole's frame (Claude, routine, 2026-10-30).**
Erel_bind (Bind.v) runs K[e] with e ∈ E^W_n⟦Θ1 ⊢ U ≺ F ∪ H⟧, the composite at Θ = Θ1, Θ2 and
frame F, where every entry of Θ2 lies at or above some point of H. E-App and E-Pair instantiate
H with heads(Θ2, Δ2) for the left subterm and with {ℓ} or heads(T) for the right one. The frame
then forbids the redex of e to act on a channel that Θ2 also holds, because the two ends sit at
aliased points and the frame would put one strictly below the other (subjs_free). Every step of e
is therefore a step on Θ1 alone, and the composite's offers are e's offers. At new, the point e
picks is renamed by Erel_new_rename to one that is also fresh for Θ2, T and F.

**49. The point of new must be known to the world (Claude, delegated, 2026-10-30).**
V-Const put new in V at ∗ ⊸ S@ι ⊗ S′@ι for every ι. When the world does not know the root of
ι (a point variable, or a constant outside the support), new ∗ fails E at index 2. O-New
places only the fresh a, so no extension can alias (a, 0) to ι, and ⟨c, c⟩ is then not in V
at S@ι ⊗ S′@ι. E-App fails on new ∗ for that reason. Decision: konst_ty takes the points
the order knows as a third parameter. In V it is pt_known W (the root is in the support),
monotone in W. KTNew asks it of ι. Then the fresh extension aliasing (a, 0) to ι exists
(wext_fresh_alias, TermRules.v). The static system reads every point of G as known.
Rejected: letting O-New also place the root of ι, which changes the clause and its
renaming lemma (§7).

**50. The semantic judgment composes the grounding's environment with Θ (Claude, delegated, 2026-10-30).**
sem_typed asked Θ′ ##ₘ Θ and used Θ ∪ Θ′. A value bound by let (x, y) = t₁ in t₂, by case
or by a λ may hold the other end of a channel of Θ, because the static Θ₁, Θ₂ composes
dual ends. The disjoint version cannot prove E-LetPair, E-Case or E-Abs then. Decision:
sem_typed quantifies over Θ″ with tenv_comp (≡ of the future world) Θ″ Θ Θ′, as V-Abs
already does for its argument. P-Term instantiates Θ′ = ∅ (§8).

**51. (Q) E-App fails when the function is force.** *(decided as 52)*
V-Box asks the body in E at frame ∅, and force has upper point ⊥, so E-App applies it under
every frame F. Counterexample: the box body creates a channel at a fresh a, receives on it
(a spawned thread sends) and returns it at type Close@(x+1). Every proof of E for the body
must alias (a, 0) ≡ x at new, because the world grows only at new and the final value
needs (a, 1) ≡ x+1. The body is in E at frame ∅. Applied by force under F = {x}, the
stable state that waits on (a, 0) needs (a, 0) ≺ x, which fails. So force ∈ V and the
box ∈ V, but force b ∉ E⟦· ⊢ Close@(x+1) ≺ {x}⟧. Options: (B, recommended) □ carries an
upper point, □^u(∀ιs. T). V-Box asks E at every F with {u} ≺ F, force has type
□^u(∀ιs. T) ⊸^u_⊤ T[ιs′/ιs], and E-Exp types the body under {μ} with only u ≺ μ, as E-Abs
does. (A) V-Box asks E at every frame, which a typed body need not satisfy. (C) force only
at frame ∅. E-App and E-Force wait for this decision. The other rules do not use V-Box.

**52. □ carries an upper point under its binder (decided 2026-10-30, 06:40, resolves 51). Confirmed by the author 2026-10-30.**
Option B of 51, with u scoped under the ∀: □(∀ιs.^u T), u ::= ι | ⊥, and u may mention ιs.
force : □(∀ιs.^u T) ⊸^{u[ιs′/ιs]}_⊤ T[ιs′/ιs]. V-Box asks, for every W′ ⊒ W, every xs and
every F with {u[xs/ιs]} ≺_{W′} F, that fix x.t ∈ E^{W′}_n⟦· ⊢ T[xs/ιs] ≺ F⟧. E-Exp types the
body under {μ} with only u ≺ μ, as E-Abs does. The upper point of a box is the upper point
of the function force makes of it, so □^u σ behaves as a replicable ∗ ⊸^u σ. u sits under
the binder because the request/reply example under □∀κ acts at (a, κ), which no point fixed
outside the ∀ bounds. ⊥ keeps the old behaviour for bodies that act on no outer point.
This is a type annotation. It adds no premise. Rejected: (A) E at every frame, which a typed
body that acts on an outer point cannot meet, and (C) force only at frame ∅, which forbids
forcing a box inside any context with pending channels.

**53. The static system reads fresh point variables as "every" (Claude, delegated, 2026-10-30).**
Static.v indexes Θ; Δ ⊢^F_G t : T by the world W = W_G and reads every side condition on
points in W. E-Abs types the body under {μ} with μ fresh and only u ≺ μ. E-Exp does the same
and leaves the box's ιs free in the body. Static.v states both premises for every later world
W₁ ⊒ W and every frame F′ with {u} ≺_{W₁} F′, and E-Exp also for every instance xs of ιs,
which is the shape of V-Abs, V-Box, sem_typed_lam and sem_typed_box. A μ about which only
u ≺ μ is known can stand for any such frame, so the rule adds no restriction. With these
premises the fundamental theorem is an induction that applies one lemma per rule. The
syntactic presentation with fact schemas and a fresh constant μ would need two more lemmas:
a typing derivation survives a substitution of point variables (G closed under it), and E
is invariant when a conservative fresh extension of the world is dropped (the reverse of
monotonicity, for names nothing mentions). Neither is mechanized. The other rules are §9 as
written, and E-Force is derived from E-App at the constant force (typed_force). Static
P-Connect is binary with one world W, and Prel_connect at W₁ = W₂ = W gives it, because
W ⊔ W ⊑ W (wext_join_self). P-Connectⁿ is therefore not needed for the fundamental
theorem. P-Term and P-Connect carry the implicit well-formedness of Prel_term and
Prel_connect as premises: Θ_B dual at aliased points over exactly C₀, the disjoint unions,
and dual cut ends.

**54. Dropping a fresh conservative extension fails at V-Const (Claude, 2026-10-30). Resolved by option (D), see 56.**
Undoing the infinitary part of 53 needs this lemma. If W′ places a fresh constant μ over W
and adds nothing between old points, then V and E at W′ give V and E at W for Θ, T and F
without μ. The lemma is false. The witness T₀ of V-Const is existential, and force's
instance xs may use μ. Counterexample (DropCounter.v, closed under the global context):
W knows b and has only program order. W′ adds (μ,1) ≡ (b,0), a fresh conservative
extension (Wm_fresh). force is in V^{W′} at □(∀ι. Close@(ι+1)) ⊸ Close@(b,0) with
xs = [(μ,0)]. It is in no V^W at that type, because no point x of W has x+1 ≡_W (b,0)
(force_notin_Wb, and force_notin_Erel_Wb for E). The E-Abs instance
W + {u ≺ μ, μ ≺ F′} has no alias on μ, but the restricted lemma has no proof in the style
of monotonicity either. At O-New the world can alias the new point to μ, so the restriction
of that world to the old names and a leaves the no-alias class, and V-Const then needs a
new witness for xs. Options: (A) keep the "every" premises of 53 (status quo, sound,
closed). (B) prove the no-alias lemma by rebuilding witnesses, mapping μ into unused
slots of the point new creates. This is a different proof, and its truth is open. (C) change
V-Const, for instance by asking pt_known W of force's xs as 49 does for new. This changes
the relation and needs the author. Static.v is unchanged.

**55. P-Connectⁿ lifts every component to the full amalgam, then folds P-Connect (Claude, routine, 2026-10-30).**
Prel_connect_n (ConnectN.v) is the corollary of §11. The components first move to
W₁ ⊔ … ⊔ Wₙ by monotonicity, so every step connects at one world, and P-Connect at W ⊔ W
lands in W (wext_join_self'). Duality of the cut ends then needs ≡ of the full amalgam
only, as the spec states it. Partial amalgams never appear. Prel_connect_list folds the
list from the left. Each step merges the composite with the next component over the
channels both hold, and the cut channels with an end further down stay in the interface.
The cut is read off the list of entries the components hold for a channel: two dual
entries on C₀, at most one elsewhere. The side conditions are the implicit well-formedness
of Prel_connect, stated per list: interfaces apart, restricted channels apart from each
other, from C₀ and from every interface, dom Σ_Cᵢ ⊆ C₀ and dom Σᵢ ## C₀. W₁ ⊔ … ⊔ Wₙ is
wjoins, the world generated by all facts. The T-component comes first. The static system
has no n-ary rule: binary P-Connect already gives the fundamental theorem (53).

**56. The fresh μ of E-Abs and E-Exp is a frame variable (option D of 54, Claude, 2026-10-30). The E-Exp part is resolved by 57.**
A static frame is a set of points plus at most one frame variable φ, and the judgment
typed W Φ Θ Δ F e T carries hypotheses Φ of the form u ≺ φ (u ::= ι | ⊥). E-Abs types the
body under (∅, φ) with Φ, u ≺ φ for a fresh φ, at the same world W. E-Exp does the same with
u[xs/ιs] ≺ φ. One frame variable per frame is enough, because the body of λ or box starts at
{φ} and the other rules only add points. φ never enters a type, an environment or the world,
so neither new nor force can alias it, and the counterexample of 54 does not apply. E-App
checks x ≺ φ as x ≼_W u for the hypothesis u ≺ φ, and x ≺ f for points f in W as before.
typed_ityped instantiates φ by any concrete frame F′ with {u} ≺_{W₁} F′ at any W₁ ⊒ W and
yields the infinitary judgment of 53 (ityped). Monotonicity in W is folded into that one
induction, because typing reads W only through ≡, ≺ and pt_known, and these grow along ⊑.
fundamental, fundamental_proc and soundness are re-proved through ifundamental and are
closed under the global context. E-Abs now has finitely many premises. E-Exp keeps the
quantifier over the instance xs of the box's ιs, though no longer over worlds and frames.
Typing the body with ιs as point variables needs a substitution lemma for derivations, and
that lemma fails without a scoping invariant the static system lacks. KTSend and KTRecv
type send and recv at payload_at m T x = T[x[i]/ιᵢ], and T[σ][slots (σ x) m] = T[slots x m][σ]
holds only when the payload T has no free point variable beyond its m binders. Nothing in
Types.v or Static.v enforces that (sclosed_ty covers session variables only). The body's Δ
and the recursive □ would also need shifting past the m new variables, which Static.v never
does now. The fix is a point-scoping predicate on types, a premise of E-Const for send and
recv, and composition lemmas for pinst_ty with plist and pup. It changes no semantic
statement. The world itself causes no trouble, because a strict W relates point variables
by program order only and the substitution preserves program order.

**57. E-Exp types the box body once, with ιs as point variables (resolves 56, Claude, 2026-10-30).**
E-Exp has one premise. The body is typed with the box's ιs as the point variables 0, …, m−1.
The hypotheses Φ, the environment □Δ and the recursive binding □(∀ιs.^u T) are shifted past
them by pshift m. The fresh φ gets the hypothesis u itself, which may mention ιs. E-Const asks
of send and recv that the payload ∃ιs.T be scoped by its m binders (kscoped, pscoped m T).
§4 already says "all points of T bound", and pscoped also admits constants, so it rejects no
payload the spec types. pscoped looks at the payload's top level only. A payload nested in
the continuation is checked when its own send or recv is typed. typed_pinst substitutes
points for point variables in a derivation at the same strict W. typed_ityped does that and
frame instantiation in one induction. At a box it substitutes plist xs after pup m σ, which
undoes the shift (plist_pup_shift). force needs no scoping, because pup lifts σ under the ∀ of
□ and plist (σ xs) ∘ pup n σ = σ ∘ plist xs (plist_pup_comm). The world needs no closure
condition. A well-formed world knows constants only (wf_names_const), so a fact about a point
with a variable root is reflexivity or program order, and every instance keeps both
(pinst_eq, pinst_lt, pinst_known). typed_ityped_closed uses the identity pvar. fundamental,
fundamental_proc and soundness are closed under the global context. No semantic statement
changed, and no file outside Static.v.

**58. Constrained quantification □(∀ιs. C.^u T) (approved by the author 2026-10-30, Rocq 8f6aec6, ef86970).**
A box body knows nothing about two of its point variables except program order. A box whose
arguments must be used in a fixed order therefore did not type. The box now carries a finite
set C of facts x ≺ y over its ιs and outer points, under the binder like u (TBox n C ub T).
C = ∅ is the box of 52. V-Box quantifies over the instances xs with C[xs/ιs] in W′. KTForce
asks C[xs/ιs] in the order that konst_ty is given, which is ≺_W in V-Const and a premise on
the world, as pt_known is for new (49). ≈_W compares two constraints fact by fact, points up
to ≡_W (pcs_rel). The relation changed nowhere else. Monotonicity, conversion (pcs_hold_conv),
point renaming (pcs_hold_sw), channel renaming, junk, Connect, PTerm and ConnectN went through
with the extra hypothesis passed along. sem_typed_force and sem_typed_box gained the
constraint as a premise, and no other composition lemma changed.

The static judgment is typed W Φ Ψ Θ Δ F e T. Ψ lists the constraints of the enclosing boxes
as hypotheses on point variables. Every side condition x ≺ y is read in slt W Ψ, the closure
of ≺_W and Ψ under ≡_W and transitivity, and x ≼ y as x ≡_W y or slt W Ψ x y. E-Exp types the
body under the shifted Ψ followed by C, so a recursive call at xs must derive C[xs/ιs] from
W, Ψ and C. A derived fact survives substitution because every generator does (slt_map). A
fact of W maps by pinst_lt, a hypothesis maps by assumption, and ≡_W and transitivity hold in
the target. typed_pinst asks Ψ[σ] in slt W Ψ′ (slt_pinst_s). typed_ityped asks Ψ[σ] in ≺_{W₁},
and the box case meets the body's hypotheses from Ψ[σ] in W₁ and C[xs] in W₂ (E4 in the proof).
Without hypotheses slt W [] is ≺_W (slt_nil).

C has ≺ facts only (Claude, delegated). An ≡ hypothesis on point variables would also have
to enter ≡, with successor and slot congruence and the duality checks of tenv_comp and E-Ch,
and the static ≡ is ≡_W at every one of those places. No example so far needs one. The
infinitary it_box now carries term_wf of the body, because an unsatisfiable C makes its
premise vacuous and ityped_term_wf had read term_wf off one instance.
typed_term_wf_s reads it off the finitary derivation instead.

Example in Static.v: ordered = !(f = λp. let (c, d) = p in let () = close c in close d) at
□(∀ι ι′. {ι ≺ ι′}.^⊥ Close@ι ⊗ Close@ι′ ⊸^{ι′}_⊤ ∗) (ordered_typed). close c blocks at ι while the
body holds d at ι′, which needs the hypothesis. ordered_force forces it at ((a, 0), (a, 1)),
where program order meets C. The relay of docs/DECIDABILITY.md §8.2 still does not type. Its
recursive call at (ι+1, ι[1]+1, ζ) asks ι+1 ≺ ι[1]+1, and neither W nor C relates a slot of ι
to ι. The ceiling also fails, because ι ≺ ζ in C does not give ι+1 ≺ ζ.

**59. new in a box body cannot create a channel at a point variable (Claude, 2026-10-30). Resolved by 61 (option B).**
The factory of spec §13 is a box □(∀ι.^⊥ ∗ ⊸ S@ι) whose body runs new and spawns the worker,
so that each request yields a session at a point the caller picks. It does not type. KTNew asks
pt_known W ι of the point of new (49). A well-formed world knows constants only
(wf_names_const), so it knows no point variable (pvar_unknown in OrdExamples.v). No other rule
gives a value of type S@ι in a box body. E-Conv compares points by equality (eqT), E-Ch needs
a channel of Θ and E-Exp types the body with Θ = ∅, and a received payload lives at the slots
of the receiving point. OrdExamples.v types the factory at one constant point instead
(fac_typed, fac_deadlock_free). Its client uses the box twice but holds one session at a
time, because two sessions at (a, 0) held together ask (a, 0) ≺ (a, 0). Options, none
mechanized. (A) Keep it, so a factory serves its sessions in sequence. (B) V-Box quantifies
over known instances only, KTForce asks the instance known as it asks C (58), and the static
system reads the box's ιs as known. A recursive call at ι+1 stays known, because roots do not
change under shift. This touches V-Box, KTForce and their lemmas, as 58 did. (C) O-New also
places the root of ι, rejected in 49.

**60. Recursive boxes cannot carry their constraint to the next unrolling (Claude, 2026-10-30). Resolved by 61 (option D with a finite set of steps).**
request/reply of spec §13 does not type, and neither does the relay of docs/DECIDABILITY.md
§8.2. In request/reply the server is
srv : □(∀ι ι′. {ι ≺ ι′, ι′ ≺ ι+1}.^⊥ Sa@ι ⊗ Sb@ι′ ⊸^{ι′}_⊤ ∗), which receives on a at ι while
it holds b at ι′, replies on b at ι′ while it holds a at ι+1, and recurses at (ι+1, ι′+1)
inside a spawned thunk. The spawn removes the ceiling of 58. The thunk's lower point ι′ lies
below a at ι+1 and b at ι′+1, and its upper point is ι′+1, the upper point of the call. A
tail call would ask ι′+1 ≼ ι′ at the frame variable instead. The recursive call fails at
typed_force. It asks C at (ι+1, ι′+1), that is ι+1 ≺ ι′+1 and ι′+1 ≺ ι+2, in slt W C, and
neither is derivable. slt closes the hypotheses under ≡_W and transitivity, and a
well-formed world relates points with a variable root by program order only.
rr_call_underivable (OrdExamples.v) proves this for ι+1 ≺ ι′+1 with a rank that meets C and
program order and puts ι′+1 below ι+1. No finite C helps, because each unrolling asks C one
step further and no rule raises the offset of a hypothesis. In the relay the call
instantiates (ι, ι′) by (ι+1, ι[0]+1) and asks ι+1 ≺ ι[0]+1, which C relates only through
ι′, below both.

Options. (A) A successor law x ≺ y ⇒ x+1 ≺ y+1. As a static rule alone it is unsound. A box
under {ι ≺ ι′, ι′ ≺ ι+1} with c, d : !∗.Close sends on c, sends on d, closes c and closes d.
Closing c while it holds d at ι′+1 asks ι+1 ≺ ι′+1, which the law gives. Forced at
((a,0), (b,0)) in a world with (a,0) ≺ (b,0) ≺ (a,1) and (b,1) ≺ (a,1) (strict, ranks 0, 1, 3,
2), it runs against a partner that receives on c, receives on d, closes d and closes c. That
partner types from the world alone, and the two deadlock, the box on close c and the partner
on close d. As a law of every world it rejects deadlock-free programs that type now. Two
threads that both act on c, d, d, c need (c,0) ≺ (d,0) and (d,1) ≺ (c,1), and the law turns
the first into (c,1) ≺ (d,1). (B) Counter variables ∀κ over points (c, κ). The body still has
to derive C at κ+1 from C at κ. Either the world gives the facts uniformly in κ, which is (A)
on the names involved, or the hypotheses hold at every κ, which is (C) with a second binder
kind and its own substitution lemma. (C) Shift-invariant facts. A fact x ≺ y of C marked
invariant stands for x+n ≺ y+n for every n. KTForce and V-Box ask all of them, the body gets
all of them as hypotheses, and slt gets one generator for the shifted hypotheses. The call at
(ι+1, ι′+1) asks the facts at n+1, which are hypotheses, so request/reply types. A caller
needs a world with (a,n) ≺ (b,n) ≺ (a,n+1) for every n, strict by the ranks 2n and 2n+1. We
expect the 58 proofs to carry over unchanged in shape. Substitution commutes with shift
(pt_inst_shift), a shift keeps roots, so pcs_roots and point renaming are unaffected, and
≈_W compares facts up to ≡_W, which successor congruence preserves under shift. Not
mechanized. The cost is a flag per fact in TBox, the premise of KTForce and V-Box, the slt
generator, and the 58 lemmas passing it along. It does not cover the relay, whose step is no
shift. (D) Orbit-invariant constraints. The box declares a step substitution σ of its ιs, C
holds at every iterate σᵏ, and recursive calls go to σ(ιs). (C) is σ = shift by one. The relay
types with σ = (ι+1, ι[0]+1). This is a sound form of reading A of DECIDABILITY.md §8.1, at
the cost of σ in the type and iterates of substitutions in V-Box. Recommendation (Claude): (C)
is the smallest sound change for request/reply. (D) is needed only if the relay matters.

**61. Step-invariant constraints □(∀ιs. C.^u_Σ T) and new under □∀ (design approved by the author 2026-10-30, Rocq dc8acc1, 18b13f1).**
A box constraint is now a record bcs of steps Σ and facts. A step is a list of points, the
images of ι₀, …, ιₙ₋₁, and acts on the box's context by pext (ιᵢ ↦ sᵢ, every other variable
stays). A word applies its last step first (wsub). bcs_hold lt C xs says that the facts hold at
w(xs) for every word w over Σ, and the empty word gives C[xs/ιs]. Σ = ∅ is the box of 58, and
bcs_hold_nil turns a 58 proof into a 61 proof. V-Box ranges over the instances xs with
bcs_hold (≺_{W′}) C xs whose points W′ knows. KTForce asks bcs_hold of C at its instance in the
order konst_ty is given, and asks the instance known in the predicate konst_ty is given, a
semantic premise like pt_known for new (49). ≈_W compares the steps point by point up to ≡_W
(bcs_rel), so teqW's box clause has the same four conjuncts. bcs_hold_conv maps a word of one
constraint to the related word of the other and needs ≡_W to be a congruence for substitution
(weq_inst). sem_typed_force, sem_typed_box, it_box and ityped_force gained the new premises as
in 58. No other composition lemma changed, and no semantic lemma broke.

The static hypotheses Ψ are a list of pairs (C, xs), a constraint and its instance (hyps). The
generator sl_h of slt yields every fact of C at every word of xs (hyp_fact). E-Exp types the body
under hyps_inst (pshift m) Ψ followed by (C shifted past the ιs, ids m), the box's own constraint
at its own ιs. The static force premise is bcs_hold (slt W Ψ) C xs together with skn for the
points of xs. We chose this single premise over a separate rule for recursive calls (Claude,
delegated). A call at a step σᵢ(ιs) of the box gets the premise from the body's hypothesis by
bcs_hold_step, because the words of σᵢ(xs) are words of xs that start with σᵢ. The same lemma
serves a force of an outer box inside a body at a step of that box. Any other instance has to
show C at all words from W and Ψ, which for a ground instance means uniform facts in W
(rq_hold_W, rel_hold_W). typed_ityped asks every hypothesis of Ψ[σ] to hold in W₁ with known
instance points (hyps_hold), typed_pinst asks it in slt W Ψ′ with skn. Substitution commutes with
words (wsub_pup, pext_pup, wins_pinst), so bcs_hold_inst and hyp_fact_inst carry facts through
both lemmas.

59, option B. The static knownness is skn W Ψ x, which holds when W knows x or x has the root of
an instance point of a hypothesis. KTNew reads skn in the static system and pt_known in V-Const.
V-Box quantifies over known instances only, rather than deriving knownness elsewhere (Claude,
delegated). skn_pinst moves skn to pt_known W₁ in typed_ityped, because the instance points of
every hypothesis are known there and a point and its slots and shifts share a root. The top level
has no hypotheses, so a closed program creates channels at known constants as before.
ordered_force gained the premise that W knows (a, 0).

Examples (OrdExamples.v), all with deadlock_free closed under the global context. request/reply
(rr_deadlock_free) types the server and client at σ = (ι+1, ι′+1) and C = {ι ≺ ι′, ι′ ≺ ι+1},
and Wrr has (a,k) ≺ (b,k) ≺ (a,k+1) for every k (ranks 2k+2, 2k+3). The relay
(rel_deadlock_free) types at σ = (ι+1, ι[0]+1) with C = {ι ≺ ι′, ι ≺ ι[0], ι[0] ≺ ι+1, ι[0] ≺ ι′,
ι′ ≺ ι+1, ι′ ≺ ι[0]+1}. Its producer creates the payload channel at ι[0] with new, which needs
59, and its send of that channel asks ι ≺ ι[0]. Wrel ranks (a,k) by 3k+3, (a,k)[0]+o by
3k+4+4o and (b,0) by 5. The factory under □∀ι (fa_deadlock_free) creates its channel at ι, and
the client holds sessions at (a,0) and (b,0) at once. Both recursive examples recurse through
spawn. A tail call still asks the call's upper point below the body's (58).

**62. Approved refactors A3, A4, B4 and B5 (Rocq 32ba5c2, 5d73add, 041baa2).**
The infinitary rules are `sem_rules` in SemRules.v, and E-Abs there carries
term_wf as E-Exp does. Typing.v is reduced to Lenv.v. The cost of a label is
defined once (send, close, link 0, the rest 1), and every obligation sits at
n − cost. E and P recur on (n, size) through fuel equal to the size, because
the unfolding equation of stdlib Fix needs functional extensionality. Connect3,
PTerm and Internalize use the same measure, and their proofs were not
restructured. No statement of a composition lemma or of soundness changed.

**63. Approved refactors B2 and B3: the upper point lives on arrows, and readiness absorbs the frame.**
The box former is TBox n C T and carries no point. A box of the design has
type □(∀ιs. C_Σ. ∗ ⊸^u_⊤ T), so u sits on the thunk's arrow under the binder.
V-Box asks that the thunk λ_. fix x.t be in V at every admissible instance
(Vrel_box_iff). Vdef reads that through Vfun, the arrow clause factored out of
Vdef. Vfun reads argument and result only at lower levels, so V-Box can use it
at an instance of its type without breaking the structural recursion. A λ is in
V only at an arrow type (Vrel_lam_inv), so a box type whose body is no arrow is
empty. Vrel_box_thunk_iff unfolds V-Box at a thunk type to the clause of 52, and
the composition lemmas for force and E-Exp use it unchanged. force has type
□(∀ιs. C_Σ. ∗ ⊸^u_⊤ T) ⊸^{u[xs/ιs]}_⊤ T[xs/ιs] (KTForce). The lemmas that map V
along a transformation (swap of points, swap of channels, ≈, ≈_W, index) prove
the arrow case first and use it at the instance in the box case.

ready_t W Θ F t is ready_W(Θ ∣ F, t). Every offered head lies below every head
of Θ that is not offered and below every point of F (below_rest). E-Step has one
premise. For a term the change is a strengthening only at a link, whose two
offered entries are compared one by one, and every typed link holds both
entries alone, so no proof needed more. The bind lemma reads the context's heads
as points of the hole's frame, as 48 says. P keeps its readiness. The
unified form at F = ∅ is false for processes. Two components that offer at
unrelated points (a,0) and (c,0), with held entries at (b,5) above (a,0) and
(d,0) above (c,0), are each ready, and their parallel composition (P-Connect
with an empty cut) would need (a,0) ≺ (d,0). ready_term (Chain.v) turns the
term's readiness into the process's. It needs an offered entry, which a stable
term that is no value has (offered_some, now in Junk.v), and the term not
irreducible. Both are new hypotheses of its section. No statement of a
composition lemma or of soundness changed beyond the box types, which read
TBox m C (TLolli ub None TUnit T) where they read TBox m C ub T.

**64. Approved refactor B1: one fact theory.**
The static system reads every fact from one judgment fl Γ a b, written
Γ ⊢ a ≺ b, over nodes, which are points and frame variables (Static.v). The
context Γ = (W, Ψ, Φ) has three generators: x ≺_W y, the facts of a hypothesis
(C, xs) at every word of xs, and u ≺ φ for a frame hypothesis. The judgment is
closed under ≡_W and under transitivity through a point. A frame variable never
sits in the middle of a derivation, because no generator has one on the left.
slt W Ψ is the fragment between points, and it does not depend on Φ
(fl_points). ub_below_s is the judgment from u to every node of the frame, and
ub_below_h is gone. fl_map carries a derivation along any map of the generators.
Point substitution is fl_map with σ on points (fl_pinst). Instantiating the frame
variables into a world is fl_map with each node read as the points it stands for
(ub_below_s_inst). Without hypotheses the judgment is ≺_W (slt_nil), which makes
the world the ground case. The force premise stays C at every word of its
instance in Γ. The step invariance of 61 needs no closure condition on Γ,
because the facts of a hypothesis are generated at every word. typed keeps W,
Φ and Ψ as separate arguments, which together form Γ. No statement of a
composition lemma, of soundness or of the semantic relation changed. The
examples in Static.v and OrdExamples.v prove {u} ≺ F through
ub_below_s_intro, which reads the frame variable as x ≼ u for its hypothesis.

**65. Free constraints replace steps, and slots become carried roots (decided by the author 2026-10-30, spec only, Rocq pending).**
Steps were hard to read, and the restrictions of 58 and 61 (finite C, ≺ facts
only, invariance by words) came from decidability, which the author postponed.
A constraint is now any set of positive facts x ≺ y and x ≡ y, finite or
infinite, written with set-builder notation. Positivity is the one semantic
limit, because V-Box must persist along ⊑ and a fact x ⊀ y does not. Steps
leave the core. A recursive call is a force like any other and asks Γ ⊢ C at
its instance, which holds whenever the instance of C is contained in C. C is
the invariant of the recursion and states the facts of every round at once.
≡ in C lets a box body delegate a channel it did not create, so the static
system reads ≡ from Γ as a congruence over W and the hypotheses. Slots are
renamed carried roots, written x.i with positions from 1, and §4 of the spec
states why they exist. The infinite sets give three programs the old design
rejected: a tail call with a ceiling ζ and {ι+k ≺ ζ ∣ k ∈ ℕ}, a forwarder
inside a box, and recursion on a received channel. None is checked in Rocq
yet. Decidability moves to §16 as a question about a fragment, with the
counter language of docs/DECIDABILITY.md as the candidate.

**66. Rocq port of 65 (Claude, 2026-10-30, Rocq 297c45f, d3dfbe4).**
A constraint is a closure BCs env P (Types.v). P is a predicate on facts
FLt x y and FEq x y whose points have variable roots only. The variables
0, …, n−1 are the box's ιs, and n + j is the j-th point of env, which
lives outside the binder and carries the outer point variables and
constants. Substitution and renaming of points act on env alone, so
pinst_ty, the swaps of Points.v and their equations hold by computation
on lists, with no functional extensionality. The image of P under
substitution, which the spec writes C[σ], is bcs_open n C, and
bcs_open_inst and bcs_open_sw state that it commutes with substitution
and renaming. A fact whose variables lie beyond n + |env| is not part of
C. The representation forces one restriction the spec does not state. A
constraint has finitely many roots, those of env. A type with infinitely
many constant roots would leave O-New no fresh point, so the restriction
is needed anyway. bcs_hold eq lt C xs asks every open fact at xs, ≺ in
lt and ≡ in eq. V-Box, KTForce, sem_typed_force and sem_typed_box read
it in W′ with both relations. ≈_W on constraints (bcs_rel) relates two
constraints when every open fact of one has an open fact of the other of
the same kind with points related by ≈_W, in both directions.
bcs_hold_conv moves a constraint along it.

The fact theory has a second judgment seqs W Ψ, the least congruence for
successor and slots that contains ≡ of W and the ≡ facts of the
hypotheses. fl is closed under it. fl_map maps both judgments along one
map of the generators and concludes their conjunction. fl_pinst,
seqs_pinst and slt_pinst are its instances. E-Const reads konst_ty at
seqs W Ψ, so link compares its ends in Γ ⊢ ≡. E-Ch and the composition
of environments read seqs W Ψ too. P-Term and P-Connect keep ≡ of W,
because Ψ = [] at process level. Hypotheses stay a list of (C, xs), with
hyps_inst σ substituting env and xs. Steps, words, wsub, pext,
bcs_hold_step and bcs_hold_nil are gone. A recursive call is a force.
bcs_hold_sub derives C at an instance ys from the body's hypothesis (C, xs)
when every fact of C[ys] is a fact of C[xs], and bcs_hold_self is the case
of a constraint without outer points, C[ys] ⊆ C. No statement of a
composition lemma or of soundness changed beyond the types of the box
premises. Static.v grew from 1819 to 1840 lines.

Examples (OrdExamples.v), all with deadlock_free closed under the global
context. request/reply has C = {ι+k ≺ ι′+k, ι′+k ≺ ι+k+1 ∣ k}, and its
call at (ι+1, ι′+1) is rq_step. rr_call_underivable now states that the
one-round constraint {ι ≺ ι′, ι′ ≺ ι+1} does not give ι+1 ≺ ι′+1, by a
rank that meets the hypotheses, program order and ≡, which relates
points with variable roots by equality only. The relay has
C = C₀(ι, ι′) ∪ {C₀(ι+k+1, ι+k[0]+1) ∣ k} with slots from 0. Its call at
(ι+1, ι[0]+1) maps round 0 to round 0 of the family and round k+1 to
round k+2 (rel_sub). The tail call (tc_deadlock_free) types without spawn
under {ι+k ≺ ζ ∣ k}. Its world has (a,k) ≺ (z,0) for every k, which no
rank into ℕ orders, so wgen_strict_lex uses a pair rank. Recursion on a
received channel (ch_deadlock_free) types with
C = {ι[0]ⁿ + 1 ≺ ι[0]ⁿ⁺¹ ∣ n} and recursion through spawn. The upper point
ι+1 of its λ covers the receive at ι and the close at ι+1, and the call
forces the box at ι[0].

The forwarder does not type, and the obstacle is not the constraint. recv
gives the received channel d the type D@ι[0]. send on the outgoing channel
at ι′ is the constant send at its KTSend instance, whose payload is D@ι′[0].
E-Const types a constant at its instance exactly, E-Conv compares points by
equality, and only E-Ch moves the point of a type along ≡, for a channel
name. So no derivation gives the variable d the type D@ι′[0], and the fact
ι[0] ≡ ι′[0] is never read. Spec §9 lists the payload of send and recv
among the comparisons that read Γ ⊢ ≡, and no rule of §9 or of Rocq does
that for a variable. Inside a box Θ = ∅, so Γ ⊢ ≡ reaches link alone. The
missing rule is E-Conv up to ≈ with points compared by Γ ⊢ ≡. Its semantic
side would be rel_tconv along ≈ of W₁ after seqs_pinst. It is a change of
the static system and waits for the author.

Slots stay 0-based in Rocq (pt_slot x i, slots x m = x[0], …, x[m−1]). The
spec's carried root x.i with i ≥ 1 is pt_slot x (i−1).

**67. E-Conv up to Γ ⊢ ≡ (decided by the author 2026-10-30, Rocq done).**
E-Conv now converts T to T′ when they agree up to ≈ and Γ ⊢ ≡ relates
their points. The relation is steq W Ψ (Static.v). It compares the
points of session types and the upper and lower points of arrows by
seqs W Ψ, session types by ≈, and boxes by ≈ with points on the nose.
A box keeps syntactic points because its points live under the binder
of its ιs, where Γ ⊢ ≡ of the outer context says nothing. teq_steq makes
the old rule a special case, and the examples reach it through
conv_sess. Soundness is steq_teqW. Under an instantiation σ whose
hypotheses hold in W₁, seqs_pinst maps Γ ⊢ ≡ to ≡ of W₁, and
w_eq_pteqW turns that into ≈_W₁, because in a well-formed world only
ground points have proper aliases. sr_conv in SemRules.v now takes ≈_W
in place of ≈. Its compositionality lemma sem_typed_tconv (Conversion.v)
is rel_tconv in every later world, with ≈_W carried along W ⊑ W′ by
teqW_mono. typed_pinst carries steq along σ by steq_pinst_s. No
statement of soundness, of the fundamental theorems or of an existing
composition lemma changed.

The forwarder of 66 types (fwd_typed in OrdExamples.v). Its box has
Cf = {ι+k ≺ ι′+k, ι′+k ≺ ι+k+1, ι′+k ≺ (ι′+k)[0], (ι+k)[0] ≡ (ι′+k)[0] ∣ k}.
recv gives d the type Close@ι[0], E-Conv moves it to Close@ι′[0] along
the ≡ fact of Cf, and the send at ι′ asks ι′ ≺ ι′[0] for its payload.
The recursive call at (ι+1, ι′+1) asks Cf one round later, which Cf
contains. fw_main runs a producer, the forwarder and a consumer over
two channels a and b. The producer and the consumer share
Cp = {ι+k ≺ (ι+k)[0], (ι+k)[0] ≺ ι+k+1 ∣ k}, and the producer creates
its payload at the slot with new. The world Wfw has (b,k)[0] ≡ (a,k)[0]
for every k. wgen_strict needs a name map that commutes with slots, and
no such map identifies (b,k)[0] with (a,k)[0] without identifying (b,k)
with (a,k). wgen_strict_cong asks only that the map respects slots,
cn x = cn y ⇒ cn x[i] = cn y[i]. fw_cn reads (b,k)[0] as (a,k)[0] at
every depth, and the rank orders (a,k), (b,k), (a,k)[0] by 3k, 3k+1,
3k+2. fw_deadlock_free is closed under the global context.

**68. Link does not block (decided by the author 2026-10-30).**
The paper types link : S × S̄ ⊸ 1 with no order at all. The port made it
blocking without a decision. Readiness counted the two entries of a c↔d
redex as offered, so every other held entry and the frame had to lie above
them, and the signature S@ι ⊗ S′@ι′ ⊸^ι_⊤ ∗ made E-App ask {ι} ≺ F. A link
never waits for a partner. P-Act-Link fires it as a τ as soon as one of its
channels is restricted, and a closed process restricts every channel, so a
stable closed process never holds a link redex.

Decision. A thread at a link imposes no order fact, and link has upper point ⊥.

```
link(t)  ≔  ∃cd t′. t —c↔d→ t′            link(p)  ≔  ∃cd p′. p —c↔d→ p′

ready_W(Θ ∣ F, t) ≔ stable(t) ⇒
                      (offered(t) = ∅  ⇒  t is a value)
                    ∧ (link(t)  ∨  ∀o ∈ offered(t). ∀y ∈ heads(entries(Θ) ∖ offered(t)) ∪ F. head(o) ≺_W y)

ready_W(Σ, p) ≔ stable(p) ⇒
                  link(p)
                ∨ ((offered(p) = ∅  ⇒  p is terminated)
                   ∧ ∀e ∈ entries(Σ) ∖ offered(p). ∃o ∈ offered(p). head(o) ≺_W head(e))

link : S@ι ⊗ S′@ι′ ⊸^⊥_⊤ ∗          S ⊥ S′,  ι ≡_Γ ι′
```

offered and selects keep c↔d. The first conjunct of the term form still asks
an entry of Θ for one of the link's channels, and a link label still selects
both entries. Only the comparisons go.

The process form exempts the whole process, not only the link entries. A
single thread K[link ⟨c, d⟩] that also holds e gives P-Term no offered entry
below e, because its term readiness compares nothing. A per-entry exemption
would therefore fail P-Term. The whole-process exemption is sound for the
composition lemmas. In a stable composite a component's link redex has no
restricted channel, or the composite would fire it as a τ. So the
composite has the same redex and is ready by its first disjunct. If the
composite has no link redex, neither component has one, and both components
satisfy the old condition, on which the old chain argument runs unchanged.
Internalizing a link argues the same way. A link redex of the unfused
process that touches c or d becomes one on the restricted d of the fused
process and would fire. Adequacy never reads readiness. It reads only that
a session step at Σ = ∅ has no obligation to meet.

One consequence reaches the bind lemma. The old frame H kept every redex of
the hole off the channels of the context, a link included. A link may now act
on the other end of a channel the context holds, as in
let (c₁, c₂) = new ∗ in let () = link ⟨c₁, d⟩ in close c₂, which types now.
Bind.v splits subjs_free in two. subjs_free_br reads the comparisons and covers
every redex, and subjs_free covers every redex but a link. The link case of
Erel_bind moves the context's end with comp_ext_gen, which extends
comp_ext to a context that holds the other end of the linked channel.

Rocq. Readiness.v defines link_t and link_p and the two disjuncts. The static
side is konst_ty with KTLink at TLolli None None, and Erel_app_link (TermRules.v)
is ready by its link redex. The proofs that changed are these.
ReadyChain.v proves the old chain argument as ready_connect_core for
components in their second disjunct, and ready_connect lifts a component's link
redex to the composite by link_l and link_r. ready_term turns a link redex of
the thread into link(p) and uses link_t_only (a term at a link offers nothing
else) in no_cut_offer. fused_ready (Internalize.v) concludes link(q) or the old
condition. Prel_S_ready and conn_stop (ConnectCut.v) and term_level (PTerm.v)
take the new disjunct. Prel_junk, fusion_exclusion and the fused Erel lemma
(JunkRenaming.v) carry it through substitution. The invariance lemmas
ready_t_sw, ready_p_sw, ready_t_wsame, ready_p_wsame, ready_t_swap,
ready_p_swap, ready_t_conv, ready_p_conv, ready_t_mono and ready_p_mono carry
link_t and link_p. Scheduler.v closes the link application by ubs_none, and
Rejected.v keeps badlink, whose argument reads only the alias. No statement of
soundness, of the fundamental theorems, of adequacy or of a composition lemma
changed.

**69. Adequacy for repaired PGV (Claude, 2026-10-30, theories/pgv/). Number 68 is taken by the non-blocking link.**
A closed program of type 1 in the monotone fragment of repaired PGV is deadlock
free (`pgv_deadlock_free`, closed under the global context). The PGV judgment
is Fig. 2 on our terms with R1 in the schemas of send and recv and R2 in
T-Pair. Every derivation becomes a derivation of `typed` at one world `Wpgv`
for every frame above u_p, and `soundness` finishes. The world has one point
per session type up to duality. Its ≡ is "same denotation" and its ≺ is
"rising rank" on the root constant. A canonical map into points would have to
commute with successor and would merge two protocols with one continuation, so
the denotation goes into a separate domain. u_⊤ for the upper bound ⊤ lies
above every u_n and takes a pair rank. The proof needs o < pr(S) only at the
session types that send and recv act on, and only at the top. The fragment
asks it recursively, as decided. The upper point of our send is the channel's
point and PGV's is u_o, so an unapplied send, recv, close or wait becomes
λz. k z (`pgv_eta`). Applied ones stay, and a program that applies all of them
is its own translation (`pgv_deadlock_free_applied`). Left out are 0 and
absurd. link is in after 68. Its schema S × S̄ ⊸ 1 maps to KTLink, and both
ends sit at a[code S], so ι ≡ ι′ holds by reflexivity
(`pgv_link_deadlock_free`).

**70. Adequacy for repaired Padovani and Novara (Claude, 2026-10-30, theories/pn/).**
The translation of a closed program of type unit in fragment v1 of Padovani and
Novara with repair R2 is deadlock free (`pn_deadlock_free`, closed under the
global context), and so are parallel Fibonacci and the signal pipe
(`fibo_deadlock_free`, `pipe_deadlock_free`). The judgment `pn_typed` is Table 2
with T-App-Poly on our terms and yields the translated term, because the
translation needs types. A function of level ⊤ becomes a box over one point
variable, the level anchor, and every level is a slot of the anchor. Shifted
copies of one arrow get one box type, normalized by the arrow's first finite
level. The box constraint is the infinite set of facts that a denotation and a
rank give between points of the variable, and a force at the anchor B[RAnc a]
meets it because instantiation adds a to every level. T-App-Poly at n is a force
at the anchor shifted by n. The world identifies points of the root with one
denotation and orders them by rank in ℤ with a top element, the ceiling for the
latent effect ⊤ (new helpers `zrank`, `wgen_strict_den` in ExampleTools.v). The
translation lemma holds at every anchor, every offset (which is the shift lemma
that section 4 of padovani-novara.md asked for) and every frame above the
effect. The static system has no lemma that inserts a binding, so the lemma
types the term renamed past inserted unlimited entries. unit becomes the box of
∗, because P&N's unit is unlimited. send and recv close the one-shot channel.
Restrictions of v1 are unit and sums of unlimited types as basic types, new only
in let form, constants only applied, recursive types only μα.p[⌈α⌉ᵐ]ⁿ with
wrap and unwrap erased and conversion at the top of a type, payloads channels or
unlimited, and arrow level ⊥ left out. padovani-novara.md §7 lists every
discrepancy. No core change.

**71. Padovani and Novara in their own semantics (Claude, 2026-10-30, theories/pn/).**
`pn_deadlock_free_source` makes a closed program of type unit deadlock free in
the sense of Definition 1 of the chapter, in the chapter's semantics
(PNSemantics.v), when every fix is fix λf.λx.e (`fixlam`). fibo and the pipe
follow (`fibo_deadlock_free_src`, `pipe_deadlock_free_src`). The proof is a
forward simulation into the target and a normalization of administrative steps
when the source is stuck (PNSimulation.v). The relation `trel` is untyped up to
modes, the shape of a P&N type that the translation reads, with one mode per
channel name in Ξ, so that sender and receiver agree on the payload. It is
closed under substitution, and the renaming inside a box and the unfolding of
fix commute with it. The extra close never blocks, because the simulation of a
communication performs the message, the receiver's β and both closes in one
step, and a related target never offers a close. fix λf.e with e no λ breaks the
simulation. The source runs e once at the unfolding, the target runs e′ at every
force, and an effect in e (fork is pure) then gives different thread pools.
The translation is unchanged, and the theorem asks `fixlam` instead.
padovani-novara.md §8 lists every deviation of the source semantics from the
chapter. No core change.

**90. A channel at a fresh point between known points (Claude, 2026-11-01, branch fresh-points). Numbers 72 to 89 are reserved on another branch.**
No point built from existing names lies strictly between two given points, so a
box over ι ≺ κ cannot create a channel between them
(`fb_between_underivable`). E-NewFresh (`t_newfresh`, static/Typing.v) types
let (x, y) = new ∗ in t with the channel at a fresh point ι and the facts
L ≺ ι ≺ H for lists L and H of known points. Betweenness asks Γ ⊢ l ≺ h for
every l ∈ L and h ∈ H, and it is the soundness condition. Without it the world
of a run could hold h ≺ l and close a cycle through ι. Three choices. ι is a
bound point variable, as the ιs of E-Exp are, so freshness is the binder and
costs no side condition. The facts enter the body as one more box hypothesis
(`fresh_bcs L H`, instance [ι]), so the fact theory, knownness and
substitution need no new clause. C holds ≺ facts between ι itself and known
points only, because ≡ to an old point is E-Const and no example needs facts
on ι+k or ι.i. The fundamental case of `typed_sem_rules` instantiates ι with
the constant that O-New picks. docs/extensions/fresh-points.md has the rule
and the proof.

**91. World extension already admits fresh points (Claude, 2026-11-01).**
The task expected ⊑ₒ to change, because it seemed to add only facts among new
points. It does not. Both `wext_fresh` and the ⊑ₒ of gvsharp-orders.lagda
forbid only new facts between two old points and let the fresh constant relate
to old ones, which E-Const uses for its alias (a, 0) ≡ ι. With betweenness the
world W plus L ≺ (a, 0) ≺ H adds no fact between old points and stays strict
(`wext_fresh_between`, rules/FreshRules.v, by the closed form `blt` of its
order). So ⊑ₒ, `fresh_extension`, `wext_fresh_join` and the composition lemmas
are unchanged, and so are the statements of `soundness`, `fundamental` and
`fundamental_proc`.

**92. Fresh points shrink the worlds of closed programs (Claude, 2026-11-01).**
examples/FreshBetween.v types the box of 90 with L = [ι] and H = [κ] and closes
it into a program with partners (`fb_deadlock_free`, at the world with the one
fact (0, 0) ≺ (1, 0)). The same program types with E-NewFresh for its two
top-level news, the second one above the first (L = [γ]). It then needs no
constant and no fact, and `fb_deadlock_free_empty` applies `soundness` in the
empty world. A closed example can move its world facts into E-NewFresh this way
when each fact relates the first point of a channel to points that exist when
the channel is created. Facts on a later instant of the new channel, such as
(b, 1) ≺ (a, 0), stay in the world. The existing examples were left as they
are. Entry 93 lifts this restriction.

**93. Facts on every point of the fresh channel (Claude, 2026-11-01, second stage).**
The list form L ≺ ι ≺ H cannot type a fresh channel that acts several times
while a later point waits (examples/FreshMany.v needs δ+k ≺ κ for k = 0, 1, 2).
`t_newfresh` now takes a box constraint C of one variable whose every fact
relates one point of ι (ι+k, (ι+b).i+k, and deeper carried points) to one outer
point, in either direction (`fresh_ok`, `fresh_lo`, `fresh_hi`). C may be
infinite. The list form is the lemma `t_newfresh_lh`, and FreshBetween.v uses
it unchanged. Two choices. C has no fact between two points of ι, because then
paths could run inside ι and C would need its own strictness. C has no ≡ fact
(96). The semantic rule takes two relations Lo and Hi with the fresh point as
the variable 0, so rules/ needs no box constraints, and `pfresh` puts the
constant in.

**94. The exact betweenness for points of the fresh channel (Claude, 2026-11-01).**
For every fact u ≺ p and q ≺ v of C with q on the name of p at an offset at
least that of p (`ple p q`), Γ ⊢ u ≺ v. A path through a enters at p, moves only
along program order of one name, and leaves at q. Carried roots do not connect
ι to ι.i in order, because a world relates a carried point to its base only
through facts and C has none between points of ι. So "q reachable from p by
program order or carried roots" in the task reduces to `ple p q`.
`wext_fresh_between_gen` builds the world with a closed form `gblt` of four
shapes and a sixteen-case transitivity proof. Betweenness closes the four cases
in which a path leaves a after it entered.

**95. Retyping the closed examples with fresh points (Claude, 2026-11-01).**
Sync, cycle, scheduler and request/reply type in the empty world, tail call
keeps the constant of its ceiling, and relay keeps the constant of c with its
facts on its own carried points (SyncFresh.v, CycleFresh.v, SchedulerFresh.v,
RequestReplyFresh.v, TailCallFresh.v, RelayFresh.v). Scheduler creates r₁ by
E-Const at the fresh point of r₀, which gives the alias that link needs.
Request/reply puts the infinite family {γ+k ≺ ε+k, ε+k ≺ γ+k+1} into C, and
program order gives its betweenness. Delegation and received chain do not
retype, because their facts relate a channel to its own carried points (93).
Forwarder does not, because it aliases carried points of two channels for every
k. Factory under □∀ι creates no channel in main. No box constraint gets
simpler. fresh-points.md has the table.

**96. One ≡ fact in E-NewFresh not done (Claude, 2026-11-01).**
The optional part was to allow one fact ι ≡ x and to derive E-Const at x from
it. An alias identifies every successor and carried point of ι with those of
x, so the semantic world combines the alias world `W0'` of E-Const with `Wg`,
and strictness and conservativity need a closed form for the combination. That
is a second argument of the size of 94, so it stays open. E-Const is unchanged.

## From the earlier abandoned mechanization (spec §15)


Leastness as gate, a gate that is not invariant under external steps, the
premise "distinct channels have distinct instants", term-level ∀-introduction,
and a window condition on all pending heads. Each is avoided by a design choice
recorded in §15.

## History of the channel-named worlds

Entries 18 to 36, except 26, belong to the design in which worlds stated facts
about channel names. Entry 37 replaced it with points-only worlds and removed
the common cause. Each entry keeps its number and title so that references in
commits stay valid.

**18. (A) Process-level new did not extend the world.**
Process-level new left the process world unchanged while the thread's world
grew, so a thread that created and sent a channel failed at process level. The
fix let Q-Tau grow the world (21).

**19. (B) An internal link renames a visible channel.**
After P-Act-Link removed c, the environment talked over d, and the world knew
nothing about d. The paper gets this from invariance under channel substitution,
which fails once names carry order facts. The fix made c and d aliases at an
internal link.

**20. (C) Worlds lacked slot congruence, and old names could carry stale facts.**
Worlds lacked x ≡ y ⇒ x[i] ≡ y[i], so renaming along an alias failed, and a
received name the world already knew inherited stale facts. The fix made slot
congruence a world law and required received channels to be unknown to W. Slot
congruence survives in the current design.

**21. One Q-Tau instead of special rules.**
Q-Tau let the world grow invisibly, over names restricted before or after the
step, and checked a step only when its restricted channels avoided the
interface. This replaced special rules for new and link.

**22. Adequacy needs a renaming lemma for the LTS.**
Q-Tau checked only runs whose fresh names W did not know. A renaming lemma for
the LTS (Swap.v) covered the other runs.

**23. (D) The environment's world can mention restricted names.**
Q-Recv quantified over every larger world, and such a world could state facts
about names the process restricts. Independence and P-monotonicity failed. The
fix bound restricted names and made V, E and P invariant under renaming channel
names (Equivariance.v).

**24. (E) Renaming alone does not repair it.**
Renaming moved the stale fact onto the new name, and Q-Recv demanded the exact
successor. The fix let the continuation of Q-Recv hold for an α-variant of the
successor that renames only restricted names.

**25. P is monotone in the world only up to renaming.**
A larger world could mention restricted names, so P was monotone only up to
renaming. V and E stayed monotone over well-formed worlds.

**27. (F) Renaming private names must not touch types.**
P-Connect renamed private names, and renaming touched names that types mention,
so the renamed process left its interface. Decision F2 kept channel names out of
types, with points in types as bound variables, point constants and their slots.
The current design keeps this.

**28. P is not monotone in the world, even up to renaming.**
A larger world could state stale facts about a restricted name, so P was not
monotone even up to renaming. Monotonicity was stated only for extensions that
touch no restricted name.

**29. (G) link substitutes in the whole soup.**
P-Act-Link wrote [d/c] into every thread, so a junk occurrence of c in the other
component merged with a live channel. Decision G2 ported the paper's
junk-collapse lemma (Junk.v) to worlds.

**30. Internal links: α-closure instead of an alias; the paper's junk argument works again.**
An alias obligation on internal links made junk collapse false. The fix bound
restricted names in every step obligation, so the two successors of a link
between a cut channel and a restricted one differ by a transposition and need no
alias.

**31. (I) Which names may an α-variant introduce?**
An α-variant could rename a restricted name to an interface name or to one with
stale facts. Decision I1 allowed only names outside the interface and unknown to
the step's world.

**32. (J) Fresh for which world?**
Under I1 the channel created at new carries facts after the step and cannot be
fresh for that world, so P-Term failed. Decision J1 required freshness for the
world before the step.

**33. (K) Fresh for the environment's world at a receive.**
After J1 an α-variant at Q-Recv could pick a name known to the environment's
world W″. Decision K1 required freshness for W″, so a name had to be fresh for
every fact the process did not add itself.

**34. (L) The junk target can become restricted later.**
A junk target b could later become restricted, and then the two orientations of
a link differed by a transposition of two world-known names. The fix let
internal steps act only on owned or restricted channels.

**35. Link as a forwarder (author's decision).**
Entries 19 and 29 to 34 shared one cause, the substitution of a channel name in
the whole soup. The author replaced link by a forwarder thread and undid the
link-only machinery.

**36. (M) An untyped forwarder is not in E.**
An untyped forwarder could fire a label its session type forbids, so it was not
in E. Decision M1 made the forwarder follow the session type. Entry 37 then
showed that the forwarder fails readiness, and the forwarder went away.
