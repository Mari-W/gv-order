# Sharp edges

Every place where the order-based design turned out subtler than it looked,
in the order we hit them. Each entry gives the problem, a minimal witness, the
decision, and where it lives in ORDERS-SPEC.md. Entries 1 to 12 came up while
designing, entries 13 onward while mechanizing.

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

**18. (A) Process-level new did not extend the world.** *(superseded, see 37)*
The thread's world grows at new, the process world did not, so a thread that
creates a channel and sends it failed at process level.
Decision: Q-Tau may grow the world (entry 21).

**19. (B) An internal link renames a visible channel.** *(superseded, see 37)*
After P-Act-Link removing c, the environment talks over d, and the world knows
nothing about d. The paper got this for free from invariance under channel
substitution, which fails once names carry order facts.
Decision: an internal link must make c and d aliases. The step may create the
alias (entry 21).

**20. (C) Worlds lacked slot congruence, and old names could carry stale facts.** *(superseded, see 37 (slot congruence stays))*
x ≡ y did not give x[i] ≡ y[i], so renaming along an alias failed. A channel
arriving under a name the world already knows would inherit old facts.
Decision: slot congruence is a world law, and received channels must be unknown
to W except returning ones (§5, §7).

**21. One Q-Tau instead of special rules.** *(superseded, see 37)*
The world may grow during a τ step, but only invisibly, so nothing changes
between names the environment can see. The invisible names are those
restricted before or after the step, so a link removing d can still create the
alias. The step is checked only when its restricted channels are disjoint from
the interface, the paper's implicit convention made explicit (§7, lemma
"invisible extension" in §10).

**22. Adequacy needs a renaming lemma for the LTS.** *(superseded, see 37)*
Q-Tau only checks runs whose fresh names are unknown to W. Other runs are
renamings of checked runs (Swap.v, §10, §12).

**23. (D) The environment's world can mention restricted names.** *(superseded, see 37)*
Q-Recv quantifies over every larger world, and such a world may state facts
about names the process restricts. Witness: a component placed its internal r
for a later send, and the environment's world contradicts that placement.
Independence and P-monotonicity fail.
Decision: restricted names are bound. V, E and P are invariant under renaming
channel names, worlds and types included (Equivariance.v, §10).

**24. (E) Renaming alone does not repair it.** *(superseded, see 37)*
Renaming moves the stale fact onto the new name, and Q-Recv demanded the exact
successor.
Decision: Q-Recv's continuation holds for some α-variant of the successor,
renaming only its restricted names (§7).

**25. P is monotone in the world only up to renaming.** *(superseded, see 37)*
A larger world may mention restricted names. V and E are monotone, given a
well-formed world (§10).

**26. Deciding strictness of W_G.**
Uniform schemas fall under Kosaraju and Sullivan's zero-cycle algorithm. Facts
with a counter on one side only need a free-coordinate extension, which we
believe decidable but have to prove. Uniformity is not a restriction, because
the static system produces only equal or independent counters (§12).

**27. (F) Renaming private names must not touch types.** *(superseded, see 37 (completed))*
P-Connect renames the private names of the component that does not receive,
and renaming acts on every channel name, including names a type mentions. If a
fresh name appears in a session type of Σ or in the process type, the renamed
process no longer fits the same interface. No semantic counterexample, only an
obstruction to the proof.
Decision (F2): types never mention channel names. Points in types are bound
variables, point constants and slots of those. Channels appear only in worlds
and environments, and types reach them through aliases (§4, §7).

**28. P is not monotone in the world, even up to renaming.** *(superseded, see 37)*
A larger world can state stale facts about a restricted name, and renaming
only moves the needed facts onto the new name.
Decision: stated only for extensions that touch no restricted name. P-Connect
keeps one world per component and does not need more (§10).

**29. (G) link substitutes in the whole soup.** *(superseded, see 37)*
P-Act-Link writes [d/c] into every thread, also into the other component's.
A junk occurrence of c there would merge with a live channel.
Decision (G2): port the paper's junk-collapse lemma (Junk.v) to worlds, so the
composition lemmas need no tightness premise (§10).

**30. Internal links: α-closure instead of an alias; the paper's junk argument works again.** *(superseded, see 37)*
With an alias obligation on internal τ links (an external c linked to a restricted d), junk
collapse is false: ({d}, {link⟨x,d⟩, (λy.∗) d, close b}) is related in a world with
(b,0) ≺ (d,0), because its link names the junk x and owes nothing, but renaming x to b gives
link⟨b,d⟩ with b external, which owes b@0 ≡ d@j, impossible above that fact.
Decision: restricted names are bound in every step obligation (each Q-clause holds for some
α-variant of the successor). A link between a cut channel c and a component's restricted d
can remove c or d, and the two successors differ by the transposition (c d), so the
composite's step reduces to the component's own step and needs no alias. The alias stays on
O-Link and Q-Link. The freshness guard at new is subsumed (§7, §10).

**31. (I) Which names may an α-variant introduce?** *(superseded, see 37)*
If an α-variant may rename a restricted name to any name absent from the
process, it can pick an interface name or a name the world has facts about.
The junk transport then cannot reuse the variant after renaming, and moving
the world would need an unproved monotonicity.
Decision (I1, taken by Claude under the author's delegation): α-variants are
capture-avoiding, renaming only to names outside the interface and unknown to
the step's world. The paper's freshness convention with the world in scope (§7).

**32. (J) Fresh for which world?** *(superseded, see 37)*
I1 required the names an α-variant introduces to be unknown to the world after
the step. At new that is impossible: the created channel must carry facts in
the new world, so it can never be renamed away from a name with stale facts,
and P-Term fails (witness: new picks a name with a conflicting stale fact and
then sends it).
Decision (J1, Claude, delegated): fresh for the world before the step, in
every clause. The created channel is renamed to a fresh name first and placed
by the step (§7).

**33. (K) Fresh for the environment's world at a receive.** *(superseded, see 37)*
After J1, a Q-Recv α-variant could introduce a name fresh for W but known to
the environment's world W″, which carries the environment's stale facts. The
junk transport cannot replace such a witness.
Decision (K1, Claude, delegated): at Q-Recv, names are fresh for W″. Together
with I1 and J1 the rule is "fresh for every fact the process did not add
itself" (§7).

**34. (L) The junk target can become restricted later.** *(superseded, see 37)*
In P-Connect the junk target b is a live cut channel, which can later move
into comp2 and become restricted. A junk redex link⟨x, r⟩ in the original
then becomes link⟨b, r⟩ with both names restricted and known to the world, and
the two link orientations differ by a transposition of two world-known names,
which neither an α-step nor an invisible world move bridges.
Decision (Claude, delegated): semantic ownership in Q-Tau. An internal step may
only act on owned or restricted channels, so the original never executes a link
on junk, and neither does the renamed process. Rejected: building tightness
(fchans ⊆ dom Σ ∪ C) into E and P, because it is syntactic (§7).

**35. Link as a forwarder (author's decision).** *(superseded, see 37)*
Entries 19 (B), 29 (G), 30, 31 (I), 32 (J), 33 (K) and 34 (L) all came from one
cause: P-Act-Link substitutes a channel name in the whole soup, and with names
carrying order facts every substitution needs an argument (aliases, junk,
orientation, α-freshness). Decision: link ⟨c, d⟩ becomes a forwarder thread
that relays messages, with no substitution anywhere in the LTS. The link-only
machinery is undone (renaming along an alias, junk collapse, internalizing a
link, α-closure of every clause, I1/J1/K1, ownership). A self-link still
releases the channel. Reduction semantics and Harmony change (§3, §7, §10).

**36. (M) An untyped forwarder is not in E.** *(superseded, see 37)*
E asks every label for its clause. An untyped fwd c d can fire c?v while c has
type !P.S, and O-Recv then has no head to consume, so fwd c d ∉ E for every S
other than Close, although no well-typed partner ever fires that label.
Decision (M1, Claude, delegated): the forwarder follows the session type.
link carries its type S, filled in by typing (surface syntax unchanged), and
link_S ⟨c, d⟩ —β→ fwd_S c d reads only on the receiving side. E, P and the
O-clauses stay as they are. Rejected M2 (no obligation for labels of the wrong
kind), because it changes E and P and endangers the chain arguments (§2, §7).

**37. (N) Facts on channel names were the cause.**
With M1 the forwarder failed readiness: it reads before it writes, so it offers
one of its two entries while the other sits at the same instant. The relation
was right. link ⟨a, b⟩ ∥ link ⟨b, a⟩ over a P-Connect cut {a, b} deadlocks
under forwarders and terminates under substitution. A separate analysis traced
entries 18 to 36 to one cause: worlds attached facts to channel names, and every
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

**54. (Q) Dropping a fresh conservative extension fails at V-Const (Claude, 2026-10-30).**
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

## From the earlier abandoned mechanization (spec §15)


Leastness as gate, a gate that is not invariant under external steps, the
premise "distinct channels have distinct instants", term-level ∀-introduction,
and a window condition on all pending heads. Each is avoided by a design choice
recorded in §15.
