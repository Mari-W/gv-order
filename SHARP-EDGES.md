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

**18. (A) Process-level new did not extend the world.**
The thread's world grows at new, the process world did not, so a thread that
creates a channel and sends it failed at process level.
Decision: Q-Tau may grow the world (entry 21).

**19. (B) An internal link renames a visible channel.**
After P-Act-Link removing c, the environment talks over d, and the world knows
nothing about d. The paper got this for free from invariance under channel
substitution, which fails once names carry order facts.
Decision: an internal link must make c and d aliases. The step may create the
alias (entry 21).

**20. (C) Worlds lacked slot congruence, and old names could carry stale facts.**
x ≡ y did not give x[i] ≡ y[i], so renaming along an alias failed. A channel
arriving under a name the world already knows would inherit old facts.
Decision: slot congruence is a world law, and received channels must be unknown
to W except returning ones (§5, §7).

**21. One Q-Tau instead of special rules.**
The world may grow during a τ step, but only invisibly, so nothing changes
between names the environment can see. The invisible names are those
restricted before or after the step, so a link removing d can still create the
alias. The step is checked only when its restricted channels are disjoint from
the interface, the paper's implicit convention made explicit (§7, lemma
"invisible extension" in §10).

**22. Adequacy needs a renaming lemma for the LTS.**
Q-Tau only checks runs whose fresh names are unknown to W. Other runs are
renamings of checked runs (Swap.v, §10, §12).

**23. (D) The environment's world can mention restricted names.**
Q-Recv quantifies over every larger world, and such a world may state facts
about names the process restricts. Witness: a component placed its internal r
for a later send, and the environment's world contradicts that placement.
Independence and P-monotonicity fail.
Decision: restricted names are bound. V, E and P are invariant under renaming
channel names, worlds and types included (Equivariance.v, §10).

**24. (E) Renaming alone does not repair it.**
Renaming moves the stale fact onto the new name, and Q-Recv demanded the exact
successor.
Decision: Q-Recv's continuation holds for some α-variant of the successor,
renaming only its restricted names (§7).

**25. P is monotone in the world only up to renaming.**
A larger world may mention restricted names. V and E are monotone, given a
well-formed world (§10).

**26. Deciding strictness of W_G.**
Uniform schemas fall under Kosaraju and Sullivan's zero-cycle algorithm. Facts
with a counter on one side only need a free-coordinate extension, which we
believe decidable but have to prove. Uniformity is not a restriction, because
the static system produces only equal or independent counters (§12).

**27. (F) Renaming private names must not touch types.**
P-Connect renames the private names of the component that does not receive,
and renaming acts on every channel name, including names a type mentions. If a
fresh name appears in a session type of Σ or in the process type, the renamed
process no longer fits the same interface. No semantic counterexample, only an
obstruction to the proof.
Decision (F2): types never mention channel names. Points in types are bound
variables, point constants and slots of those. Channels appear only in worlds
and environments, and types reach them through aliases (§4, §7).

**28. P is not monotone in the world, even up to renaming.**
A larger world can state stale facts about a restricted name, and renaming
only moves the needed facts onto the new name.
Decision: stated only for extensions that touch no restricted name. P-Connect
keeps one world per component and does not need more (§10).

**29. (G) link substitutes in the whole soup.**
P-Act-Link writes [d/c] into every thread, also into the other component's.
A junk occurrence of c there would merge with a live channel.
Decision (G2): port the paper's junk-collapse lemma (Junk.v) to worlds, so the
composition lemmas need no tightness premise (§10).

**30. Internal links: α-closure instead of an alias; the paper's junk argument works again.**
With an alias obligation on internal τ links (an external c linked to a restricted d), junk
collapse is false: ({d}, {link⟨x,d⟩, (λy.∗) d, close b}) is related in a world with
(b,0) ≺ (d,0), because its link names the junk x and owes nothing, but renaming x to b gives
link⟨b,d⟩ with b external, which owes b@0 ≡ d@j, impossible above that fact.
Decision: restricted names are bound in every step obligation (each Q-clause holds for some
α-variant of the successor). A link between a cut channel c and a component's restricted d
can remove c or d, and the two successors differ by the transposition (c d), so the
composite's step reduces to the component's own step and needs no alias. The alias stays on
O-Link and Q-Link. The freshness guard at new is subsumed (§7, §10).

**31. (I) Which names may an α-variant introduce?**
If an α-variant may rename a restricted name to any name absent from the
process, it can pick an interface name or a name the world has facts about.
The junk transport then cannot reuse the variant after renaming, and moving
the world would need an unproved monotonicity.
Decision (I1, taken by Claude under the author's delegation): α-variants are
capture-avoiding, renaming only to names outside the interface and unknown to
the step's world. The paper's freshness convention with the world in scope (§7).

**32. (J) Fresh for which world?**
I1 required the names an α-variant introduces to be unknown to the world after
the step. At new that is impossible: the created channel must carry facts in
the new world, so it can never be renamed away from a name with stale facts,
and P-Term fails (witness: new picks a name with a conflicting stale fact and
then sends it).
Decision (J1, Claude, delegated): fresh for the world before the step, in
every clause. The created channel is renamed to a fresh name first and placed
by the step (§7).

**33. (K) Fresh for the environment's world at a receive.**
After J1, a Q-Recv α-variant could introduce a name fresh for W but known to
the environment's world W″, which carries the environment's stale facts. The
junk transport cannot replace such a witness.
Decision (K1, Claude, delegated): at Q-Recv, names are fresh for W″. Together
with I1 and J1 the rule is "fresh for every fact the process did not add
itself" (§7).

**34. (L) The junk target can become restricted later.**
In P-Connect the junk target b is a live cut channel, which can later move
into comp2 and become restricted. A junk redex link⟨x, r⟩ in the original
then becomes link⟨b, r⟩ with both names restricted and known to the world, and
the two link orientations differ by a transposition of two world-known names,
which neither an α-step nor an invisible world move bridges.
Decision (Claude, delegated): semantic ownership in Q-Tau. An internal step may
only act on owned or restricted channels, so the original never executes a link
on junk, and neither does the renamed process. Rejected: building tightness
(fchans ⊆ dom Σ ∪ C) into E and P, because it is syntactic (§7).

**35. Link as a forwarder (author's decision).**
Entries 19 (B), 29 (G), 30, 31 (I), 32 (J), 33 (K) and 34 (L) all came from one
cause: P-Act-Link substitutes a channel name in the whole soup, and with names
carrying order facts every substitution needs an argument (aliases, junk,
orientation, α-freshness). Decision: link ⟨c, d⟩ becomes a forwarder thread
that relays messages, with no substitution anywhere in the LTS. The link-only
machinery is undone (renaming along an alias, junk collapse, internalizing a
link, α-closure of every clause, I1/J1/K1, ownership). A self-link still
releases the channel. Reduction semantics and Harmony change (§3, §7, §10).

**36. (M) An untyped forwarder is not in E.**
E asks every label for its clause. An untyped fwd c d can fire c?v while c has
type !P.S, and O-Recv then has no head to consume, so fwd c d ∉ E for every S
other than Close, although no well-typed partner ever fires that label.
Decision (M1, Claude, delegated): the forwarder follows the session type.
link carries its type S, filled in by typing (surface syntax unchanged), and
link_S ⟨c, d⟩ —β→ fwd_S c d reads only on the receiving side. E, P and the
O-clauses stay as they are. Rejected M2 (no obligation for labels of the wrong
kind), because it changes E and P and endangers the chain arguments (§2, §7).

## From the earlier abandoned mechanization (spec §15)

Leastness as gate, a gate that is not invariant under external steps, the
premise "distinct channels have distinct instants", term-level ∀-introduction,
and a window condition on all pending heads. Each is avoided by a design choice
recorded in §15.
