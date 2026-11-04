# Report: worlds that depend on data

Branch claude/data-dependent-worlds-9rgdfr, started from main at b621661.
The design note is [data-dependent-worlds.md](data-dependent-worlds.md).

## Result in one paragraph

The program the task describes is not a counterexample. db_main b receives a
bit and closes two external channels in the order the bit picks, and it has a
source derivation for both bits with no top-level points (`db_typed`). The
receiver types the bit with an unsatisfiable fact about the payload points of
the receive on the side the sender does not use, E-Open makes the hypotheses
of the dead branch inconsistent, and the static creation constraints order
the live branch. The limit of one world per component is real for a component
whose interface fixes a fact-free bit. The case node with z : ∗ ⊕ ∗, and the
receive with e : ?(∗ ⊕ ∗).Close, have no derivation under any hypotheses a
strict world realizes (`db_component_unrealizable`, `db_rnode_unrealizable`,
proved through the logical relation). Facts on both sides of the bit do not
help as long as one world realizes both sides together with the hypotheses
(`db_component_sides`). A case node that runs every round with the live
branch alternating types (`alt_typed`). Section 3 of the note conjectures, in
both directions, that the closed programs that fail are those whose case node
runs once per round with an order pattern that is not eventually periodic.
Of the four candidates, pending choices with an owner (4.4 of the note) are
the one to pursue. Their world-level lemmas hold in Rocq (`resolve_valid`,
`resolve_pext`, `pfresh_new`, `pjoin_fresh`, `pjoin_valid`, `pcreate_join`,
`owned_resolutions_join`). Two components that resolve one choice in opposite
ways conflict (`unowned_resolutions_conflict`), which is why the owner is
needed. The logical relation with ownership is not built, so its
monotonicity is not proved.

## Files

| File | Content |
|---|---|
| theories/examples/DataBranch.v | the program, its derivation, the non-derivability theorems, the keep simulation |
| theories/examples/GrowDeadlock.v | the composition of note 4.2 is not deadlock free |
| theories/examples/DataAlternate.v | a case node that runs every round, both branches live, typed through a state that carries the alternating pattern |
| theories/relation/BranchWorlds.v | prototype of pending-choice worlds |
| docs/extensions/data-dependent-worlds.md | design note, candidates 4.1 to 4.4 |
| docs/extensions/data-dependent.md | one targeted edit in item 1 (Branches) pointing to the note |
| _CoqProject | the four new files registered |

No existing Rocq file, theorem statement or rule changed.

## Theorems

Every theorem below prints "Closed under the global context" under
`Print Assumptions`.

DataBranch.v

| Theorem | Statement |
|---|---|
| `db_typed` | `∀ b, styped ∅ [] [] (∅, None) (db_main b) TUnit` |
| `db_deadlock_free` | `∀ b, deadlock_free (∅, {[+ db_main b +]})`, from `soundness` |
| `db_component_unrealizable` | `styped Φ Ψ (db_ctx x y k) F db_case T → ¬ realizable Φ Ψ` |
| `db_component_untyped_top` | `creation_ok n nofact nofact (λ _, False) C0 → ¬ styped ∅ [(C0, ids n)] (db_ctx x y k) F db_case T` |
| `db_component_sides` | `styped Φ Ψ (db_ctx2 C1 C2 x y k) F db_case T → ¬ realizable2 Φ Ψ C1 C2`, the bit at ∃{C₁}.∗ ⊕ ∃{C₂}.∗ |
| `db_rnode_unrealizable` | `styped Φ Ψ (db_rctx x y z k) F db_rnode T → ¬ realizable Φ Ψ` |
| `db_rnode_untyped_top` | the same at `[(C0, ids n)]` |
| `db_main_shape` | db_main b is three lets of new, three spawns and db_rnode |
| `df_keep` | `okb b e → deadlock_free (∅, {[+ keep b e +]}) → deadlock_free (∅, {[+ e +]})` |

DataAlternate.v

| Theorem | Statement |
|---|---|
| `alt_typed` | `styped ∅ [] [] (∅, None) alt_main TUnit` |
| `alt_deadlock_free` | `deadlock_free (∅, {[+ alt_main +]})` |

alt_main runs a box K that sends on c and d every round in the order a state
bit says and flips the bit. The bit carries the alternating pattern from the
current round on, as facts relative to K's instance.

`realizable Φ Ψ` says that some strict world W and instance σ make every
hypothesis of Ψ hold and put every variable of Φ, the hypotheses on the
future, below some point set. `realizable2 Φ Ψ C1 C2` asks in addition that
C1 and C2 hold in W under σ. db_case is the case node of db_main, db_rnode its receive with everything
after it. db_ctx and db_rctx are the contexts the derivation of db_main gives
these nodes, with the bit, or e's payload, typed at ∗ ⊕ ∗.

BranchWorlds.v

| Theorem | Statement |
|---|---|
| `resolve_valid` | resolving a pending choice keeps a pending world valid |
| `resolve_pext` | resolving is a pending extension |
| `pfresh_new` | new with a pending choice that records the ≺ facts of two creation constraints is fresh at every choice vector, given cc_ok of each at every old choice vector |
| `pjoin_fresh` | at every choice vector, the join of the choice worlds of a fresh extension with new choices and of any pending extension is a fresh extension (reduces to `wext_fresh_join`) |
| `pjoin_valid` | the pending world of that join is valid |
| `pfresh_pext`, `pfresh_valid` | a creation with new choices is a pending extension and valid |
| `pcreate_join` | two creations from one pending world, each with new choices, join to a valid pending world |
| `unguarded_extensions_conflict` | there are two extensions that add opposite facts between existing points whose join is not strict |
| `unowned_resolutions_conflict` | resolving one choice to false and to true gives two extensions whose join is not strict |
| `owned_resolutions_join` | resolutions of two distinct choices join to a world strict at every choice vector |
| `db_pending_valid` | two orders of two points with no other facts form one valid pending choice |

GrowDeadlock.v

| Theorem | Statement |
|---|---|
| `grow_not_df` | `¬ deadlock_free grow_proc`, the two components of note 4.2 with both bits inl |

## What is by hand

The step from a derivation of db_main with e : ?(∗ ⊕ ∗).Close to a derivation
of db_rnode at db_rctx under realizable hypotheses. It inverts the derivation
through three lets of new and three spawns (`db_main_shape` fixes the term),
past E-Weak, E-Conv, E-Open and E-Contract. examples/Rejected.v leaves the
same step by hand for its programs. Section 3 of the note gives the argument.

## Build

Full build green with Rocq 9.2.0 and stdpp 1.13.0 (stdpp from the MPI-SWS
GitLab mirror, the GitHub archive was blocked by the proxy). Clean build from a
fresh clone, `make -j4`, exit 0, recorded in the final section.

## Verdict per candidate

| Candidate | Verdict |
|---|---|
| 4.1 branch-indexed worlds | types the fact-free component, unsound without an owner of each index, the index set is the product of all branch histories |
| 4.2 growth at internal choices, facts learned with the label | the receiver half exists today (payload ∃{Γᵢ}.T and E-Open, which is how db_main types). The chooser half without an owner is unsound. Two components that add opposite facts compose to a deadlock (`grow_not_df`), and the monotonicity step fails (`unguarded_extensions_conflict`) |
| 4.3 a second composition rule splitting at extrusion | argued sound, proof not attempted, lives in the process layer, types closed compositions, which already type, and not the fact-free component behind an interface |
| 4.4 pending choices with an owner, also guarded facts and disjunctive Γ | recommended. Would type the fact-free case node when it owns the choice (argued, rule not built). Amalgamation of creations and ⊑ₒ reduce to the existing lemmas at every choice vector, and resolutions of distinct owned choices join (prototype). Cost is an ownership discipline like channel ends and 2^k creation checks for k pending choices |

## Recommendation

Do not change the system for db_main. It types. Record in SHARP-EDGES 4 that
the limit concerns a case node whose interface fixes a fact-free bit, with
db_component_unrealizable and db_rnode_unrealizable as the statements, and
db_typed as the reason the closed program is not a counterexample. If
interfaces with fact-free bits matter (translations from GV or from priority
systems fix session types without facts), pursue pending choices with an
owner. The next step is the logical relation with ownership. Its first check
is O-Recv, which quantifies over every received value, against a resolution
that travels with a value.

I did not edit SHARP-EDGES.md. Other branches add numbered entries there, and
the revision of entry 4 is the author's decision. Proposed text, to replace
the body of entry 4.

> A component that acts on two external channels in an order chosen by a
> value it receives needs both orders, one per branch. In a closed program
> this types. The receiver gives the value a sum type whose side for the
> other branch carries an unsatisfiable fact about payload points, and E-Open
> makes the dead branch typable under inconsistent hypotheses
> (examples/DataBranch.v, db_typed). The case node of that program, with an
> interface that types the value at ∗ ⊕ ∗ or at a sum whose two sides one
> world realizes together with the hypotheses, has no derivation under
> realizable hypotheses (db_component_unrealizable, db_component_sides,
> db_rnode_unrealizable). A case node that runs every round with an
> alternating live branch types through a state that carries the pattern
> (examples/DataAlternate.v). Open problem. A pattern that is not eventually
> periodic (conjecture, docs/extensions/data-dependent-worlds.md).
> Witness: examples/DataBranch.v, db_component_unrealizable.
> Decision: deferred by the author (§14). Pending choices with an owner are
> the candidate extension (same file, section 4.4).

## Open problems

- The logical relation with pending worlds and ownership, and the typing
  rules E-Case-Resolve and creation with choices. Not started. Monotonicity
  of the relation under resolution needs ownership (`unowned_resolutions_conflict`,
  `owned_resolutions_join` give the world-level picture).
- Pending choices in recursion. A box that creates a choice per round needs
  infinitely many pending choices, and choice vectors become functions.
- The closed-program conjecture (section 3 of the note), in both directions.
  Closed programs fail only when a case node runs once per round with an
  order pattern that is not eventually periodic, and such a program with a
  recursive generator fails. The alternating pattern types (alt_typed).
  Periodic patterns fit in finitely many fact sets relative to a box
  instance, aperiodic ones do not. Neither direction is checked.
- Mechanizing the inversion from db_main to db_rnode.
- Inferring the dead-side facts and anchors of section 2 of the note.

## Final build record

Clean build of commit 1e1aab4 from a fresh clone, `rocq makefile` then
`make -j4` with `ulimit -s 1000000`. 118 files compiled, exit 0, no errors.
A `Print Assumptions` run over the 24 theorems listed above prints "Closed
under the global context" for each. The commit that adds this section
changes only this report.
