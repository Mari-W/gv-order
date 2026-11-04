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
proved through the logical relation). A closed program that fails needs a
case node that runs once per round with an order pattern that is not
eventually periodic (conjecture, section 3 of the note). Of the four candidates,
pending choices with an owner are the one to pursue, and the world-level
lemmas the relation needs from them hold in Rocq (`resolve_valid`,
`resolve_pext`, `pfresh_new`, `pjoin_fresh`, `pjoin_valid`).

## Files

| File | Content |
|---|---|
| theories/examples/DataBranch.v | the program, its derivation, the two non-derivability theorems, the keep simulation |
| theories/examples/DataAlternate.v | a case node that runs every round, both branches live, typed through a state that carries the alternating pattern |
| theories/relation/BranchWorlds.v | prototype of pending-choice worlds |
| docs/extensions/data-dependent-worlds.md | design note, candidates (a) to (d) and more |
| docs/extensions/data-dependent.md | one targeted edit in item 1 (Branches) pointing to the note |
| _CoqProject | the two new files registered |

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
future, below some point set.
db_case is the case node of db_main, db_rnode its receive with everything
after it. db_ctx and db_rctx are the contexts the derivation of db_main gives
these nodes, with the bit, or e's payload, typed at ∗ ⊕ ∗.

BranchWorlds.v

| Theorem | Statement |
|---|---|
| `resolve_valid` | resolving a pending choice keeps a pending world valid |
| `resolve_pext` | resolving is a pending extension |
| `pfresh_new` | new with a pending choice between two ≺-only creation constraints is fresh at every choice vector, given cc_ok of each at every old choice vector |
| `pjoin_fresh` | a fresh extension with new choices, joined with any pending extension, is fresh at every choice vector (reduces to `wext_fresh_join`) |
| `pjoin_valid` | that join is a valid pending world |
| `pfresh_pext`, `pfresh_valid` | a creation with new choices is a pending extension and valid |
| `pcreate_join` | two creations from one pending world, each with new choices, join to a valid pending world |
| `unguarded_extensions_conflict` | two extensions that add opposite facts between existing points have a join that is not strict |
| `db_pending_valid` | the two orders of db_main form one valid pending choice |

## What is by hand

The step from a derivation of db_main with e : ?(∗ ⊕ ∗).Close to a derivation
of db_rnode at db_rctx under realizable hypotheses. It inverts the derivation
through three lets of new and three spawns (`db_main_shape` fixes the term),
past E-Weak, E-Conv, E-Open and E-Contract. examples/Rejected.v leaves the
same step by hand for its programs. Section 3 of the note gives the argument.

## Build

Full build green with Rocq 9.2.0 and stdpp 1.13.0 (stdpp from the MPI-SWS
GitLab mirror, the GitHub archive was blocked by the proxy). The final clean
build from a fresh clone is recorded at the end of this report.

## Verdict per candidate

| Candidate | Verdict |
|---|---|
| (a) branch-indexed worlds | types the fact-free component, unsound without an owner of each index, the index set is the product of all branch histories |
| (b) growth at internal choices, facts learned with the label | the receiver half exists today (payload ∃{Γᵢ}.T and E-Open, which is how db_main types). The chooser half without an owner is unsound. Two components that add opposite facts compose to a deadlock, and the monotonicity step fails (`unguarded_extensions_conflict`) |
| (c) a second composition rule splitting at extrusion | sound, touches only the process layer, types closed compositions, which already type, and not the fact-free component behind an interface |
| (d) pending choices with an owner, also guarded facts and disjunctive Γ | recommended. Types the fact-free component when it owns the choice. Amalgamation and ⊑ₒ reduce to the existing lemmas at every choice vector (prototype). Cost is an ownership discipline like channel ends and 2^k creation checks for k pending choices |

## Recommendation

Do not change the system for db_main. It types. Record in SHARP-EDGES 4 that
the limit concerns components whose interface fixes a fact-free bit, with
db_component_unrealizable and db_rnode_unrealizable as the statements, and
db_typed as the reason the closed program is not a counterexample. If
interfaces with fact-free bits matter (translations from GV or from priority
systems fix session types without facts), pursue pending choices with an
owner. The next step is the logical relation with ownership. Its first check
is O-Recv, which quantifies over every received value, against a resolution
that travels with a value.

I did not edit SHARP-EDGES.md. Other branches add numbered entries there, and
the revision of entry 4 is the author's decision.

## Open problems

- The logical relation with pending worlds and ownership, and the typing
  rules E-Case-Resolve and creation with choices. Not started.
- Pending choices in recursion. A box that creates a choice per round needs
  infinitely many pending choices, and choice vectors become functions.
- The closed-program conjecture (section 3 of the note). A closed program
  fails only when a case node runs once per round with an order pattern that
  is not eventually periodic. The alternating pattern types (alt_typed).
  Periodic patterns fit in finitely many fact sets relative to a box
  instance, aperiodic ones do not. The general claim is not checked.
- Mechanizing the inversion from db_main to db_rnode.
- Inferring the dead-side facts and anchors of section 2 of the note.
