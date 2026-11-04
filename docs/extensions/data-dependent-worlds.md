# Worlds that depend on data

State of 2026-11-04, branch claude/data-dependent-worlds-9rgdfr. Files:
theories/examples/DataBranch.v, theories/relation/BranchWorlds.v.

## Summary

The program that SHARP-EDGES 4 and C2 of docs/history/DESIGN-REVIEW.md
describe has a derivation. db_main b receives a bit b and closes two external
channels in an order that depends on b. It types for both bits, with no
top-level points ([db_typed], Rocq). The receiver puts an unsatisfiable fact
about the payload points of the receive on the side of the sum that the
sender does not use, and the branch on that side becomes dead code typed
under inconsistent hypotheses.

What does not type is the case node with a bit that carries no fact. With
z : ∗ ⊕ ∗, c : Close@x and d : Close@y, the node has no derivation under any
hypotheses that a strict world realizes ([db_component_unrealizable], Rocq,
proved through the logical relation). So one world per component is a limit
of components whose interface fixes a fact-free bit. I found no closed
program that fails for this reason, and section 3 says why such a program is
hard to build.

Of the candidates, pending choices with an owner (section 4.4) are the one to
pursue. They type the fact-free component when it owns the choice, they keep
the relation monotone, and their amalgamation lemma reduces to the existing
[wext_fresh_join] at every choice vector ([pjoin_fresh], [pjoin_valid], Rocq,
axiom free). An unguarded extension between existing points breaks
amalgamation ([unguarded_extensions_conflict], Rocq).

## 1 The program

```
db_main b =
  let (e, e′) = new ∗ in let (c, c′) = new ∗ in let (d, d′) = new ∗ in
  let () = spawn (λu. let () = u in close c′) in
  let () = spawn (λu. let () = u in close d′) in
  let () = spawn (λu. let () = u in close (send ⟨bit b, e′⟩)) in
  let (z, e) = recv e in let () = close e in
  case z of inl u ⇒ let () = u in let () = close c in close d
          | inr u ⇒ let () = u in let () = close d in close c
```

c sits at x, d at y and e at z. The inl branch closes c while it holds d and
asks x ≺ y. The inr branch asks y ≺ x. E-Case types both branches under one
Γ. Both runs are deadlock free. The closers of c′ and d′ are separate
threads, so each order of the main thread finds its partner.

Theorems of theories/examples/DataBranch.v, all closed under the global
context.

| Theorem | Statement |
|---|---|
| `db_typed b` | `styped ∅ [] [] (∅, None) (db_main b) TUnit` |
| `db_deadlock_free b` | `deadlock_free (∅, {[+ db_main b +]})`, from `soundness` |
| `db_component_unrealizable` | `styped Φ Ψ (db_ctx x y k) F db_case T → ¬ realizable Φ Ψ` |
| `db_component_untyped_top` | the same at the hypotheses `[(C0, ids n)]` of a source program |
| `df_keep` | `okb b e → deadlock_free (∅, {[+ keep b e +]}) → deadlock_free (∅, {[+ e +]})` |

db_case is the case node of db_main literally, and db_ctx x y k is the
context [db_typed_false] reaches it with, except that db_ctx types the bit
at ∗ ⊕ ∗. [df_keep] replaces every case by the case whose two branches are
the branch the run takes. It reflects deadlock freedom for a program that
never builds the other injection. It is a tool for programs whose dead branch
does not type. db_main does not need it.

## 2 Why db_main types

The receiver types the bit, for b = false, at

```
Tz = ∗ ⊕ ∃{z[0]+5 ≺ z[0]+1}.∗        e : ?Tz.Close@z   (payload of one point)
```

z[0] is the first payload point of the receive at z. The right side of Tz
has no value in a strict world. The sender sends inl ∗ and never needs it.
Four facts make the derivation work.

1. E-Open applies to ∃{…}.∗. Its premise asks the body not to be unlimited,
   and only boxes are unlimited (types/Types.v, `unlimited`). So the inr
   branch opens u and gains z[0]+5 ≺ z[0]+1.
2. A session payload type mentions only payload points. `pinst_ty` does not
   enter `TSess`, so Tz cannot name x or y. The fact is about z[0], and the
   creation constraints anchor c and d to it. c is created with
   {z+1, z[0]+1} ≺ ι ≺ {z[0]+5}, d with {z+1, x} ≺ ι ≺ {z[0]+5}.
3. Betweenness of E-NewFresh asks z+1 ≺ z[0]+5. The creation constraint of e
   states it, {ι+1 ≺ ι[0]+5}, and it is a creation constraint by
   `cc_ok_inner` with a rank that puts program order and the fact upwards.
4. The inr branch derives y ≺ z[0]+5 ≺ z[0]+1 ≺ x. The inl branch reads x ≺ y
   from the creation constraint of d. The receive asks z ≺ x and z ≺ y, the
   close of e asks z+1 ≺ x and z+1 ≺ y, all from the creation constraints.

For b = true the sides swap. d is created with {z+1, z[0]+1} ≺ ι ≺ {x, z[0]+5},
the live inr branch reads y ≺ x and the dead inl branch derives
x ≺ z[0]+5 ≺ z[0]+1 ≺ y.

The hypotheses of the dead branch are not realizable, and the soundness proof
needs no change. The logical relation reads a value of ∃{z[0]+5 ≺ z[0]+1}.∗
only in a world with that fact, and a strict world has none.

The trick generalizes to every branch whose other side is dead in every run
and whose payload, or a top-level point, offers an anchor that the creation
constraints of the ordered channels can refer to. A source program may start
with any number of top-level points under an acyclic C₀ (sharp edges 148), and
every hypothesis context contains them, so a closed program always has
anchors.

## 3 The limit that remains

[db_component_unrealizable] states the limit. A derivation of db_case at
db_ctx x y k gives, by `styped_typed`, `typed_sem_rules` and
`sem_rules_fundamental`, the node in E at every strict world W that realizes
Φ and Ψ under an instance σ. Both inl ∗ and inr ∗ lie in V⟦∗ ⊕ ∗⟧, with c and d
at σx and σy. Two β steps bring the node to `close c; close d`, which is stable
and offers c while it holds d, so `ready_t` asks σx ≺ σy in W. The other bit
asks σy ≺ σx. W is strict, which refutes both.

Two readings of the limit.

- Fixed interface. A component typed against an interface that types the
  bit at ∗ ⊕ ∗ does not type, whatever the hypotheses. This is the
  compositional statement. P-Connect composes components that agree on an
  interface, and a translation from a system whose session types carry no
  facts (GV, priority systems) fixes the payload at ∗ ⊕ ∗.
- Fixed session types. db_main with e : ?(∗ ⊕ ∗).Close does not type. The
  argument by hand. The context of the case node holds z, d and c and
  otherwise spent or unlimited entries. Its hypotheses are C₀ and the
  creation constraints of e, c and d, opened by E-Open on the results of new.
  No other E-Open applies on the path, because the only existential the path
  meets is the one of new, and u has type ∗. The hypotheses are realizable,
  by the world `wc0` and the fresh extensions `wext_cc` builds in the
  soundness proof. db_component_unrealizable then refutes the node. The
  inversion of a derivation of db_main down to its case node, through E-Weak,
  E-Conv, E-Open and E-Contract, is not mechanized, as for the programs of
  examples/Rejected.v.

A closed counterexample needs a branch that is live under both bits under
one hypothesis context, with a bit that carries no usable fact. Each live
branch then needs its order from the static facts, and the two orders form a
cycle. Every constant that becomes a bit is typed at a site that knows the
top-level points, and a case that builds a bit from another bit can pass the
facts along with E-Open and E-Pack. I did not find a closed program where
neither works. Conjecture. Every closed program whose only obstacle is the
order of a branch on data types, possibly with infinitely many top-level
points for recursion. A counterexample would be a recursion whose round k
needs an order that depends on data computed in round k from fact-free input
and that no box constraint can relate to the anchors.

## 4 Candidates

Each candidate is judged on the same points. The typing rules it changes.
The logical relation, in particular monotonicity (Monotonicity.v needs
[wext_fresh_join] at O-New and Q-Tau), amalgamation of two futures of one
world, and the conservative-extension assumption ⊑ₒ at new. The proofs that
break and why. Whether the fact-free component of section 3 becomes typable.

### 4.1 Branch-indexed worlds

A world becomes a family W_ρ indexed by the branch history ρ of a component,
and Γ becomes Γ_ρ. E-Case types branch i under Γ_{ρ·i}, which may add facts
between existing points. The relation reads readiness in W_ρ for the history
ρ the run took.

Monotonicity holds index by index. Amalgamation needs every combination of
the histories of two components to give a strict world, because component 1
may add x ≺ y in a branch while component 2 adds y ≺ x in one of its own. The
cross product grows with every branch of every component, and a recursion
makes it infinite. ⊑ₒ holds at every index. The fact-free component types,
with W_inl ∋ x ≺ y and W_inr ∋ y ≺ x, provided no other component can choose
an index that orders x and y. Nothing in the candidate says who may, so as
stated it is unsound for the composition of 4.2. Restricting who indexes
which facts gives 4.4.

### 4.2 Growth at internal choices, facts learned with the label

E-Case-Grow types branch i under Γ + Γ_i with Γ_i between existing points,
provided Γ + Γ_i is acyclic. The relation lets the β step of a case extend
the world by Γ_i, an extension that is not fresh. The receiver half exists
today. A payload ∃{Γ_i}.T_i on the i-th side of a sum gives the branch Γ_i
by E-Open, which is how db_main types. What is new is the chooser half. It
adds facts that do not hold yet.

Unguarded growth is unsound. K₁ holds c and d, K₂ holds their other ends, K₁
branches on its bit and closes c then d in branch inl, K₂ branches on its own
bit and closes d then c in branch inl. Each types with growth, x ≺ y in K₁ and
y ≺ x in K₂. With both bits inl the composition deadlocks. In the relation,
monotonicity fails at the growth step. The step extends W to W ∪ {x ≺ y}, a
future W′ of another component holds y ≺ x, and W ∪ {x ≺ y} ⊔ W′ has a cycle.
[unguarded_extensions_conflict] (BranchWorlds.v) checks this. Two extensions
of the world over {0, 1} with only program order, one adding (0,0) ≺ (1,0)
and one adding (1,0) ≺ (0,0), are both extensions and their join is not
strict. ⊑ₒ fails at the growth step by definition. The fact-free component
types, and so does the deadlocking composition. Growth needs an owner of the
decision, which gives 4.4.

### 4.3 A second composition rule that splits at extrusion

P-Split types a composition whose cut carries the bit by one derivation per
value the sender may send, each in its own world, and composes the outside
with the meet. The relation of the composite is a disjunction of relations
at the worlds W_v. Adequacy holds, because a run sends one value and stays in
one W_v. Monotonicity holds disjunct by disjunct. Composition with a third
component needs that component related at every W_v, so the outside sees only
the facts common to all W_v, and the rule has to know the values the sender
sends, which a component typed against an interface does not.

The rule types db_main without the dead fact of section 2, which closed
programs do not need. It does not type the fact-free component, whose sender
sits behind the interface. Its proofs touch only the process layer (PTerm,
PConnect, the adequacy chain), which is its one advantage.

### 4.4 Pending choices with an owner (recommended)

new creates, next to its creation constraint C, a list of pending choices
π : {Γ₀ | Γ₁}, alternatives that relate the fresh point to known points. The
creating thread owns π, as a ghost entry of Δ that moves like a channel end
through spawn and messages. E-Case-Resolve types branch i of a case under
Γ + Γ_i when Δ owns π, and consumes the ownership. A sender can resolve and
pack, so the receiver learns Γ_i with the label through the existing E-Open.
The creation check asks cc_ok for every choice vector of the pending choices
in scope, 2^k checks for k choices, each the existing cc_ok.

The world becomes a pending world (W, P). A choice vector ch picks a side of
every choice, `at_choice W P ch` is W with the picked facts, and (W, P) is
valid when every choice vector gives a strict world (`pvalid`). E of a thread
reads every choice vector of the choices it does not own and may resolve the
choices it owns at a β step. Resolution keeps validity ([resolve_valid]) and
is an extension, a choice vector ch′ of the result lying above <[i := b]> ch′
([resolve_pext]). A third component therefore stays related across a
resolution by plain monotonicity, choice vector by choice vector.

Amalgamation. A fresh extension that places new names and new pending choices,
fresh at every choice vector (`pfresh`), joined with any pending extension,
which may resolve old choices, is a fresh extension at every choice vector
([pjoin_fresh]) and a valid pending world ([pjoin_valid]). The proof applies
[wext_fresh_join] at the choice vector the extension lies above, so the hard
lemma of the current development carries over unchanged. ⊑ₒ becomes "fresh
at every choice vector". The two orders of db_main form one valid pending
choice ([db_pending_valid]).

Proofs that change. Worlds.v gains the definitions of BranchWorlds.v.
Creation.v has to build `pfresh` from cc_ok at every choice vector, which is
`wext_cc` once per vector. LogicalRelation.v and every file above it carry the
pending world and an ownership set in E and P. Monotonicity.v replaces
[wext_fresh_join] by [pjoin_fresh]. ConnectCut.v and PConnect.v split
ownership as they split channel ends. Adequacy resolves the remaining choices
arbitrarily at the end of a run, which validity keeps strict.

The fact-free component types when its context owns the choice between x ≺ y
and y ≺ x. Its interface then states the ownership, so
[db_component_unrealizable], whose context owns nothing, stays true. A
component that branches on a fact-free bit about points whose order another
component owns still does not type, and it should not, because the owner may
decide the other way.

Guarded facts and disjunctive Γ are this candidate under other names. A
disjunctive Γ without an owner is 4.2 and unsound, and a fact guarded by the
value of a variable is a choice owned by whoever cases on that variable.

### 4.5 Verdict

| Candidate | Fact-free component | Sound | Monotonicity, amalgamation | Cost |
|---|---|---|---|---|
| 4.1 branch-indexed worlds | types | only with owners (4.4) | per index, product of all histories | every file above Worlds.v, infinite index sets |
| 4.2 growth at choices | types | no (4.2) | fails ([unguarded_extensions_conflict]) | small, unsound |
| 4.3 split at extrusion | no | yes | per disjunct | process layer only |
| 4.4 pending choices with owner | types with ownership | yes, at the world level | [pjoin_fresh], [pjoin_valid] | every file above Worlds.v, 2^k creation checks |
| status quo, dead-side facts | no | yes | unchanged | none, but needs anchors and annotation |

4.4 is the one to pursue. It is 4.1 restricted to choices declared at new and
4.2 with an owner, it reuses the existing amalgamation lemma at every choice
vector, and its ownership is the discipline channel ends already follow.

## 5 Prototype

theories/relation/BranchWorlds.v, on top of relation/Worlds.v only. Every
theorem is closed under the global context.

| Theorem | Content |
|---|---|
| `resolve_valid` | resolving a choice keeps a pending world valid |
| `resolve_pext` | resolving is a pending extension |
| `pjoin_fresh` | a fresh extension with new choices, joined with a pending extension, is fresh at every choice vector |
| `pjoin_valid` | the join is a valid pending world |
| `unguarded_extensions_conflict` | two extensions between existing points have a join that is not strict |
| `db_pending_valid` | the two orders of db_main form a valid pending choice |

Not done. The relation with pending worlds and ownership, the typing rules,
and the creation check per choice vector. The prototype shows that the lemma
the monotonicity proof needs survives, which is the step 4.2 fails at.

## 6 Open problems

- The logical relation with ownership. E has to quantify over the choice
  vectors a thread does not own and let it pick the ones it owns. The
  interaction with O-Recv, which quantifies over every received value, is
  the step to check first. A value received at a payload ∃{Γ_i}.T may carry a
  resolution, and the receiver must not resolve again.
- Recursion. A box that creates a choice per round needs infinitely many
  pending choices. Choice vectors become functions, and `pvalid` asks
  strictness for each.
- The closed-program conjecture of section 3.
- Whether the dead-side facts of section 2 can be inferred. A checker would
  have to find the anchors and the unsatisfiable fact.
