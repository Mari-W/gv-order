# Programs from the literature, typed natively

Four programs of the deadlock-freedom literature now have a derivation in this
system, written as the paper writes them. Before this, a literature program
reached the development only through the PGV or the Padovani–Novara
translation, so its order facts came from the translation's world and not from a
derivation anyone can read. Every program below is typed in the empty world
`Wpo []`, every channel comes from `new`, and every fact comes from the creation
constraint of a `new` or from the constraint of a box.

Two further files close gaps the audit found. `examples/Congruence.v` is the
first derivation that uses the congruences of ≡, and `examples/Rejected.v` turns
three rejection arguments that were comments into theorems.

## The programs

| Program | Source | Rocq file | Theorem | Result |
|---|---|---|---|---|
| Milner's cyclic scheduler, k = 3 agents with collectors | Dardha and Gay, Example 1 (dardha2018new p. 3), priorities on p. 9 | `examples/MilnerSched.v` | `ms_typed`, `ms_deadlock_free` | typed |
| recursive forwarder server | Kobayashi, Example 2 (kobayashi2006new p. 11) | `examples/KobForwarder.v` | `fwsrv_typed`, `fw_typed`, `fw_deadlock_free_kob` | typed |
| factorial server | Kobayashi (kobayashi2006new p. 2), Padovani (3) (padovani2014deadlock p. 2) | `examples/FactServer.v` | `fcsrv_typed`, `fc_typed`, `fc_deadlock_free` | typed |
| `stream` | Padovani (4) (padovani2014deadlock p. 2) | `examples/Stream.v` | `stprod_typed`, `stcons_typed`, `st_typed`, `st_deadlock_free` | typed |
| a box that needs both congruences of ≡ | ours | `examples/Congruence.v` | `cgbox_typed`, `cg_typed`, `cg_deadlock_free` | typed |
| reversed agent of the reduced scheduler | ours, after Dardha and Gay Example 1 | `examples/Rejected.v` | `sched_rev_underivable` | rejected, the facts close a cycle through the alias of `link` |
| reversed agent of the full scheduler | Dardha and Gay, Example 1 reversed (dardha2018new p. 3) | `examples/Rejected.v` | `ms_rev_underivable` | rejected, the three ring facts close a cycle |
| the bad `link` | ours | `examples/Rejected.v` | `badlink_underivable` | rejected, x ≡ y with x ≺ z ≺ y gives x ≺ x |
| `ordered` without its constraint | ours | `examples/Rejected.v` | `ord_no_constraint` | rejected, no fact between two distinct point variables |

`examples/LitTools.v` holds what the four literature files share. Program order
over a gap (`slt_po_lt`), the gate tactics, the chain of carried roots
`slotv` with the two strict orders `dlt` and `ult` on depth and offset, the two
creation-constraint wrappers `cc_ok_dlt` and `cc_ok_ult`, and `tv_case`, E-Case
for a linear scrutinee with Θ empty.

## Milner's cyclic scheduler

Dardha and Gay's Example 1 is k agents A_0 to A_{k-1} in a ring, each with a
spoke to its own collector P_i. A_0 starts the round on c_0, waits on d_0,
reports on a_0 and stops. Every other agent waits on d_i, reports on a_i and
passes the token on c_i. The ring closes because c_i and d_{(i+1) mod k} are the
two ends of one channel. `examples/Scheduler.v` had a reduced variant, three
agents, no collectors, and one agent replaced by `link`, and its comment called
it Milner's scheduler. That comment now says reduced variant and points here.

The new file takes k = 3, so six channels and six threads. All six channels sit
at the points of one root. The first `new` creates the ring channel of A_0 at a
fresh ι with the empty creation constraint, and `t_new_at` puts the other five at
ι+2, ι+4, ι+6, ι+8 and ι+10, which the hypothesis of the first `new` makes known.
Reading the two ends of a channel as one point,

```
c_0, d_1 : ι      a_1, b_1 : ι+2    c_1, d_2 : ι+4
a_2, b_2 : ι+6    c_2, d_0 : ι+8    a_0, b_0 : ι+10
```

and every fact the derivation needs is ι+j ≺ ι+k with j < k, which program order
gives. This is the order of Dardha and Gay's priority assignment for Sched
(dardha2018new p. 9). For k = 3 theirs reads d_1 at 0, a_1 at 1, c_1 at 2, d_2 at
2, a_2 at 3, c_2 at 4, d_0 at 4, a_0 at 5, with c_0 at the priority of d_1 and
b_i at that of a_i. Two of their priorities coincide for the two ends of one
channel, and one point here carries both ends.

## The three recursive servers

Kobayashi's forwarder, the factorial server and Padovani's `stream` share one
shape. A replicated channel serves requests, each round creates one fresh
channel, and the recursive call runs beside the rest of the round. The three
files differ in where the branch comes from and in which direction the order
runs.

A replicated input `*f?x.Q` becomes a box `!f. λx. Q` and an output `f!v` becomes
a spawned `(force f) v`. This is the correspondence static-system.md §8 records
for Padovani's shifting on replicated channels and for Kobayashi's schematic
tags, and it is what makes the point of each round an instance of the box's ∀.

The fresh channel of a round sits at ι.0, the first carried root of the channel
the round acts on, and `t_new_at` creates it there. The order facts between the
rounds then live in the box constraint, which speaks of ι alone and names no
outer point. In the forwarder and the factorial server nothing travels on ι, so
ι.0 holds no payload, the same use of a carried point that the ceiling of
`examples/TailCall.v` makes. In `stream` the fresh channel is the payload, so
ι.0 is where sender and receiver already name it alike.

The two directions.

```
forwarder, factorial    C = {ι.0ⁿ⁺¹ ≺ ι.0ⁿ, ι.0ⁿ⁺¹ + 1 ≺ ι.0ⁿ ∣ n ∈ ℕ}
stream                  C = {ι.0ⁿ + 1 ≺ ι.0ⁿ⁺¹ ∣ n ∈ ℕ}
```

A server that blocks on the answer of its own recursive call needs the fresh
channel strictly below the one it answers on, which is Kobayashi's r′ ≺ r
(kobayashi2006new p. 11) and Padovani's k < h (padovani2014deadlock p. 2). A
producer that sends the fresh channel on needs it strictly above, which is
Padovani's h < k. Both constraints are closed under the substitution ι ↦ ι.0, so
the recursive `force` reads C again one level deeper.

Neither constraint has a rank in ℕ. The depth grows without bound and the order
runs along it, in one direction for the servers and in the other for the
producer. `dlt` and `ult` of `examples/LitTools.v` read a point lexicographically
as its depth and its offset, once with the depth reversed and once not, and both
are irreflexive and transitive, which is all `cc_ok_inner` asks.

An alternative for the two servers is a creation constraint {κ + k ≺ ι} with the
box variable ι as an outer point. The chain of carried roots keeps every fact
inside one root, which is what the other examples in the empty world do, and it
needs no lemma for a hypothesis with outer points.

## Simplifications

Every program below loses the same two things, because the calculus has neither
integers nor replicated channels. The files state these in their headers.

| Program | Simplification |
|---|---|
| all four | a replicated input is a box and an output is a spawned `force` of it |
| all four | every integer is ∗, so a payload `int` becomes ∗ and a session carries ∗ |
| Milner's scheduler | the token n_i, the result m_i and the received x_i, y_i are ∗, and the message types are !∗.Close and ?∗.Close |
| Milner's scheduler | the continuation Q_i of a collector is ∗, so P_i reads the result and closes |
| Milner's scheduler | the program runs one round, as Dardha and Gay's does |
| forwarder | the free boolean b is the closed value inj₂ ∗ of ∗ ⊕ ∗, so the run always recurses while E-Case types both branches |
| forwarder | the answer `true` and the forwarded x are ∗, so the forward is a receive of ∗ and a send of ∗ |
| factorial server | n is a value of ∗ ⊕ ∗ and the test n = 0 is E-Case on it |
| factorial server | the recursive call passes inj₂ ∗ in place of n-1, so the run recurses for ever, as the mechanized Padovani–Novara `fibo` does |
| factorial server | the answers 1 and x*n are ∗ |
| `stream` | x is ∗ and the successor x+1 is ∗ again, so the payload is ∗ ⊗ α@κ |
| `stream` | Padovani's outputs do not block, so his (4) runs with no consumer. Ours is synchronous, so `stcons` reads the stream and closes each round |

Nothing was restructured to make a program type. The forwarder keeps Kobayashi's
receive and send, which `link` would collapse into one step, and `stream` keeps
Padovani's pair.

## The congruences of ≡

The fact theory closes ≡ under successor and under carried roots, `se_shift` and
`se_slot` of static-system.md §3. No example derived a fact by either rule.
`examples/Scheduler.v` needs c+1 ≡ a+1 from the alias c ≡ a that its `link`
asks for, and it derives that inside the world through the closure field
`wf_eq_shift`, then lifts it with `se_w`, so the static rule stays unused.
`examples/Forwarder.v` states its alias of carried roots fact by fact in a
constraint.

`examples/Congruence.v` is the smallest program we found whose derivation uses
both rules. Its box takes two point variables under one alias.

```
Scg = !⟨κ⟩(Close@κ).Close
C   = {ι ≡ ι′,  ι′ ≺ ι′.0}
cg : □(∀ι ι′. C. ∗ ⊸^⊥_⊤ ((Scg@ι ⊗ Close@ι′.0) ⊗ Close@(ι′+2) ⊸^{ι′+2}_{ι} ∗))
cg = !(f = λp. let (q, d) = p in let (c, e) = q in
              let (c, w) = ⟨send ⟨e, c⟩, ∗⟩ in let () = w in
              let () = close c in close d)
```

The payload of c at ι is Close@ι.0 and e is Close@ι′.0, so E-Conv moves e along
ι′.0 ≡ ι.0, which is `se_slot` of the alias. The close of c at ι+1 runs while the
frame holds d at ι′+2, so E-App asks ι+1 ≺ ι′+2, and the hypothesis states no
fact at ι+1. `se_shift` of the alias gives ι+1 ≡ ι′+1 and program order gives
ι′+1 ≺ ι′+2. The caller instantiates both variables by one point γ, where the
alias is reflexivity, and creates c with the constraint {γ ≺ γ.0, γ.0 ≺ γ+1}.

Neither rule is forced by any program. A derivation that uses `se_slot` at
x.j ≡ y.j may instead state that fact in the constraint it read x ≡ y from, and
the same holds for `se_shift` at x+1 ≡ y+1. The one restriction that could force
a congruence is conservativity, because a creation constraint may not state a
fact between two points that both lie outside the new channel. That fact then has
to come from the context, and the context is again a constraint or a world, which
may state it. So the congruences buy finiteness and not expressiveness. They let
one alias between base points stand for one alias per offset and per carried
root, and for an alias at every depth that is the difference between a finite
constraint and an infinite one.

## The rejections

Each rejection argument in the examples names the facts a derivation of the
program would have to supply. Three of them were comments. `examples/Rejected.v`
now proves that those facts do not hold together.

```
sched_rev_underivable   y ≺ x, z ≺ y and z ≡ x give z ≺ z
ms_rev_underivable      r_2 ≺ r_0, r_0 ≺ r_1 and r_1 ≺ r_2 give r_0 ≺ r_0
badlink_underivable     x ≡ y, x ≺ z and z ≺ y give x ≺ x
ord_no_constraint       under the empty constraint no fact relates ι and ι′
```

The first three are stated for any Γ whose ≺ has no cycle. Every Γ that a
derivation of a closed typable program meets is of that kind. `soundness` takes a
strict world, and every creation constraint is acyclic relative to the context it
is read in (`cc_acyclic`, types/Types.v), so a cycle in Γ + C is already a cycle
in Γ, and by induction in the world. `slt_acyclic_nil` discharges the hypothesis
for a Γ with no hypotheses.

`ord_no_constraint` is a model of the whole fact theory, in the style of
`rr_call_underivable` and `fb_between_underivable`. It sends ≺ to program order
on one name between points with a variable root and to the full relation between
points with a constant root, and ≡ to equality or to the pair of constant roots.
A well-formed world relates points with a variable root by program order only
(`wf_lt_supp`) and identifies them only when they are equal (`wf_eq_supp`), the
one hypothesis has no fact, and ι and ι′ have distinct names.

What stays a comment is the step from a program to the facts its derivation
forces. A theorem for that step means inverting typing derivations, and the
development avoids inversion. `examples/Rejected.v`, `examples/Scheduler.v`,
`examples/MilnerSched.v` and `examples/Ordered.v` each carry the argument for
their own program and point at the lemma.

## Assumptions

`Print Assumptions` reports "Closed under the global context" for `soundness`,
`soundness_source` and for each of

```
ms_typed                  ms_deadlock_free
fwsrv_typed               fw_typed            fw_deadlock_free_kob
fcsrv_typed               fc_typed            fc_deadlock_free
stprod_typed              stcons_typed        st_typed             st_deadlock_free
cgbox_typed               cg_typed            cg_deadlock_free
slt_acyclic_nil           sched_rev_underivable
ms_rev_underivable        badlink_underivable  ord_no_constraint
```

No typing rule was added and no existing statement changed. `examples/Scheduler.v`
and `examples/Ordered.v` changed one comment each, and `_CoqProject` lists the
five new files. Sharp edges 130 to 135 record the decisions.

## The world-free judgment, 2026-11-02

The five whole-program lemmas now state `styped`, the source judgment of
static/Source.v, which carries no world and no channel-constant context Θ.
`ms_typed`, `fw_typed`, `fc_typed`, `st_typed` and `cg_typed` read
`styped ∅ [] [] (∅, None) e TUnit`, the form the paper presents for a
self-contained source program. They were written before `styped` existed and
stated `typed W` under the premise `strict W`, which made them the only five
whole-program lemmas in examples/ out of step with the other twenty. Each
proof opens with `styped_Wpo` of examples/ExampleTools.v, poses
`Wpo_nil_strict'` and fixes `W := Wpo []`, so the derivation is still built
with the rules and tactics of `typed` and read back by `typed_styped`. No
tactic of any of the five bodies changed.

The component lemmas `fwsrv_typed`, `fcsrv_typed`, `stprod_typed`,
`stcons_typed` and `cgbox_typed` keep `typed` at an arbitrary world. A box is
a step inside a derivation, and the whole-program lemma that uses it converts
at its end. The five deadlock-freedom theorems keep their statements and reach
`soundness` through `ptyped_closed_s`, which composes `ptyped_closed` with
`styped_typed`. Sharp edge 136.
