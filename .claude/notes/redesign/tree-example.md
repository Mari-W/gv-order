# A tree of three threads (internal proof)

File: `v2/examples/TreeTopo.v`, logical names under `GV.examples.TreeTopo`. It
imports `GV.examples.SemBranch` for the strictness lemma, the β-step lemmas
and the middle thread.

## The program

```
mid = case (λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w) (inj₂ ()) of
        inl _ ⇒ let () = close c in close d
      | inr _ ⇒ let () = close d in close c
A   = close c̄
B   = close d̄
```

The process is `({c, d}, {mid, A, B})`. The thread `mid` holds c at x and d at
y, `A` holds c̄ at x̄, `B` holds d̄ at ȳ. The channel graph is the path
A - mid - B. The flag always evaluates to `inj₁ ()`, so `mid` closes c first.
The gates are x ≺ ȳ for the live arm of `mid` and y ≺ x̄ for its dead arm. The
leaves hold no other end and need no fact.

## Static verdict

The static system accepts this program. I looked for a tree program it
rejects and found none, and the reason is general. A fact has the form
u ≺ v̄, where u is the point of the end being closed or used and v the point of
an end the same thread holds. A chain of facts continues from the right side
v̄ only at a thread that holds the dual end at v̄, so it moves to the other
endpoint of that channel. In a tree the chain then moves away from the thread
where it started and cannot return. A single thread alone adds no cycle,
because its facts have unbarred points on the left and barred points on the
right, and the only steps between them are shifts that raise the offset.

For `mid` the claim is checked in Rocq. `Wd` holds both x ≺ ȳ and y ≺ x̄ and
`tt_dead_world_strict` proves it strict by the potential
10·offset + (0 for a positive point, 1 for a negative one). E-Case then types
both arms under `Wd`, the leaves need no fact, and `strict (Wd ⊔ …)` holds
for the join. The derivation itself is not written in Rocq. The verdict is
this argument plus the strictness lemma.

This differs from SemBranch, where one partner holds both c̄ and d̄ and its
fact x̄ ≺ y closes the cycle. A tree cannot give one partner both ends, so
the cycle disappears. The program is a plain tree program.

## Theorems

```
Theorem tt_deadlock_free : deadlock_free tt_config.
Theorem tt_dead_world_strict : strict Wd.
```

`tt_config` is `({c, d}, ({[+ mid +]} ⊎ {[+ A +]}) ⊎ {[+ B +]})`. `Print
Assumptions` reports both closed under the global context. The file has no
`Admitted`. Build status, `make examples/TreeTopo.vo` succeeds.

## How the proof goes

1. `mid` is in E by `sb_thread_E` of SemBranch. Three deterministic β steps
   (`Erel_det`, `det_beta_case`, `det_beta_app`, `det_beta_inr`,
   `det_beta_inl`) reach the live arm, and the fundamental theorem types only
   that arm at x ≺ ȳ. The dead arm is never read.
2. The leaves `EClose (Chan o)` are typed in `dftyped` by `leaf_typed` and put
   in E with the fundamental theorem (`leaf_E`, through `typed_E_df`). This is
   the one use of the fundamental theorem outside the live arm, for a term
   with a single `close`.
3. `sem_p_term` makes each thread a process (`mid_P`, `a_P`, `b_P`, with
   `leaf_P` and `sth_leaf` for the side condition). All three live in the
   world `Wa` of SemBranch, which holds x ≺ ȳ.
4. `sem_p_connect` joins `mid` and `A` over the cut `Sc = {c⁺}` with `Sd = {d⁺}`
   open (`conn_c`). It joins the result and `B` over the cut `Sd` (`conn_d`).
   The restricted set of the first composite is {c}, and the second connect
   adds {d}.
5. `adequacy` needs `strict ((Wa ⊔ Wa) ⊔ Wa)`. `Wtt_strict` proves it with
   `strict_rank` of SemBranch.

## What was hard

- The cut of the second connect is the open end of the first. `mid` is typed
  over `ΣC = Sd ∪ Sc` in SemBranch's order `Sc ∪ Sd`, so `ΣC_split` commutes the
  union. The composite lands over `Sd ∪ ∅` and is rewritten to `∅ ∪ Sd`.
- The restricted channel set accumulates as `∅ ∪ ∅ ∪ {c}` and then
  `… ∪ {d}`. The final equality with `{c} ∪ {d}` is by `set_solver` after the
  unit rewrites.
- The step of the potential argument needs `pt_pol` to survive `pt_shift` and
  flip under `pt_dual`. `simpl` and a case split on the polarity close it.
- The step 3 direct proof by case analysis over the configurations is not
  done.

## Proposed entry for the Examples tab

Title: Three threads in a tree

Summary: A middle thread with a data-dependent close order sits between two
leaves, and the tree shape alone makes the process deadlock free.

Explanation: The middle thread closes c then d in the live arm and d then c in
the dead arm. The leaves each close their single end. The channel graph is a
path, so no chain of facts can return to its start and one world holds
x ≺ ȳ and y ≺ x̄ without a cycle. The static system accepts the process. The
relation proof does not need that. It runs three β steps in the middle thread,
types only the live arm, makes each of the three threads a process and
connects them over c and then d. Adequacy applies because the joined world is
strict.

Code:

```
mid = case (λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w) (inj₂ ()) of
        inl _ ⇒ let () = close c in close d
      | inr _ ⇒ let () = close d in close c
A   = close c̄
B   = close d̄
```

Rocq names: `tt_mid`, `tt_a`, `tt_b`, `tt_config` (program),
`tt_deadlock_free` (main theorem), `tt_dead_world_strict`, `Wd` (static world),
`Wtt_strict` (join), `mid_P`, `a_P`, `b_P` (threads as processes), `conn_c`,
`conn_d` (connections), `leaf_E`, `leaf_typed` (leaves). All in
`v2/examples/TreeTopo.v`, with `sb_thread_E` and `strict_rank` from
`v2/examples/SemBranch.v`.
