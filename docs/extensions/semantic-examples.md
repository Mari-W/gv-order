# Semantic components in syntactic programs

Branch `semantic-examples`, cut from `main` at d9fd5c0. Three new files,
`theories/static/Mixed.v`, `theories/examples/SemFlag.v` and
`theories/examples/SemRounds.v`, all registered in `_CoqProject`. No existing
file changed apart from the three `_CoqProject` lines. Every theorem below
prints "Closed under the global context" under `Print Assumptions`.

## 1 Composition

`Mixed.v` plugs semantically typed components into syntactically typed
programs. It has a process form and a term form.

The process form is the judgment `mptyped`. It has the rules of `ptyped` as one
leaf (`mp_syn`), a second leaf for any process in the logical relation at a prim
type (`mp_sem`), and P-Connect over mixed premises (`mp_connect`). A derivation
is a tree of cuts whose leaves are typed processes or semantic processes.

```
Theorem mptyped_sem W Σ p T : mptyped W Σ p T → strict W → sem_ptyped W Σ p T.
Corollary mixed_soundness W p T : strict W → mptyped W ∅ p T → deadlock_free p.
Lemma mp_sem_thread W Σ ΘB C0 t T :
  prim T → strict W → dom ΘB = C0 → dom Σ ## C0 →
  (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
  sem_typed W (tenv_of Σ ∪ ΘB) [] ∅ t T →
  mptyped W Σ (C0, {[+ t +]}) T.
```

`mptyped_sem` follows `fundamental_proc` line by line. A syntactic leaf goes
through `fundamental_proc`, a semantic leaf is its own premise, and a cut goes
through `Prel_connect` at the world W ⊔ W. `mp_sem_thread` is the semantic
counterpart of P-Term and comes from `Prel_term`.

The term form applies a syntactically typed function to a semantically typed
argument.

```
Theorem sem_plug W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :
  strict W →
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  typed W ∅ [] Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2)), None)
    e1 (TLolli ub lb T U) →
  sem_typed W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
  sem_typed W Θ Δ F (App e1 e2) U.
Corollary plug_soundness W e1 e2 ub lb T U :
  strict W → prim U → ub_below W ub ∅ →
  typed W ∅ [] ∅ [] (∅, None) e1 (TLolli ub lb T U) →
  sem_typed W ∅ [] (opt_heads lb) e2 T →
  deadlock_free (∅, {[+ App e1 e2 +]}).
```

`sem_plug` is `fundamental` followed by `sem_typed_app`. The running example
uses the process form, because its component holds channels that the rest of
the program creates.

## 2 The running example

`SemFlag.v` builds a thread that computes its own flag and orders two channels
by it.

```
not = λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w
sf  = case not (inj₂ ∗) of inl _ ⇒ close c; close d
                         | inr _ ⇒ close d; close c
```

The flag is always inj₁ ∗, so every run closes c first. Both arms discard their
payload. In the file the component is `sf_body i j`, with c at variable i and d
at variable j.

### 2.1 The static system rejects it

```
Theorem sf_underivable Φ Ψ Δ F T i j s1 x s2 y :
  (∀ p, ¬ hlt Ψ p p) → plain Δ →
  Δ !! i = Some (Some (TSess s1 x)) → Δ !! j = Some (Some (TSess s2 y)) → i ≠ j →
  ¬ styped Φ Ψ Δ F (sf_body i j) T.
Corollary sf_underivable_top n C Φ Δ F T i j s1 x s2 y :
  c0_acyclic n C → plain Δ →
  Δ !! i = Some (Some (TSess s1 x)) → Δ !! j = Some (Some (TSess s2 y)) → i ≠ j →
  ¬ styped Φ [(C, ids n)] Δ F (sf_body i j) T.
```

The proof inverts the derivation in the style of `ChoiceNegative.v`. E-Case
types both arms under one Ψ. Relevance (`typed_term_wf_s`) puts c and d into the
context of the arms, because the flag has no free variable. An arm that never
mentions its payload can bind it only at an unlimited type, which is a box. A
box has nothing to open, so E-Open adds no fact in either arm. The arm contexts
then hold sessions and boxes only (`plainb`). In such a context E-Weak drops
boxes, E-Contract duplicates the head box and shifts every index by one, and
E-Conv and E-Pack change only the type. Three inversion lemmas follow these
four rules down to the closes (`konst_inv`, `var_inv`, `kv_inv`), and `arm_inv`
reads the upper point of the first close against the head of the second
channel. The first arm gives x ≺ y in Ψ, the second gives y ≺ x, and the order
of Ψ is irreflexive.

The payload matters. `DataBranch.v` (`db_typed`) types a branch on a received
bit whose arms consume the payload with `let ∗ = u`. There the dead side of the
bit carries an existential with an unsatisfiable fact, and E-Open in the dead
arm supplies the reverse order. A discarded payload is a box, and the trick has
no existential to open. I did not build a derivation for the variant of
`sf_body` whose arms consume the payload.

### 2.2 The logical relation accepts it

```
Lemma sem_typed_det_beta W Θ Δ F e e' T :
  (∀ γ, det_beta (subst γ e) (subst γ e')) →
  sem_typed W Θ Δ F e' T → sem_typed W Θ Δ F e T.
Theorem sf_sem_typed W x y :
  strict W → w_lt W x y → sem_typed W ∅ (sf_ctx x y) ∅ (sf_body 0 1) TUnit.
Theorem sf_thread_sem W x y :
  strict W → w_lt W x y → sem_typed W (db_Θ x y) [] ∅ sf_thread TUnit.
```

`sf_ctx x y` is c : Close@x, d : Close@y. `det_beta e e'` says that e takes a β
step to e' and takes no other step. `sem_typed_det_beta` comes from
`Erel_det_beta`. The proof of `sf_sem_typed` takes the 3 β steps of the flag
and of the outer case and lands in the first arm. The static system types that
arm in every world with x ≺ y (`sf_arm_typed`), and `fundamental` finishes.
`sf_thread_sem` is the same thread with c and d as channel constants, obtained
from `sf_sem_typed` by the grounding c ↦ "c", d ↦ "d" (`sf_ground`).

### 2.3 Deadlock freedom by composition

```
Lemma cc2_typed W x y :
  world_wf W → w_lt W x y → typed W ∅ [] (db_Θ x y) [] (∅, None) (cc2 chc chd) TUnit.
Theorem sf_mixed W x y : strict W → w_lt W x y → mptyped W ∅ sf_config TUnit.
Theorem sf_deadlock_free : deadlock_free sf_config.
```

`sf_config` is `({[chc; chd]}, {[+ sf_thread; cc2 chc chd +]})`, the thread and
a partner `close c; close d` on the other ends. The partner is typed by the
static system (`cc2_typed`) and enters through `mp_syn` and P-Term. The thread
enters through `mp_sem_thread` and `sf_thread_sem`. One `mp_connect` joins them
over the cut {c, d}. `sf_deadlock_free` applies `mixed_soundness` in the world
`sf_W`, which has the constants 0 and 1 and the one fact (0, 0) ≺ (1, 0). No
run of the configuration is explored.

## 3 An order pattern that is not eventually periodic

`SemRounds.v` runs a recursive component through infinitely many rounds. The
box K sends one unit on c and one on d per round, with c, d : μα.!∗.α. Its state
is a pair (i, j) of unary numerals. A round with i = 0 sends on d first and
moves to (j+1, 0). A round with i = i'+1 sends on c first and moves to
(i', j+1). From (0, 0) the rounds that send on d first are 0, 2, 5, 9, 14, and
the gap grows by one each time.

```
Theorem rdfirst_not_periodic p N : 0 < p → ∃ k, N ≤ k ∧ rdfirst k ≠ rdfirst (k + p).
Lemma rW_strict : strict rW.
Theorem rthread_Erel n : ∀ W k a b c d s1 s2 xk yk Θ,
  wext rW W → rst k = (a, b) → seq s1 Sb → seq s2 Sb →
  w_eq W xk (px k) → w_eq W yk (py k) →
  tenv_comp (w_eq W) Θ {[c := One (s1, xk)]} {[d := One (s2, yk)]} →
  Erel n W Θ TUnit ∅ (rthread a b c d).
Theorem rthr_sem : sem_typed rW rΘ [] ∅ rthr TUnit.
Lemma rrecv_typed W c a :
  world_wf W → pt_known W (Pt (NConst a) 0) →
  typed W ∅ [] {[c := One (Sa, Pt (NConst a) 0)]} [] (∅, None) (rrecv c) TUnit.
Theorem rounds_mixed : mptyped rW ∅ rconfig TUnit.
Theorem rounds_deadlock_free : deadlock_free rconfig.
```

`rst k` is the state of round k and `rdfirst k` says that round k sends on d
first. The world `rW` puts c at the points (0, k) and d at (1, k). A round that
sends on c first gets (0, k) ≺ (1, k) ≺ (0, k+1), a round that sends on d first
gets (1, k) ≺ (0, k) ≺ (1, k+1). A rank that places the first send of round k
at 2k and the second at 2k+1 proves it strict.

`rthread_Erel` is the semantic typing through the recursion. It is an
induction on the step index, for every round, every state and every world
above `rW`. The first β step of a round lowers the index, 4 more β steps reach
the case on i (`rthread_head`), and `Erel_round` runs the two sends through
`Erel_bind` with the readiness facts of the round. The recursive call then
lies at a lower index and the induction hypothesis applies. `rthr_sem` is round
0 with c and d as channel constants.

`rconfig` is the thread with two receivers, `alt_R` of `DataAlternate.v`
forced at c and at d. The receivers are typed by the static system
(`rrecv_typed`), and two `mp_connect` steps join the three threads.
`rounds_deadlock_free` applies `mixed_soundness`.

What stays open is the static half. The claim that no derivation types K at a
type that serves this thread is the conjecture of
docs/extensions/data-dependent-worlds.md §3, here for the triangular numbers in
place of the powers of two. I did not prove it. `SemFlag.v` proves rejection
for the one-shot component only.

## 4 Build

A clean build of the branch with `make -j$(nproc)` and `ulimit -s 1000000`
finishes with exit code 0. The `Print Assumptions` check ran on the 21 theorems
above in two separate files outside the repository. `CheckAll.v` is unchanged.
`scripts/gen-checkall.py` would pick up the theorems of `SemFlag.v` and
`SemRounds.v` that match its name filter when rerun. It does not list
`Mixed.v`.
