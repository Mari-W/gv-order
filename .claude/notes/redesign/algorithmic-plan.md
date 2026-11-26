# Algorithmic typing, a plan

## 2026-11-26. The algorithmic system in Rocq, final state

Branch algorithmic, theories/algorithmic. No change to `typed`, the relation or
any existing statement. No admit, no axiom. `make`, `make check` and
`make test` pass, and the main theorems are in CheckAll.v.

### Files

| file | content |
|---|---|
| Annot.v | annotated terms `aexpr`, `erase`, the split by occurrence `tpart` and `lpart`, weakening lemmas, `box_inst` |
| Algo.v | the judgments `syn` (synthesis) and `chk` (checking), mutually inductive |
| Sound.v | `algo_sound`, and `box_body_all` (one instance of a box body gives all) |
| Complete.v | `algo_complete`, `algo_complete_at`, `algo_iff`, `algo_iff_df` |
| Oracles.v | the oracle classes, decidable equality of types, `tsub_dec` and the other derived decision procedures |
| Decide.v | the function `alg`, `alg_sound`, `alg_complete`, `syn_dec`, `chk_dec`, `syn_det`, `chk_det`, `typed_annot_dec` |
| .claude/notes/redesign/algorithmic-map.py | writes the map section `algorithmic` |

### Statements

    algo_sound W N :
      (∀ Θ Γ Δ F t T c, syn W N Θ Γ Δ F t T c → typed W N Θ Γ Δ F (erase t) T c) ∧
      (∀ Θ Γ Δ F t T c, chk W N Θ Γ Δ F t T c → typed W N Θ Γ Δ F (erase t) T c)

    algo_complete W N Θ Γ Δ F e T c :
      typed W N Θ Γ Δ F e T c → tenv_contr Θ →
      ∀ Δ', lenv_wk Δ Δ' → lenv_contr Δ' →
      ∃ t, erase t = e ∧ syn W N Θ Γ Δ' F t T c

    algo_iff W N Θ Γ Δ F e T c : tenv_contr Θ → lenv_contr Δ →
      typed W N Θ Γ Δ F e T c ↔ ∃ t, erase t = e ∧ syn W N Θ Γ Δ F t T c

    algo_iff_df W Θ Γ Δ F e T : tenv_contr Θ → lenv_contr Δ →
      dftyped W Θ Γ Δ F e T ↔
      ∃ t, erase t = e ∧ syn W None (tenv_df Θ) Γ (lenv_df Δ) F t (ty_df T) None

    alg_sound t (under the oracles) :
      ((alg t).1 Θ Γ Δ F = Some (T, c) → syn W N Θ Γ Δ F t T c) ∧
      ((alg t).2 Θ Γ Δ F T = Some c → chk W N Θ Γ Δ F t T c)
    alg_complete : the converse of both, for every derivation
    syn_dec : {Tc | syn … t Tc.1 Tc.2} + {∀ T c, ¬ syn … t T c}
    chk_dec : {c | chk … t T c} + {∀ c, ¬ chk … t T c}
    syn_det, chk_det : at most one result

The fragment of completeness is the contractive contexts, `tenv_contr Θ` and
`lenv_contr Δ`. P-Term types its thread over contractive interface ends and no
variables, so every program and every thread of a configuration is in it. Every
theorem holds for each N, so for the deadlock-free instance (N = ∞) and for the
lock-free one.

### Design

- Annotated terms. The term formers of `expr`, plus `new[C, S, m1, m2]` (E-New),
  `new[x·κ, S, m1, m2]` (E-New-Field), `force[xs, ss] t` (E-Force), `(t : T ! c)`
  (E-Sub), `pack[xs] t : ∃^l ῑ. C. T` (E-Pack) and `open i : U in t` (E-Open).
  Inside `open` the annotations use the de Bruijn points of the premise of
  E-Open, so the opened points have names (finding 6.2). This is the `unpack`
  alternative of 6.2. The other alternative, point expressions `pt(a)`, would
  need a resolution function from variables to points and keeps E-Open
  placement open, which 6.3 shows is not determined.
- Modes. A λ, an injection, a case and a box are checked only. A let checks
  or synthesizes its body in the mode of the conclusion. Every other form
  synthesizes, and checks by synthesis followed by `tsub` (`c_sub`, guarded
  by `by_sub` so that the judgment stays syntax-directed). The first premise
  of let-unit is checked against ∗.
- Splits. `tpart` gives the first premise the ends of the erased first
  subterm. `lpart` gives it the linear variables that the first subterm
  mentions, and both premises the unlimited ones. Completeness absorbs the
  difference to the declarative split by quantifying over weakenings Δ' of Δ
  (`lpart_wk`, uses `typed_tfacts`).
- Box bodies. Checked once, at the session variables `box_inst M k` with
  `M = box_base k U Δ`, above every free session variable of the box context.
  The rule asks `lenv_contr Δ` and `tcontr U`. `box_body_all` turns the one
  instance into all through `typed_sinst`. The identity instance is wrong when
  the context has free session variables, because `slist` shifts the outer
  variables.
- Numbers. Credits, tickets, costs and N are literals of the annotations or
  computed from them. Checking returns the cost of the term, and Chk-Lam,
  Chk-Box and the ascription ask it at most the annotated cost. Every oracle
  call is on ground types (6.6).

Alternatives not taken, each a refinement that keeps the theorems above as the
reference.

- Subsumption only at the switch, E-Pack folded into it, and E-Open placed by
  the rule of plan section 3.6. Completeness then needs `tsub_trans`,
  type-keeping generation lemmas and permutation lemmas for E-Open, and fails
  for existentials whose lower bound is not below their body (6.3).
- Unknown credits, tickets and N with linear constraints (phase 2 of 3.1).
  This removes the numbers from the annotations. It needs a symbolic version
  of `syn` over number variables and a solver interface. Not in Rocq.
- Inference of the constraint of `new` from the goals of its scope (3.4).

### Oracles

One class per oracle, each a decision procedure taken as an instance
argument. `SltOracle` (entailment `slt`), `HoldOracle` (`hold_at`),
`ConsOracle` (`cons_open`), `NewOracle` (`new_ok`), `BcsOracle` (equality of
constraints), `SequivOracle` (`sequiv`), `SsubOracle` (`ssub`). From them
Oracles.v derives equality of types and session types, `ub_below_s`,
`ub_below_u`, `lbx_below_h`, `below_ty`, `ex_wf`, `pscoped`, `sinsts`, `teq`
and `tsub` (`tsub_dec`, by recursion on one side, both orientations at once
because arrows are contravariant). Decide.v adds aging (`tage_f`, `thage_f`,
`lage_f`, each proved equivalent to the relation), `lenv_unl`, `lenv_only`
and `lenv_contr`.

### Decidability

Proved. `alg` is a Rocq function, and `alg_sound` with `alg_complete` show that
it returns exactly what the judgments derive. So `syn` and `chk` are decidable
relative to the seven oracles and deterministic. For finite constraints the
first four oracles and `BcsOracle` reduce to searches over the facts
(section 4 below), which are not mechanized. Session equivalence and
subtyping stay oracles as decided.

### Proposed declarative changes

None needed. Completeness holds for the full judgment over contractive
contexts, without changing a rule. The static premise on existential types of
6.3 is no longer needed, because E-Open placement is an annotation.

### Not done

- Phase 2, inference of numbers.
- Process typing. P-Term and P-Connect are already syntax-directed up to the
  worlds, the cut and the restricted channels (6.10). No algorithmic process
  judgment is in Rocq.
- Decision procedures for the oracles on finite constraints (section 4).

## 2026-11-26. Section 6 against main at 39b7f18b

Branch algorithmic. Each finding of section 6 read again against
theories/static (Typing.v, Contexts.v, Inversion.v, Constants.v, Sinst.v) and
types (Points.v, Worlds.v, Types.v, Costs.v).

- 6.1 fixed. `sinsts` asks `contractive` and `sscoped` of every instance, and
  `typed_sinst` (static/Sinst.v) instantiates a derivation over contractive
  contexts at any instance with `sinst_ok`. So a box body checked at one
  instance types at all of them when the box context is contractive. The
  instance to check at maps the k box variables to fresh variables above
  every free session variable of the box context, the instance that the E-Box
  case of `typed_sinst` itself uses. The identity instance is wrong when the
  context has free session variables, because `slist` shifts the outer
  variables down by k.
- 6.2 holds. E-Open binds de Bruijn point variables that no term names. The
  algorithmic layer makes the opening a node of the annotated term,
  `open x : U in a`, and annotations inside a use the shifted de Bruijn
  points, the opened ones at 0 to m − 1. This is the `unpack` fix of 6.2. The
  node also fixes where E-Open applies.
- 6.3 changed. Plain `new` has two rules now. E-New creates at a fresh base
  with a constraint C under `new_ok` and returns `∃^⊥ ρ. C. (S@ρ)^{m1} ⊗
  (S̄@ρ̄)^{m2}`. E-New-Field creates at `x·κ` for any point x and any field κ,
  with no constraint. Neither the constraint nor the position is in the term.
  The annotated term carries them, `new[C, S, m1, m2]` and
  `new[x·κ, S, m1, m2]`. The static premise on existential types landed as
  `ex_wf`, a premise of E-Pack, and Sub-Ex gained `lb_lower`. Types in
  contexts are still not asked well formed, so a λ may bind an existential
  whose lower bound is not below its body, and the η-law for existentials
  still fails for such an entry. With E-Open placement annotated, this no
  longer blocks completeness.
- 6.4 holds. `cs_P`, `fmx_P` and `rg_P` are still infinite. It concerns the
  oracles, which are parameters here.
- 6.5 holds as written. The algorithm splits by occurrence. A linear entry
  goes to the side whose erased term mentions it. An unlimited entry, which is
  a box, goes to both sides. A box has no heads, no ⊥ flag and ages to itself,
  so this split is complete by weakening.
- 6.6 holds. `eqT` compares credits, tickets and costs on the nose. In the
  algorithm every number is a literal of an annotation or computed from one,
  so every call of the equivalence oracle is on ground types.
- 6.7 fixed. Sub-Ex asks the target constraint entailed under the source
  (`hold_at` under `hc_open`) and lets the lower bound fall by `lb_lower`.
- 6.8 holds. The algorithm takes `force[xs, ss]`.
- 6.9 holds. A λ is checked against its arrow.
- 6.10 holds. P-Term asks `∃ S x m m'` for each restricted channel. The
  algorithm stops at terms.
- 6.11 holds, and `new_ok` adds one more such premise. At finite N it asks a
  partner relation `∃ Sr, gen_new_rel W Γ C Sr`.
- 6.12 fixed. Creation takes any tickets with `tsum_ok N m1 m2`.
- 6.13. `typed_sinst` exists. `tsub_trans` and type-keeping generation lemmas
  are still missing. The algorithm below needs neither, because E-Sub is an
  annotation node and the switch from checking to synthesis is the only other
  place where subtyping enters.

2026-11-21, branch redesign. A plan, not the system. No Rocq change. It reads
the declarative judgment of redesign-clean3 at 933ca2e
(.claude/worktrees/redesign-s4, v2/static/Typing.v, Contexts.v, Inversion.v,
types/Types.v, Costs.v, Points.v, Worlds.v) and the decided changes that have
not landed (layers and plain `new`, from check-layers.md, check-layers-open.md,
the map's typing section and pending.md). The decisions of the author of
2026-11-21 fix the frame. The system is bidirectional, sound and complete for
the declarative one, and decidable relative to the constraint theory.
Equivalence of session types is an oracle. Constraints are finite.

Section 6 is the part to read first. It lists what the algorithmic view
exposes in the declarative rules.

## Summary

- The algorithm runs in two phases. The first is syntax-directed over an
  annotated term and checks types, points and futures. It leaves every credit,
  cost, ticket and N as an integer unknown and emits linear constraints over
  ℕ ∪ {∞}. The second solves them. Points and numbers do not interact, because
  no premise about points reads a number and no numeric premise reads a point
  (`idle` reads only the session type).
- Context splitting needs no input/output contexts. A linear entry occurs in
  exactly one subterm (`typed_tfacts`, cost/Exact.v), so the split is the free
  variables and free ends of each subterm, computed before typing it. This is
  what makes the future `F ◁ Δ2` of the first subterm an input.
- E-Sub and E-Pack move to the switch from checking to synthesis. E-Open
  moves to binders for existentials at ⊥ or with a lower bound below their
  heads, and to the eliminating construct for the others. E-Weak and E-Contract stay admissible. P-Connect is replaced by
  one well-foundedness check of the union of the thread worlds.
- Every oracle except session equivalence has a decision procedure for finite
  C, by reachability or cycle detection over the finitely many facts.
- Thirteen findings in section 6. The three with the most consequence are a
  missing premise in `sinsts` that makes E-Box reject every box that sends or
  receives an end of polymorphic session type (6.1), the absence of names for
  the points E-Open introduces, which leaves several choices that no
  annotation can fix (6.2), and the finite fragment excluding ClientServer,
  LFController, FreshMany and GrowRing with their lock-free versions (6.4).

## 0. The judgment read here

    Θ ; Γ ; Δ ⊢^F_{W,N} e : T ▷ c                         typed W N Θ Γ Δ F e T c
    Σ ⊢^N_W p : T                                         ptyped N W Σ p T

Landed on redesign-clean3. Tickets as one number per end, `TSess S x a m`,
E-Link with `lgt N a1 m2` and `lgt N a2 m1`. E-Open with `cons_open W Γ m C`.
Generalized arrows `TLolli ub lb c T U a`. No future variables. Creation
tickets are fixed for now (N/2 and N − N/2 at `new_ℓ`, m and N − m at
`new_κ o`, N/2 at interface ends).

Planned and read from the design documents. Layers replace families. E-New
becomes plain `new` with a position `(ῑ, π) ∈ {(ρ, ρ), (∅, x·κ)}`, a
constraint C, tickets `m1 + m2 ≤ N`, the premise (wf-new) at a fresh root and
`Γ ⊢ C` at a field. P-Term asks `wf W`, P-Connect asks
`wf (W1|S ⊔ W2|S)` and loses `w_fams W1 ## w_fams W2`. Static worlds are
`(A, facts)`. Transfinite step indices are semantic only and change nothing
here.

The decidable fragment. Every constraint (world facts, box constraints,
existential constraints, E-New constraints) is a finite list of facts. A
`bcs` with `bc_facts : fact → Prop` is read through a finite list
`fbcs = (env, list fact)` with the obvious coercion.

## 1. The rules that are not syntax-directed

| rule | why it is not syntax-directed | how it folds in |
|---|---|---|
| E-Sub | applies to every term | at the switch from checking to synthesis, `chk e T` is `syn e T0` and `T0 ≤p T` (below). Elsewhere synthesis returns the least type (largest credits, least cost), which is principal because every premise that reads a credit asks it large and every premise that reads a cost asks it small (aging, E-App `c2 ≤ a1`, E-Spawn `1 ≤ a`, E-Link, E-Send's payload). |
| E-Pack | applies to every term | folded into `≤p`, the closure of `tsub` under packing. `T0 ≤p ∃^l ῑ. C. T` holds when `T0 ≤p T[xs]`, `Γ ⊢ C[xs]` and `l ≼ ap(T[xs])` for a witness xs found by matching (3.4). Synthesis never packs, because a transparent type is never worse to hold than a packed one (`ap` of a pack is ⊥, ∅ or `{z}` with `z ≼ ap(T[xs])`). |
| E-Open | applies to any existential entry of Δ at any node | an entry at lower bound ⊥, or with `l ≼ ap(T[ῑ])` under `Γ, C(ῑ)`, opens at its binder. Any other existential entry opens at the smallest enclosing node whose type is free of the new points and that contains the construct eliminating the entry. Section 3.6 and finding 6.3 give the argument and its limit. |
| E-Weak, E-Contract | lemmas, not rules (`e_weak`, `e_contract`, static/Weakening.v) | nothing to fold. The leaves E-Unit, E-Var, E-Chan and E-New ask `lenv_unl` of the rest, and unlimited entries go to both sides of every split. |
| context splitting (`tsplit`, `lenv_split` in E-App, E-Pair, E-LetU, E-LetP, E-Case) | the split is a choice, and the future of the first premise reads the second half | the split is fixed by occurrences. `Θ1` is the set of ends of `e1`, the linear entries of `Δ1` are the free variables of `e1`, unlimited entries go to both. `typed_tfacts` shows that every derivation splits this way. The future `F ◁ (Θ2, Δ2)` is then computed from types already known. |
| P-Connect | the binary tree over threads, the cut ΣC and the two worlds are choices | the worlds are outputs (the least world each thread needs, 3.4). Under layers `wf_join_iff` turns the premises of all P-Connect nodes of any tree into `wf (W1 ⊔ … ⊔ Wn)` together with `wf Wi` for each thread, so the tree shape does not matter and one cycle check suffices. The cut of a node is the set of channels with one end on each side. |

Three more premises are choices inside syntax-directed rules.

- E-Box ranges over every session instance `ss`. The algorithm checks the body
  once at the identity instance (finding 6.1).
- E-Force picks a point instance xs and a session instance ss (3.4).
- Plain E-New picks the position, C, S and the tickets (3.4).

## 2. Modes

Two judgments, both with inputs W, Γ, Θ (exactly the ends of e), Δ, F.

    Θ ; Γ ; Δ ⊢^F e ⇒ T ▷ c | K        synthesis, outputs T, c, K
    Θ ; Γ ; Δ ⊢^F e ⇐ T ▷ c | K        checking, input T, outputs c, K

K is a set of integer constraints. Types carry integer unknowns in every
credit, cost and ticket position. Annotations give the shape of a type with
points and session types. Numbers in annotations are optional and default to
fresh unknowns, except inside session types, where they are literals (finding
6.6).

| former | mode | premises in order | annotation needed |
|---|---|---|---|
| `∗` | ⇒ `∗`, cost 0 | `lenv_unl Δ` | none |
| `x` | ⇒ `Δ(x)`, cost 0 | the rest unlimited | none |
| `o` | ⇒ `Θ(o)`, cost 0 | `lenv_unl Δ` | none |
| `λ e` | ⇐ `(T ⊸^u_l[c] U)^a`, or ⇒ with `λ(x : T)^u. e` | `l ≼ ap(Θ, Δ)`, then body ⇒ or ⇐ U under `(Θ, Δ) − a` at `F_u` | argument type and upper point u when synthesized. Lower point l when the captured heads have no greatest common lower bound (6.9). Credit a is an unknown. |
| `spawn (λ e)` | ⇒ `∗` | body ⇐ `∗` under `(Θ, Δ) − 1` at the empty future | none. (⊤, ⊥, 1) is the best instance (`e_spawn_lam`) |
| `e1 e2` | ⇒ U | `e1 ⇒ (T ⊸^u_l[c] U)^{a1}` at `F ◁ (Θ2, Δ2)`, `u ≺ F`, `e2 ⇐ T` at `F ◁ l`, under `(Θ2, Δ2) − c1`, `c2 ≤ a1` | none, except a forced box in head position (3.4) |
| `⟨e1, e2⟩` | ⇒ `(T1 − c2) ⊗ T2`, or ⇐ `V1 ⊗ V2` | `e1` at `F ◁ (Θ2, Δ2)`, `e2` at `F ◁ T1` under `(Θ2, Δ2) − c1`. Checking pushes `V2` into `e2` and checks `e1 ⇐ V1 + c2` with c2 an unknown | none |
| `let ∗ = e1 in e2`, `let ⟨a, b⟩ = e1 in e2` | conclusion's mode | `e1 ⇒` at `F ◁ (Θ2, Δ2)`, body in the conclusion's mode | none |
| `let x = e1 in e2` | conclusion's mode | as E-Let, then E-Open on x when its type is an existential (3.6) | `let x : T = e1` when the binder needs a weaker constraint than `e1` synthesizes (6.2) |
| `inj_i e` | ⇐ `T1 ⊕ T2` | `e ⇐ T_i` | the sum when synthesized |
| `case e (e1) (e2)` | ⇐ T, or ⇒ the join of both branches | `e ⇒ T1 ⊕ T2` at `F ◁ (Θ2, Δ2)`, branches under `T_i, (Θ2, Δ2) − c0` | none in checking position. In synthesis the join exists when both branch types have the same shape and points (credits min, costs max, existential facts intersected, argument types met) |
| `box e` | ⇐ B | `lenv_unl Δ`, Θ = ∅, body ⇐ `U` at the identity instance under `Γ, C(ῑ)`, `Δ, f : B`, future `(∅, ↑u)` | the full box type B, with named point binders ῑ and session binders ᾱ |
| `force e` | ⇒ `U[ss][xs]` | `e ⇒ □(∀ῑ ᾱ. C. ∗ ⊸^u[c] U)`, `Γ ⊢ C[xs]`, `u[xs] ≺ F` | ss whenever k > 0 (6.8). xs is matched (3.4) or given |
| `send e` | ⇒ `(S@x⁺)^m_m` | `e ⇒ Tp ⊗ (S0@x)^a_m`, `unfold S0 = !(ῑ.T).S`, `pscoped`, `x ≺ ap(T[x·i])`, `x ≺ F`, `Tp − 1 ≤ T[x·i]` | none |
| `recv e`, `close e`, `select_i e`, `branch e` | ⇒ as in the rule | `e ⇒ (S0@x)^a_m`, unfold, `x ≺ F` | none |
| `link e` | ⇒ `∗` | `e ⇒ (S1@x)^{a1}_{m1} ⊗ (S2@x̄)^{a2}_{m2}`, `S2 ≈ S̄1`, `a1 + m2 > N`, `a2 + m1 > N` | none |
| `spawn e` | ⇒ `∗` | `e ⇒ (∗ ⊸^u_l ∗)^a`, `1 ≤ a` | none |
| `new` | ⇐ `∃^⊥ ῑ. C. (S@π)^{m1} ⊗ (S̄@π̄)^{m2}`, or ⇒ with `new[S]` | position, C and tickets read off the checked type, or chosen (3.4) | S when synthesized. A field position needs a name for x·κ (6.3) |
| `(e : T)` | ⇒ T | `e ⇐ T` | it is the annotation |

Process typing. `Σ ⊢^N p ⇒ W` takes the interface Σ, synthesizes the least
world, and is defined for processes with no restricted channel inside a single
thread (`C0 = ∅` at every P-Term) unless the restriction carries its session
type and point (6.10).

## 3. Inference

### 3.1 Two phases

Phase 1 walks the annotated term once and produces a typing with unknowns and
the constraint set K. It decides every point premise on the spot with the
entailment oracle, because no point premise depends on a number. Phase 2 asks
whether K has a solution over ℕ ∪ {∞}. Deadlock-freedom typing is phase 1
alone with every number at ∞ (`dftyped`, the instance N = ∞).

### 3.2 Costs

Costs are synthesized like effects, by the formulas of the rules (`fadd`,
`fmax`), and are least. Checking a cost bound `c ≤ c'` is a constraint. The
cost of a closure is the cost of its body, and the cost of a box is an unknown
c with the body's cost at most c. A box that forces its self has a body cost
of at least `c + 1`, so its only solution is ∞, which the solver must accept
(`fle` has `∞ ≤ ∞`).

### 3.3 Credits, tickets and N

Phase 1 creates one credit unknown per end position and per closure in every
type it builds, one cost unknown per arrow and box, the tickets `m1, m2` of
each `new`, and N for the whole program. The credit `a` that E-Abs gives a
closure is a genuine choice (6.9).

Constraints, all linear over ℕ ∪ {∞} with truncated subtraction, max and
halving.

| source | constraint |
|---|---|
| aging `T − c` (E-App, E-Pair, E-LetU, E-LetP, E-Case, E-Abs capture) | `c ≤ a` for every end that is not idle and every closure in T. An idle end gets `max(a − c, 0)`. `idle` is decided from S |
| E-App | `c2 ≤ a1` |
| E-Spawn | `1 ≤ a` |
| E-Link | `a1 + m2 ≥ N + 1`, `a2 + m1 ≥ N + 1` |
| E-Send | each credit of `Tp − 1` at least the literal of the payload type |
| E-Sub at a switch | `a' ≤ a` per credit, `c ≤ c'` per cost, tickets equal |
| E-New (planned) | `m1 + m2 ≤ N`, both ends at credit = tickets |
| P-Term | interface ends at `N/2`, restricted channels `m + m' ≤ N` |
| lock freedom | `N ≠ ∞` |

The theory is existential Presburger arithmetic once ∞ is a case split per
unknown, so phase 2 is decidable. Tickets never change under subtyping
(`sub_sess` keeps `mt`), so tickets are equalities along the flow of an end and
reduce to one unknown per channel end created.

### 3.4 Points

Points are first-order terms. A point is a root (constant, variable,
generated root) with a path of fields and offsets, a polarity and an offset. Matching a pattern with
variables ῑ against a point is decidable by `pt_inst` read backwards. A
variable at offset k and polarity p against `q` gives `σ ι = polar p (q − k)`
when `off q ≥ k`, uniquely. A variable under a field (`ι·κ`) fixes the name and
offset of `σ ι` and leaves its polarity open, because `pt_field` forgets
polarity. So a match has at most `2^{|ῑ|}` solutions, and each is checked
against the constraint.

- E-Pack witness. Matching the synthesized `T0` against `T[ῑ]`. A variable
  that occurs in T only inside C or the lower bound gets no value from the
  match and needs `pack[xs]`.
- E-Force instance. xs by matching the expected type in checking position.
  In head position of an application, `(force e) e2`, the argument is
  synthesized first and matched against the argument type of U, which is
  local inference over the spine. Variables left open after both need
  `force[xs]`. Session instances ss need annotation when k > 0 (6.8).
- E-New, checked against an existential, reads S, the position, C and the
  ticket shape off the type (position ρ when the existential binds one
  variable, x·κ when it binds none). Synthesized, `new[S]` gives S, the
  position defaults to a fresh root, and C has two modes.
  - Annotated. `new[S | C]`.
  - Collected. C is the set of entailment goals that phase 1 meets about
    points of the new tree and cannot discharge, each goal assigned to the
    innermost opened tree it mentions. This C is least: any C' that works
    entails every goal, and (wf-new) holds for C when it holds for C', because
    a goal `u ≺ y` down to the context needs a downward fact in C' and a cycle
    of goals is a cycle of C' ∪ po. Facts that a Sub-Ex comparison asks of the
    type join C. (wf-new) is checked when the scope of the binder closes.
- Worlds. A thread's world is the set of goals between constant-rooted points
  that phase 1 cannot discharge, including the bridges of `cons_open` (4.2).
  Every premise reads W positively, so this world is least, and `wf` holds of
  every world that works only if it holds of the least one.

### 3.5 Futures F ◁ H and ap

The future is an inherited input everywhere. `F ◁ H = F ∪ ap(H)` with ⊥ when H
holds an unopened existential at ⊥ (`sf_unionb`). H is known when the rule
needs it, because the split is fixed by occurrences and the subterms are typed
left to right. E-App reads the lower point of the closure that `e1`
synthesized, E-Pair reads `ap(T1)` of the first component, both before typing
`e2`. `ap` reads no number, so unknown credits do not block it. Readiness
premises (`ub_below_s`, `ub_below_u`, `lbx_below_h`, `rest_below`) become
entailment queries `x ≺ y` and `x ≼ u` over the finite F. E-App at ⊤ asks
`F = (∅, ·)`, a syntactic test.

### 3.6 E-Open

- Every existential entry at ⊥ whose body is not unlimited opens at its
  binder, if `cons_open` holds there. If it fails there, it fails at every
  later node of the same box body (invariance, 4.2), so the entry is never
  opened.
- An entry with `l ≼ ap(T[ῑ])` under `Γ, C(ῑ)` (one entailment query per
  head) also opens at its binder, because the opened entry is then easier to
  hold and repacks.
- Any other existential entry opens at the smallest node that contains the
  construct eliminating it and whose type is free of the new points.
- A result type that mentions opened points must be checked against an
  existential (the avoidance problem). Synthesis fails there and asks for an
  annotation.
- Checking a variable of type `∃ C1. T` against `∃ C2. T` first tries Sub-Ex
  (`C2 ⊆ C1`), then opening and repacking with the fresh points as witness
  (6.7).

## 4. The constraint interface

Six oracles. Five have decision procedures for finite constraints, the sixth
is postulated.

### 4.1 Entailment `Γ ⊢ x ≺ y`

`slt W Γ` is the transitive closure of the facts of W, the instantiated
hypotheses of Γ (each `bcs_at C xs` for `(C, xs) ∈ Γ`) and program order. Let
G be the finite set of these facts. Program order alone relates two points
exactly when they have the same name and the second has the larger offset,
either polarity (`x ≺ x⁺`, `x ≺ x‾⁺`). Write `p ⊑ q` for `p = q` or that
relation.

    Γ ⊢ x ≺ y   iff   x ⊑ y with x ≠ y,
                 or   there are facts (a1, b1), …, (ak, bk) ∈ G, k ≥ 1, with
                      x ⊑ a1, b_i ⊑ a_{i+1}, bk ⊑ y

Every edge is strict, so every nonempty path is. A search over G decides it in
time quadratic in |G| per query, or after one closure of G for all queries.
The Rocq lemma is `slt_path`, the characterization above, from `fl` by
induction and a lemma on program order (`po_iff : po x y ↔ name x = name y ∧
off x < off y`).

### 4.2 `cons_open W Γ m C`

The premise quantifies over all pairs of outer points. For finite C it
reduces to finitely many queries. Call a point new when its root is one of the
m opened variables and outer otherwise. A path between outer points in
`hc_open m C Γ` can enter the new trees only through a fact of C, because
program order keeps the name, world facts sit at constant roots
(`facts_const`) and the shifted hypotheses of Γ mention no new variable.
A bridge of C is a pair `(z, y)` of outer points with

    z ≺ u ∈ C,   u ≼ u' in (C restricted to new points) ∪ po,   u' ≺ y ∈ C,

or a fact `z ≺ y ∈ C` between two outer points (an environment fact).

    cons_open W Γ m C   iff   Γ ⊢ z ≺ y for every bridge (z, y)

Any path in the opened context between outer points is a path of Γ with some
segments replaced by bridges, which gives the direction from right to left.
Each bridge is itself such a path, which gives the other. The number of
bridges is at most `|C|²`. The Rocq lemma is `cons_bridges`.

Two consequences matter for the algorithm. Bridges depend on C alone, so
`cons_open` is monotone in W and Γ. A later E-Open adds no fact between points
that existed before it (`opened_cons`), and an existential entry never enters
a box body (box contexts are unlimited), so `cons_open` of an entry has the
same value at every node between its binder and the end of the enclosing box
body. Lemma `cons_stable`.

### 4.3 (wf-new) at a fresh root

    every fact of C has a point in tree(ρ)
    every fact between tree(ρ) and a context point goes from the context point
    C ∪ po is well-founded on tree(ρ)

The first two are syntactic tests on the finite list. For the third, a
descending chain in C ∪ po uses facts infinitely often, because program order
alone descends finitely (offsets fall). With finitely many facts one fact
repeats, so the chain contains a cycle. Conversely a cycle gives an infinite
chain. So for finite C, well-founded is acyclic, decided by a cycle search in
the graph whose nodes are the facts of C inside tree(ρ), with an edge from
`(a, b)` to `(a', b')` when `b ⊑ a'`. A fact from the context into the tree
cannot lie on a cycle inside the tree, because leaving the tree needs a
downward fact. The constructive direction for Rocq gives the rank. `μ(p)`, the
largest number of facts on a path ending at p, is finite on an acyclic finite
graph, and `(μ, off)` decreases lexicographically along every step. It reads
as the ordinal `ω·μ + off`, the shape the layers write-up uses. Lemma
`wf_fin_acyclic`.

At a field, the premise `Γ ⊢ C` is one entailment query per fact.

### 4.4 `wf W` at P-Term and `wf (W1|S ⊔ W2|S)` at P-Connect

`wf W` for a finite static world is the cycle search of 4.3 on the facts of W.
At P-Connect both sides sit over well-founded worlds by induction, so by
`wf_join_iff` (check-layers-open.md, section 2, not yet in Rocq) the premise is
equivalent to `wf (W1 ⊔ W2)`, which is the cycle search on the union of the two
fact lists. Computing `W|S` is not needed. For a whole process the algorithm
runs one search on the union of all thread worlds.

### 4.5 Session equivalence `S ≈ S'`

Postulated, as decided. Three remarks fix its interface.

- It is called on session types whose numbers are literals (6.6).
- Almeida, Mordido and Vasconcelos decide bisimilarity of context-free
  session types whose messages are basic types, and they list higher-order
  session types as future work (almeida2020deciding, section 6). Our payloads
  are types with ends and arrows, compared by `eqT` with `≈` inside. For
  payloads closed under the enclosing μ, each payload class can be replaced by
  a fresh message label, bottom up. For a payload that mentions an enclosing
  recursion variable (`μα. !(α@ι).S`) I know no reduction, and the oracle is
  then an assumption beyond that paper.
- `hcontractive` (`∀ n, ahc n s`) is not an oracle. It needs a decision lemma,
  a syntactic guardedness test for μ, `hcontractive_dec`.

### 4.6 Integer constraints

Existential Presburger arithmetic over ℕ ∪ {∞}, as in 3.3. The Rocq interface
is a solver `solve : list ncon → option valuation` with soundness and
completeness as section hypotheses, or `Decision` of satisfiability.

## 5. Soundness and completeness, and how to prove them in Rocq

### Statements

Annotated terms `aexpr` with `erase : aexpr → expr`. Shapes `sty_shape`,
`ty_shape` with integer unknowns, and valuations `σ : nat → fuel`.

    Theorem algo_sound W Θ Γ Δ F a T c K σ :
      syn W Θ Γ Δ F a T c K → σ ⊨ K →
      typed W (σ N̂) (σ Θ) Γ (σ Δ) F (erase a) (σ T) (σ c).

    Theorem algo_complete W N Θ Γ Δ F e T c :
      finite W Γ Θ Δ F T →
      typed W N Θ Γ Δ F e T c →
      ∃ a K σ, erase a = e ∧ annotated_at_sites a ∧
        chk W (shape Θ) Γ (shape Δ) F a (shape T) ĉ K ∧ σ ⊨ K ∧
        σ (shape T) = T ∧ σ N̂ = N ∧ fle (σ ĉ) c.

    Theorem algo_dec W Θ Γ Δ F a T :
      finite W Γ Θ Δ F T →
      Decision (∃ c, typed W N Θ Γ Δ F (erase a) T c ∧ respects a)

with `annotated_at_sites` the annotation discipline of section 2 and
`respects a` that the derivation agrees with the annotations of a. Process
level

    Theorem palgo_iff N Σ p T :
      (∃ W, ptyped N W Σ p T) ↔ ∃ W, psyn N Σ p T W ∧ wf W.

and the same for `dftyped` and `ptyped None`. The finiteness hypothesis bounds
the inputs. A derivation of a finite input may still use an infinite C at an
E-New or E-Pack, so completeness needs `finitize`, which cuts every such C to
the facts that some entailment of the derivation uses, plus those a Sub-Ex
comparison with a finite type asks. Each entailment is a finite derivation of
`fl`, so the cut is finite, and bridges and (wf-new) survive the passage to a
subset.

### Proof route

Two layers keep the work separate.

1. A syntax-directed declarative judgment `sdtyped`, the rules of section 2
   with numbers still concrete. Prove `sdtyped ↔ typed` on finite inputs.
   - Soundness. Each rule of `sdtyped` is a declarative rule or a short
     composition with E-Sub, E-Pack and E-Open.
   - Completeness. Normalize a `typed` derivation in four steps, each a lemma
     by induction.
     1. Splits by occurrence, from `typed_tfacts`.
     2. E-Sub and E-Pack pushed to the switch points. This needs `tsub_trans`
        (missing), and generation lemmas that keep the type, `inv_X` with
        `T0 ≤p T` in the conclusion. The lemmas of Inversion.v forget the
        type and give the shape of the `opened` context, which is the right
        start.
     3. E-Open moved to its place. A permutation lemma `open_commute` per
        rule moves an E-Open across a syntax-directed node when the opened
        entry goes to one side, with `cons_stable` for the premise and
        `open_pack` (opening and repacking at the fresh points) for the uses
        at the existential type.
     4. E-Box at the identity instance from the ∀ over instances, which is
        immediate, and its converse `typed_sinst`, which is missing (6.1).
2. The algorithm as a function on `aexpr` that returns `option (T, c, K)`,
   proven sound and complete for `sdtyped` modulo `σ ⊨ K`. This part is
   bookkeeping of unknowns.

Oracles enter as section hypotheses, never as axioms. `sequiv_dec : ∀ s r,
Decision (sequiv s r)` and the solver. Entailment, bridges, (wf-new) and `wf`
are proven decision procedures on `fbcs` and finite worlds.

The lemmas to build, in this order, are `po_iff`, `slt_path`, `slt_dec`, `cons_bridges`,
`cons_stable`, `wf_fin_acyclic`, `wf_new_dec`, `hcontractive_dec`,
`tsub_trans`, the generation lemmas, `open_commute`, `open_pack`,
`typed_sinst`, `finitize`, then `sdtyped` and its two directions.

## 6. Findings

### 6.1 E-Box ranges over instances that E-Send and E-Recv reject

E-Box asks the body at every `ss` with `sinsts N ss`, and `sinsts` asks only
`Forall hcontractive ss` and, at N = ∞, `sty_df s = s`. It does not ask
`sscoped`. E-Send and E-Recv ask `pscoped m T` of the payload, and `pscoped`
of `TSess s x _ _` asks `sscoped s`. Take a box whose body receives on an end
of type `?(∃ι. α@ι).S` with α a box session variable. At the instance
`α := !(∃.(End@ι₇)).Skip`, whose payload mentions a point variable free below
its binder, the payload `T[α := s]` is not `pscoped`, so E-Recv fails and E-Box
fails. Every box that sends or receives an end whose type contains a session
variable of the box is untypable, whatever its body. No example has k > 0
(every `TBox` in v2/examples has k = 0), so nothing shows it today.

For the algorithm this is a soundness gap. Checking the body once at the
identity instance accepts such a box, and the declarative rule does not. The
fix is a premise on the instance, `sinsts N ss` with `Forall sscoped ss`,
which `pinst_sty = id` already presumes (session types carry no free point).
With it, `typed_sinst` (typing at the identity instance gives typing at every
instance) becomes provable by induction. It needs three lemmas. Unfolding commutes
with `sinst` when the head is an action, `sequiv` is closed under `sinst`, and
`dual` commutes with `sinst`. `typed_sinst` does not exist today.

Correction of the fourth run (2026-11-21). `typed_sinst` is false even with
`Forall sscoped` in `sinsts` (`typed_sinst_false`, v2/examples/SinstStuck.v).
`sequiv` compares stuck terms on the nose, and a contractive instance can
turn two equivalent session types with a stuck tail into two distinct stuck
continuations. Checking a box body at the identity instance is sound only for
bodies whose session types are all contractive.

### 6.2 The points E-Open introduces have no name

E-Open binds `ῑ` fresh, and the program has no binder for them. Every
annotation inside the scope that must mention an opened point cannot be
written. The cases are a λ whose upper point is the point of an end obtained
by opening (the usual case after `let x = new in let ⟨a, b⟩ = x in …`), a
`force[xs]` at opened points, a `pack[xs]`, and a field position `x·κ` with x
opened. Points of W and box binders can be named. Opened points cannot,
because decision Q1 keeps points out of programs and E-Open is not syntax.

Two fixes, both erased before the declarative judgment. A binder
`unpack x as ῑ in e` that fixes where E-Open applies and names the points. Or
point expressions relative to variables, `pt(a)` for the point of the end
bound to a, with `pt(a)⁺`, `pt(a)‾`, `pt(a)·κ`. The second covers the examples
I know without changing where E-Open applies.

The binder type of an opened entry is a further choice. `cons_open` grows
harder as C grows, and Sub-Ex lets a derivation drop facts before the binder.
The conservative subsets of a C have no greatest element. Take
`C = {z ≺ ι, ι ≺ w}` with `Γ ⊬ z ≺ w`. Both `{z ≺ ι}` and `{ι ≺ w}` are
conservative, their union is not, and the body may need either. Synthesizing
the strongest type of `e1` and binding it is then incomplete. The algorithm
asks for `let x : T = e1` when `cons_open` fails on the synthesized type.

### 6.3 Plain `new` has a position no term carries

E-New (planned) picks `(ῑ, π) ∈ {(ρ, ρ), (∅, x·κ)}` with x any point of Γ and
κ any field. Today `new_κ o` names the field through an end. Plain `new`
names nothing. The choice is finite. A field whose tree no fact of W or Γ
touches is never better than a fresh root with collected C, so the candidates
are the field names that occur in the facts, plus one fresh root. A search
over them is decidable and exponential in the number of `new` sites. I
recommend keeping `new_κ e` as surface syntax that fixes the field, with
`pt(a)·κ` from 6.2 as the general form.

E-Open placement. Opening and repacking an entry `∃^l ῑ. C. T` asks
`l ≼ ap(T[ῑ])` under `Γ, C(ῑ)` (E-Pack's `lbx_below_h`), and nothing in the
type guarantees it for `l = LPt z` or `l = LNone`. So the η-law for
existentials fails, and where E-Open applies matters. For l = ⊥ opening at the
binder dominates (packing at ⊥ asks nothing, and an unopened ⊥ entry blocks
every action while held because `ub_below_s` asks `fs_bot F = false`). For
other lower bounds the unopened entry contributes `{z}` or nothing to the
future and the opened one contributes `ap(T[ῑ])`, which are incomparable. The
rule of 3.6 is complete for entries at ⊥ and for entries with
`l ≼ ap(T[ῑ])` under C. For the rest neither placement dominates, and
completeness needs a search over the nodes between binder and elimination. A static premise on existential types, `l ≼ ap(T)` under C with
`LNone` asking `ap(T) = ∅`, would make eager opening complete for every lower
bound. It is a well-formedness of types, read at binders and annotations,
with no semantic content.

### 6.4 The finite fragment excludes four example pairs

The box constraint of ClientServer (`cs_P`, examples/ClientServer.v) is
`{ι+k ≺ (κ+k)‾, κ+k ≺ (ι+k+1)‾, ι+k ≺ ζ, κ+k ≺ ζ | k ∈ ℕ}`. The constraints
of LFController (`ctl_P`) and FreshMany (`fmx_P`, `(ι·0)+k ≺ ι₁` for every k)
and the GrowRing constraint `rg_P` (a predicate over the reachable field pairs
`rreach`) are infinite as well, and so are the laws of their worlds. Their
lock-free versions use the same. No finite C works for ClientServer. The
recursive call instantiates the box at `(ι⁺, κ⁺, ζ)`. Let d be the largest
offset at which a fact of C leaves ι. The instance of that fact at `ι⁺` starts
at `ι+d+1`, and no path of `C ∪ po` leaves `ι+d+1`, because program order only
raises offsets and no fact leaves ι above d. The same holds for every
recursive box that recurses at shifted points of two channels with an order
between them, which is the client-server pattern.

Layers make this sharper. A field creation carries no constraint, so every
fact about a field at any depth comes from the creation of its root. A
recursion that creates at fields of fields, as GrowRing does, needs a
constraint at the root for every depth.

So the decided fragment covers Cycle, FreshBetween, FactoryEx and their
lock-free versions, LFClose, and the examples without boxes. It excludes
ClientServer, LFController, FreshMany and GrowRing with their lock-free
versions, among them the two programs that motivated ordinal ranks. An
extension that keeps decidability is facts schematic in one offset variable k,
each side at `k + d` or at a fixed offset, for a fixed integer d. ClientServer,
LFController and FreshMany have this form. A path then carries the offset of
its current point as a counter. A fact `x+k+d1 ≺ y+k+d2` adds `d2 − d1` when
the counter is at least d1, a fact into a fixed offset resets the counter,
and program order adds any positive amount. Entailment is reachability in a
one-counter system, which is decidable. GrowRing's constraint is a regular
set of field paths and stays outside. This contradicts nothing decided. It is
the first question for the full draft.

### 6.5 The future of the first subterm reads the context of the second

E-App, E-Pair, E-LetU, E-LetP and E-Case type `e1` at `F ◁ (Θ2, Δ2)`, the
heads of everything `e1` does not use. Read with input and output contexts,
the output of `e1` is an input of `e1`. The rule is fine only because
linearity determines the split. Two consequences for future changes. A rule
that weakens a linear entry (an idle end, a unit variable) makes the split a
search, because `F ◁ Δ2` then depends on which entries are dropped. And
`unlimited` holds of boxes only, so a variable of type ∗ must be consumed
(`let ∗ = x in …`), which programs feel and the algorithm needs.

Numbers have a second circularity. Checking `⟨e1, e2⟩` against `V1 ⊗ V2`
needs c2 to check `e1 ⇐ V1 + c2`, and `e2` runs under `(Θ2, Δ2) − c1`. Unknown
credits remove it, which is one reason for phase 2.

### 6.6 Session equivalence compares numbers on the nose

`eqT` asks `a = a'`, `mt = mt'` and `c = c'` inside payload types, and `≈`
compares payloads by `eqT`. When payload credits are unknowns, a boolean
oracle cannot answer. It would have to return which payload occurrences
correspond along the bisimulation, so that phase 1 can emit the equalities.
The algorithm avoids it by keeping numbers inside session types literal,
which holds when protocols are declared. Under that restriction every call of
the oracle is on ground types.

### 6.7 Sub-Ex is syntactic, so `let x = e in x` types more than `e`

Sub-Ex asks `facts C' ⊆ facts C` with equal environments and lower bounds. A
change of constraint by entailment needs E-Open and E-Pack, and E-Open opens
only entries of Δ. So `e : ∃ C1. T` does not check against `∃ C2. T` when C2
is entailed by C1 and not a subset, while `let x = e in x` does, provided
`cons_open` holds for C1. The algorithm reproduces this with open and repack
in the variable case of checking (3.6). Subject expansion of `let` fails, and
annotations must list a subset of the synthesized facts. Sub-Box has the same
rigidity for k > 0, where it asks `U = U'` and not `U ≡ U'`.

### 6.8 E-Force's session instance is not found by matching

The result `U[ss][xs]` must meet the expected type up to E-Sub, which compares
sessions by ≈. Where a session variable stands alone (`α@ι`), matching assigns
it. Where it sits in a sequence (`α; S`), matching asks for α with
`α; S ≈ S''`, a division problem for context-free session types that the
equivalence oracle does not answer. The algorithm asks for `force[ss]` when
k > 0. Points xs are found by matching (3.4).

### 6.9 E-Abs has no principal type

- Credit a. A larger a helps every user of the closure (E-App `c2 ≤ a`,
  E-Spawn `1 ≤ a`, aging while held) and leaves less to the body, which sees
  `(Θ, Δ) − a`. An unknown with constraints settles it.
- Upper point u. ⊤ is best for the body (empty future) and worst for the
  caller (E-App asks `F = (∅, ·)`). `·` lets the body act nowhere. A point is a
  trade-off between the body's actions below it and the caller's future above
  it. The algorithm asks for u in synthesis. `spawn (λ e)` is the exception,
  where (⊤, ⊥, 1) is best.
- Lower point l. ⊥ is always allowed, `·` only without heads, a point z when
  z lies below every head. The best z is a greatest common lower bound of the
  heads under Γ, which need not exist. One head, or a head below all others,
  gives it. Otherwise the algorithm asks for l.

### 6.10 P-Term hides the session type and point of restricted channels

P-Term asks `∃ S x m m'` for every restricted channel `c ∈ C0`. The process
syntax `(C0, threads)` carries no type for c, and the thread names `c⁺` and
`c⁻` only through constants. Inferring S is session type inference. The
algorithm types processes with `C0 = ∅` at every P-Term, which covers every
initial program, or needs `ν (c : S @ x)`. Run-time configurations are typed
by the declarative judgment only, which is all subject reduction needs.

### 6.11 Premises that are not decidable as stated

- `cons_open` quantifies over all pairs of points. Decidable by bridges (4.2).
- `wf W`, (wf-new) and the P-Connect premise ask `well_founded`. Decidable by
  cycle search for finite facts (4.3), with a constructive rank.
- `hcontractive` and `sequiv` quantify over every depth n. The first needs
  `hcontractive_dec`, the second is the oracle.
- E-Box quantifies over all instances (6.1).
- Every `bcs` is a predicate `fact → Prop`, so `hold_at`, Sub-Ex inclusion and
  the open hypotheses are undecidable for general C. The fragment reads them
  through `fbcs`.

### 6.12 The landed creation tickets leave E-Link almost unusable

On redesign-clean3 a channel at a fresh root starts at `⌊N/2⌋` and
`N − ⌊N/2⌋` tickets, a field creation at `m` and `N − m` for the tickets m of
the anchor end, and interface ends at `⌊N/2⌋`. In a program typed from P-Term
with `C0 = ∅` every end therefore holds `⌊N/2⌋` or `⌈N/2⌉` tickets, because
sending keeps tickets (`sub_sess` keeps `mt`) and payload literals must match
the sender's end. E-Link asks `a1 + m2 > N` and `a2 + m1 > N` with `a ≤ m`. For
even N no link types. For odd N a link types only when both linked ends hold
`⌈N/2⌉` tickets at full credit. No lock-free example links, so nothing
failed. The report of the run states that the fixed split waits for the
existential property. For the algorithm the free split `m1 + m2 ≤ N` of the
map is the form to target, with the tickets as unknowns.

### 6.13 Missing lemmas the algorithm needs

`tsub_trans` (only `tsub_refl` exists), generation lemmas that keep the type
(Inversion.v forgets it), `typed_sinst`, `hcontractive_dec`, `wf_join_iff`
(open from check-layers-open.md on), and the decision lemmas of section 4.

## 7. When the Rocq run lands

| change | effect on the plan |
|---|---|
| tickets, `TSess S x a m` (landed) | none. Tickets are unknowns with equalities along each end. The fixed creation split goes when plain `new` gets free tickets (6.12) |
| E-Open with `cons_open` (landed) | `cons_bridges` and `cons_stable` build on `opened_cons` and `facts_const`, both in Rocq |
| transfinite step indices | none. They are semantic. The statements of section 5 do not mention indices |
| layers | `ENew ℓ` and families go, `w_fams` disjointness and `wfrename` leave P-Connect, `strict` becomes `wf`, `ptyped_strict` becomes `ptyped_wf`. The world becomes `(consts, facts)`, a finite list in the fragment. The oracles keep their procedures, because for finite facts strict and well-founded coincide |
| plain `new` (entry 2) | E-New takes the position, C and tickets as choices (3.4, 6.3). `e_new_at` becomes the field case, kept as surface syntax |
| ordinal credits and tickets, if they come | numbers become ordinals below ω² written `ω·a + b`, with the natural sum in E-Link. The theory stays Presburger over pairs. Aging is undefined at a limit credit, which adds a side condition per aging |

Decisions the full draft needs from the author.

1. `Forall sscoped` in `sinsts` (6.1).
2. Names for opened points, `unpack` or `pt(a)` (6.2).
3. Whether existential types are well formed, `l ≼ ap(T)` under C (6.3).
4. Whether the fragment admits offset-uniform facts (6.4).
5. `new_κ e` as surface syntax for field creations (6.3).
6. Literal numbers inside session types (6.6).

## What was checked

On paper, against the files named at the top. The rules, contexts, aging,
subtyping, `sinsts`, `pscoped`, `cons_open`, `pt_inst`, `pt_field`, the
creation tickets and the example constraints were read in the Rocq of
redesign-clean3. The reduction of entailment, bridges and well-foundedness to
finite searches, the principality claims of 3.2 to 3.4, the invariance of
`cons_open`, the counterexample to a greatest conservative subset, the
failure of finite C for ClientServer, the one-counter reduction of 6.4 and the
link arithmetic of 6.12 are arguments here, not proofs. Nothing was compiled.
Finding 6.1 rests on reading `sinsts`, `pscoped` and E-Recv and was not probed
in Rocq. The constraints of the examples were read in v2/examples.

## Literature used

- almeida2020deciding. The decision procedure for bisimilarity of
  context-free session types, with messages of basic type only, and higher-order
  session types listed as future work (section 6).
